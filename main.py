#!/usr/bin/env python3
"""
Discord Favorite GIF Downloader
Async downloader for Discord favorite GIFs from protobuf data
Author: nloginov
"""

import asyncio
import httpx
import base64
import json
import os
import logging
from pathlib import Path
from typing import List, Tuple, Optional, Set, Dict, Any
from dataclasses import dataclass, field
from datetime import datetime
import sys
import re
from urllib.parse import urlparse, unquote, parse_qs, urlunparse
import mimetypes
import html
import time
import random

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger(__name__)

# Suppress httpx debug logs
logging.getLogger('httpx').setLevel(logging.WARNING)
logging.getLogger('httpcore').setLevel(logging.WARNING)

# Media type mappings
MEDIA_TYPES = {
    'image/gif': ('.gif', 'gif'),
    'video/mp4': ('.mp4', 'mp4'),
    'image/png': ('.png', 'img'),
    'image/jpeg': ('.jpg', 'img'),
    'image/jpg': ('.jpg', 'img'),
    'video/webm': ('.webm', 'mp4'),
    'image/webp': ('.webp', 'img'),
    'video/quicktime': ('.mov', 'mp4'),
}

DISCORD_TOKEN = ""

# Rate limiting configuration
RATE_LIMIT_DELAY = 0.1
MAX_REQUESTS_PER_DOMAIN = 10
REQUEST_TIMEOUT = 30

# Domain-specific delays
DOMAIN_DELAYS = {
    'tenor.com': 0.2,
    'imgur.com': 0.2,
    'giphy.com': 0.2,
    'discordapp.com': 0.15,
    'discordapp.net': 0.15,
    'media.discordapp.net': 0.15,
    'cdn.discordapp.com': 0.15,
}


@dataclass
class DownloadStats:
    """Track download statistics"""
    total: int = 0
    successful: int = 0
    failed: int = 0
    skipped: int = 0
    resolved: int = 0
    unsupported: int = 0
    rate_limited: int = 0
    not_found: int = 0  # 404 errors
    errors: List[str] = field(default_factory=list)
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    downloaded_files: List[str] = field(default_factory=list)
    failed_urls: Dict[str, str] = field(default_factory=dict)

    @property
    def success_rate(self) -> float:
        return (self.successful / self.total * 100) if self.total > 0 else 0

    @property
    def duration(self) -> float:
        if self.start_time and self.end_time:
            return (self.end_time - self.start_time).total_seconds()
        return 0

    def add_error(self, url: str, error: str):
        # Clean the URL for display
        display_url = url[:80] + "..." if len(url) > 80 else url
        self.errors.append(f"{display_url}: {error}")
        self.failed_urls[url] = error
        
        # Count specific error types
        if "404" in error or "Not Found" in error:
            self.not_found += 1


class RateLimiter:
    """Rate limiter to avoid getting blocked"""
    
    def __init__(self):
        self.domain_timestamps: Dict[str, List[float]] = {}
        self.domain_semaphores: Dict[str, asyncio.Semaphore] = {}
    
    async def wait_for_domain(self, domain: str):
        """Wait before making a request to a domain"""
        now = time.time()
        
        if domain not in self.domain_semaphores:
            self.domain_semaphores[domain] = asyncio.Semaphore(MAX_REQUESTS_PER_DOMAIN)
        
        delay = DOMAIN_DELAYS.get(domain, RATE_LIMIT_DELAY)
        
        # Check last request time
        if domain in self.domain_timestamps:
            timestamps = self.domain_timestamps[domain]
            if timestamps:
                last_time = timestamps[-1]
                time_since = now - last_time
                if time_since < delay:
                    await asyncio.sleep(delay - time_since + random.uniform(0, 0.03))
        
        # Update timestamps
        if domain not in self.domain_timestamps:
            self.domain_timestamps[domain] = []
        self.domain_timestamps[domain].append(time.time())
        
        # Keep only recent timestamps
        self.domain_timestamps[domain] = [t for t in self.domain_timestamps[domain] if now - t < 60]
        
        # Acquire semaphore
        return await self.domain_semaphores[domain].acquire()
    
    def release_domain(self, domain: str):
        """Release semaphore after request"""
        if domain in self.domain_semaphores:
            self.domain_semaphores[domain].release()


class URLResolver:
    """Resolve special URLs to direct media URLs"""

    def __init__(self, rate_limiter: RateLimiter):
        self.rate_limiter = rate_limiter
        self.tenor_cache = {}

    @staticmethod
    def clean_url(url: str) -> str:
        """Clean and normalize URL"""
        if not url:
            return url

        # Decode HTML entities
        url = html.unescape(url)

        # Fix URLs that start with slash
        if url.startswith('/') and not url.startswith('//'):
            url = 'https:' + url

        return url

    @staticmethod
    def is_discord_attachment(url: str) -> bool:
        parsed = urlparse(url)
        return (
            parsed.netloc in ('cdn.discordapp.com', 'media.discordapp.net')
            and '/attachments/' in parsed.path
        )

    @staticmethod
    def extract_domain(url: str) -> str:
        """Extract domain from URL"""
        try:
            parsed = urlparse(url)
            domain = parsed.netloc
            
            # Handle special Discord domains
            if 'images-ext-' in domain:
                return 'discordapp.net'
            elif 'cdn.discordapp.com' in domain:
                return 'cdn.discordapp.com'
            elif 'media.discordapp.net' in domain:
                return 'media.discordapp.net'
            
            # Extract main domain
            domain_parts = domain.split('.')
            if len(domain_parts) >= 2:
                return f"{domain_parts[-2]}.{domain_parts[-1]}"
            return domain
        except:
            return "unknown"
    
    @staticmethod
    def is_valid_url(url: str) -> bool:
        """Check if URL is valid"""
        if not url or len(url) < 10:
            return False
        
        # Must start with http:// or https://
        if not url.startswith(('http://', 'https://')):
            # Check if it's a relative URL that can be fixed
            if url.startswith('//'):
                url = 'https:' + url
                return URLResolver.is_valid_url(url)
            return False
        
        try:
            parsed = urlparse(url)
            return bool(parsed.scheme and parsed.netloc)
        except:
            return False
    
    async def resolve_discord_proxy_url(self, client: httpx.AsyncClient, url: str) -> List[str]:
        """Resolve Discord proxy URLs (images-ext-X.discordapp.net)"""
        try:
            parsed = urlparse(url)
            
            # Check if it's a Discord proxy URL
            if 'images-ext-' not in parsed.netloc:
                return [url]
            
            # Extract the actual URL from the path
            path_parts = parsed.path.split('/')
            
            # Look for 'external' in path
            for i, part in enumerate(path_parts):
                if part == 'external' and i + 1 < len(path_parts):
                    # The next part is the encoded URL
                    encoded_url = '/'.join(path_parts[i+1:])
                    
                    # Remove any trailing query/fragment
                    encoded_url = encoded_url.split('?')[0].split('#')[0]
                    
                    # Try to decode
                    try:
                        # URL might be base64 encoded or just URL encoded
                        decoded = unquote(encoded_url)
                        
                        # Sometimes it's double encoded
                        while '%' in decoded:
                            decoded = unquote(decoded)
                        
                        # Ensure it's a full URL
                        if decoded.startswith('http'):
                            return [decoded]
                        elif decoded.startswith('//'):
                            return ['https:' + decoded]
                        else:
                            # Try to reconstruct
                            return ['https://' + decoded.lstrip('/')]
                    except:
                        pass
            
            # Also check query parameters
            query = parse_qs(parsed.query)
            
            # Check common query param names
            for key in ['url', 'src', 'image', 'media']:
                if key in query:
                    for value in query[key]:
                        if value.startswith('http'):
                            return [value]
                        elif value.startswith('//'):
                            return ['https:' + value]
            
            # If we can't resolve, return original
            return [url]
            
        except Exception as e:
            logger.debug(f"Error resolving Discord proxy URL {url}: {e}")
            return [url]
    
    async def resolve_imgur_url(self, client: httpx.AsyncClient, url: str) -> List[str]:
        """Resolve Imgur URL to direct image URLs"""
        try:
            parsed = urlparse(url)
            if parsed.netloc == 'i.imgur.com':
                return [url]
            
            domain = self.extract_domain(url)
            await self.rate_limiter.wait_for_domain(domain)
            
            try:
                # Extract Imgur ID
                path_parts = parsed.path.strip('/').split('/')
                imgur_id = None
                
                if len(path_parts) >= 2 and path_parts[0] in ['a', 'gallery']:
                    imgur_id = path_parts[1]
                else:
                    imgur_id = path_parts[-1].split('.')[0] if path_parts else None
                
                if not imgur_id:
                    return []
                
                # Try to get direct image first
                direct_extensions = ['.jpg', '.png', '.gif', '.mp4', '.webm']
                for ext in direct_extensions:
                    test_url = f"https://i.imgur.com/{imgur_id}{ext}"
                    # We'll let the downloader check if it exists
                    return [test_url]
                    
            finally:
                self.rate_limiter.release_domain(domain)
            
        except Exception as e:
            logger.debug(f"Error resolving Imgur URL {url}: {e}")
        
        return []
    
    async def resolve_tenor_url(self, client: httpx.AsyncClient, url: str) -> List[str]:
        """Resolve Tenor URL to direct media URL"""

        if url in self.tenor_cache:
            return self.tenor_cache[url]

        try:
            domain = self.extract_domain(url)
            await self.rate_limiter.wait_for_domain(domain)
            
            try:
                resp = await client.get(url, follow_redirects=True)

                if resp.status_code != 200:
                    return []

                html_text = resp.text

                patterns = [
                    r'https://media\.tenor\.com/[^\s\"\']+\.gif',
                    r'https://media\.tenor\.com/[^\s\"\']+\.mp4',
                    r'https://c\.tenor\.com/[^\s\"\']+\.gif',
                    r'https://c\.tenor\.com/[^\s\"\']+\.mp4'
                ]

                found = []

                # Find patterns in HTML code
                for pattern in patterns:
                    matches = re.findall(pattern, html_text)

                    for match in matches:
                        clean = match.split("?")[0]

                        if clean not in found:
                            found.append(clean)
                
                return []
                    
            finally:
                self.rate_limiter.release_domain(domain)
            
        except Exception as e:
            logger.debug(f"Error resolving Tenor URL {url}: {e}")
        
        return []
    
    async def resolve_url(self, client: httpx.AsyncClient, url: str) -> List[str]:
        """Main URL resolver"""
        try:
            # Clean the URL first
            url = self.clean_url(url)
            
            # Validate URL
            if not self.is_valid_url(url):
                logger.debug(f"Invalid URL: {url}")
                return []
            
            parsed = urlparse(url)
            domain = parsed.netloc.lower()
            
            # Route to appropriate resolver
            if 'images-ext-' in domain:
                return await self.resolve_discord_proxy_url(client, url)
            elif self.is_discord_attachment(url):
                return [url]
            elif 'tenor.com' in domain:
                return await self.resolve_tenor_url(client, url)
            elif 'imgur.com' in domain:
                return await self.resolve_imgur_url(client, url)
            else:
                return [url]
                
        except Exception as e:
            logger.debug(f"Error in resolve_url for {url}: {e}")
            return [url] if self.is_valid_url(url) else []


    async def bulk_refresh_discord_urls(self, client: httpx.AsyncClient, urls: List[str]) -> Dict[str, str]:
        """Refresh Discord CDN URLs"""
        if not DISCORD_TOKEN or not urls:
            return {}

        headers = {"Authorization": DISCORD_TOKEN, "Content-Type": "application/json"}
        refreshed: Dict[str, str] = {}

        for i in range(0, len(urls), 50):
            batch = urls[i:i+50]
            try:
                # Fetch new URLs
                # https://docs.discord.food/resources/message#refresh-attachment-urls
                resp = await client.post(
                    "https://discord.com/api/v10/attachments/refresh-urls",
                    headers=headers,
                    json={"attachment_urls": batch},
                    timeout=httpx.Timeout(15.0)
                )
                resp.raise_for_status()
                data = resp.json()

                # Retrieve new URLs
                for item in data.get("refreshed_urls", []):
                    original = item.get("original")
                    fresh = item.get("refreshed")
                    if original and fresh:
                        refreshed[original] = fresh
            except Exception as e:
                logger.debug(f"Bulk refresh failed for batch {i}: {e}")

        return refreshed


class ProtobufParser:
    """Parse Discord protobuf data"""
    
    @staticmethod
    def extract_urls_simple(data: bytes) -> List[str]:
        """Simple but effective URL extraction"""
        urls = set()
        
        # Convert to string for regex
        try:
            text = data.decode('latin-1')
        except:
            text = data.decode('utf-8', errors='ignore')
        
        # Improved URL pattern that catches more cases
        url_patterns = [
            r'https?://[^\s"\'\x00-\x1F<>)\]]+',  # Main pattern
            r'//[^\s"\'\x00-\x1F<>)\]]+',  # Protocol-relative URLs
        ]
        
        for pattern in url_patterns:
            matches = re.findall(pattern, text)
            for match in matches:
                # Clean up the URL
                match = match.rstrip('.\'"')
                match = match.split('\\x')[0] if '\\x' in match else match
                match = unquote(match)
                
                # Fix protocol-relative URLs
                if match.startswith('//'):
                    match = 'https:' + match
                
                # Basic validation
                if match.startswith(('http://', 'https://')) and len(match) > 10:
                    urls.add(match)
        
        return list(urls)


class GifDownloader:
    """Async downloader for Discord favorite GIFs"""
    
    def __init__(self, base_dir: str = "downloads", max_concurrent: int = 5):
        self.base_dir = Path(base_dir)
        self.logs_dir = Path("logs")
        self.max_concurrent = max_concurrent
        self.stats = DownloadStats()
        self.semaphore = asyncio.Semaphore(max_concurrent)
        self.rate_limiter = RateLimiter()
        self.client = None
        self.progress = {"done": 0, "total": 0}
        self.url_cache = {}
        self.last_status_length = 0
        
    def clear_line(self):
        """Clear the current line in terminal"""
        print('\r' + ' ' * self.last_status_length + '\r', end='', flush=True)
        self.last_status_length = 0
    
    def print_progress(self, status: str = ""):
        """Print progress bar without overlapping text"""
        done = self.progress["done"]
        total = self.progress["total"]
        
        if total == 0:
            return
        
        # Clear previous line
        self.clear_line()
        
        # Calculate progress
        percent = (done / total) * 100
        bar_length = 30
        filled_length = int(bar_length * done // total)
        bar = '█' * filled_length + '░' * (bar_length - filled_length)
        
        # Build status line
        status_line = f"[{bar}] {percent:.1f}% ({done}/{total})"
        if status:
            status_line += f" {status}"
        
        # Print and track length
        print(status_line, end='', flush=True)
        self.last_status_length = len(status_line)
        
        if done >= total:
            print()
            self.last_status_length = 0
    
    def setup_folders(self):
        """Create folder structure"""
        self.base_dir.mkdir(exist_ok=True)
        self.logs_dir.mkdir(exist_ok=True)
        
        for _, folder_name in MEDIA_TYPES.values():
            (self.base_dir / folder_name).mkdir(exist_ok=True)
    
    async def get_client(self) -> httpx.AsyncClient:
        """Get or create HTTP client"""
        if self.client is None:
            self.client = httpx.AsyncClient(
                timeout=httpx.Timeout(30.0, connect=10.0),
                follow_redirects=True,
                max_redirects=5,
                headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                    'Accept': 'image/webp,image/*,*/*;q=0.8',
                }
            )
        return self.client
    
    async def close_client(self):
        """Close HTTP client"""
        if self.client:
            await self.client.aclose()
            self.client = None
    
    def sanitize_filename(self, filename: str) -> str:
        """Sanitize filename"""
        invalid_chars = '<>:"/\\|?*'
        for char in invalid_chars:
            filename = filename.replace(char, '_')
        
        while '__' in filename:
            filename = filename.replace('__', '_')
        
        if len(filename) > 150:
            name, ext = os.path.splitext(filename)
            filename = name[:150 - len(ext)] + ext
        
        return filename.strip('_. ')
    
    def get_file_extension(self, url: str, content_type: str) -> str:
        """Get appropriate file extension"""
        content_type = content_type.split(';')[0].strip().lower()
        
        if content_type in MEDIA_TYPES:
            return MEDIA_TYPES[content_type][0]
        
        # Guess from URL
        url_lower = url.lower()
        if '.gif' in url_lower or url_lower.endswith('.gif'):
            return '.gif'
        elif '.mp4' in url_lower or url_lower.endswith('.mp4'):
            return '.mp4'
        elif '.webm' in url_lower or url_lower.endswith('.webm'):
            return '.webm'
        elif '.webp' in url_lower or url_lower.endswith('.webp'):
            return '.webp'
        elif '.jpg' in url_lower or '.jpeg' in url_lower:
            return '.jpg'
        elif '.png' in url_lower or url_lower.endswith('.png'):
            return '.png'
        elif '.mov' in url_lower or url_lower.endswith('.mov'):
            return '.mov'
        
        # Try mimetypes
        guessed = mimetypes.guess_extension(content_type)
        if guessed:
            return guessed
        
        return '.bin'
    
    def get_folder_name(self, extension: str) -> str:
        """Get folder name based on extension"""
        extension = extension.lower()
        
        if extension in ['.gif']:
            return 'gif'
        elif extension in ['.mp4', '.webm', '.mov']:
            return 'mp4'
        elif extension in ['.jpg', '.jpeg', '.png', '.webp']:
            return 'img'
        else:
            return 'other'
    
    def get_file_path(self, url: str, content_type: str, index: int) -> Path:
        """Determine file path"""
        extension = self.get_file_extension(url, content_type)
        folder = self.get_folder_name(extension)
        
        parsed = urlparse(url)
        filename = os.path.basename(parsed.path)
        
        if not filename or filename == '/':
            import hashlib
            url_hash = hashlib.md5(url.encode()).hexdigest()[:8]
            filename = f"file_{index}_{url_hash}{extension}"
        else:
            name, ext = os.path.splitext(filename)
            if not ext or ext.lower() != extension.lower():
                filename = f"{name}_{index}{extension}"
            else:
                filename = f"{name}_{index}{ext}"
        
        filename = self.sanitize_filename(filename)
        return self.base_dir / folder / filename
    
    async def resolve_urls(self, urls: List[str]) -> List[str]:
        """Resolve special URLs"""
        print(f"\nResolving special URLs...")
        
        resolver = URLResolver(self.rate_limiter)
        resolved_urls = []
        client = await self.get_client()
        
        for i, url in enumerate(urls):
            try:
                if url in self.url_cache:
                    resolved_urls.extend(self.url_cache[url])
                    continue
                
                # Show simple progress
                if i % 10 == 0:
                    print(f"\rResolving: {i+1}/{len(urls)}", end="", flush=True)
                
                resolved = await resolver.resolve_url(client, url)
                
                if resolved:
                    self.url_cache[url] = resolved
                    resolved_urls.extend(resolved)
                    self.stats.resolved += 1
                else:
                    resolved_urls.append(url)
                    
            except Exception as e:
                logger.debug(f"Failed to resolve {url}: {e}")
                resolved_urls.append(url)
        
        print(f"\rResolved {self.stats.resolved} URLs")

        discord_urls = [u for u in resolved_urls if URLResolver.is_discord_attachment(u)]
        if discord_urls and DISCORD_TOKEN:
            print(f"\nRefreshing {len(discord_urls)} Discord attachment URLs...")
            refreshed_map = await resolver.bulk_refresh_discord_urls(client, discord_urls)
            print(f"Refreshed {len(refreshed_map)} URLs")
            resolved_urls: List[str] = [
                refreshed_map.get(u) or u
                for u in resolved_urls
            ]

        return resolved_urls
    
    async def download_file(self, url: str, index: int) -> bool:
        """Download a single file"""
        async with self.semaphore:
            try:
                # Validate URL first
                if not URLResolver.is_valid_url(url):
                    error_msg = "Invalid URL"
                    self.stats.add_error(url, error_msg)
                    self.stats.failed += 1
                    self.progress["done"] += 1
                    self.print_progress("invalid")
                    return False
                
                client = await self.get_client()
                domain = URLResolver.extract_domain(url)
                await self.rate_limiter.wait_for_domain(domain)
                
                try:
                    # Skip HEAD request to reduce requests
                    content_type = 'application/octet-stream'
                    
                    # Get file path
                    file_path = self.get_file_path(url, content_type, index)
                    
                    # Check if file already exists
                    if file_path.exists():
                        self.stats.skipped += 1
                        self.progress["done"] += 1
                        self.print_progress("exists")
                        return True
                    
                    # Download with timeout
                    timeout = httpx.Timeout(30.0, connect=10.0)
                    response = await client.get(url, timeout=timeout)
                    
                    # Check for errors
                    if response.status_code == 404:
                        error_msg = "HTTP 404"
                        self.stats.add_error(url, error_msg)
                        self.stats.failed += 1
                        self.progress["done"] += 1
                        self.print_progress("404")
                        return False
                    elif response.status_code == 429:
                        error_msg = "Rate limited"
                        self.stats.add_error(url, error_msg)
                        self.stats.failed += 1
                        self.progress["done"] += 1
                        self.print_progress("429")
                        return False
                    
                    response.raise_for_status()
                    
                    # Get content type
                    actual_content_type = response.headers.get('Content-Type', '').split(';')[0].strip()
                    if actual_content_type:
                        content_type = actual_content_type
                    
                    # Skip HTML
                    if content_type.lower() == 'text/html':
                        self.stats.unsupported += 1
                        self.progress["done"] += 1
                        self.print_progress("html")
                        return False
                    
                    # Get content
                    content = response.content
                    
                    # Check for error pages
                    if len(content) > 500:
                        text_preview = content[:1000].decode('latin-1', errors='ignore').lower()
                        if any(error in text_preview for error in ['error', 'not found', '404', '403', 'unavailable']):
                            raise Exception("Error page")
                    
                    # Update file path
                    file_path = self.get_file_path(url, content_type, index)
                    
                    # Save file
                    file_path.parent.mkdir(parents=True, exist_ok=True)
                    file_path.write_bytes(content)
                    
                    # Update stats
                    self.stats.successful += 1
                    self.stats.downloaded_files.append(str(file_path))
                    
                    # Show success with clean output
                    file_size = len(content)
                    size_str = f"{file_size:,}B"
                    if file_size > 1024*1024:
                        size_str = f"{file_size/(1024*1024):.1f}MB"
                    elif file_size > 1024:
                        size_str = f"{file_size/1024:.1f}KB"
                    
                    self.progress["done"] += 1
                    short_name = file_path.name[:15] + "..." if len(file_path.name) > 15 else file_path.name
                    self.print_progress(f"{short_name} ({size_str})")
                    return True
                        
                finally:
                    self.rate_limiter.release_domain(domain)
                    
            except httpx.HTTPStatusError as e:
                if e.response.status_code == 404:
                    error_msg = "HTTP 404"
                    self.stats.not_found += 1
                elif e.response.status_code == 429:
                    error_msg = "HTTP 429"
                    self.stats.rate_limited += 1
                else:
                    error_msg = f"HTTP {e.response.status_code}"
                self.stats.add_error(url, error_msg)
                self.stats.failed += 1
                self.progress["done"] += 1
                self.print_progress(f"HTTP {e.response.status_code}")
                return False
            except httpx.TimeoutException:
                error_msg = "Timeout"
                self.stats.add_error(url, error_msg)
                self.stats.failed += 1
                self.progress["done"] += 1
                self.print_progress("timeout")
                return False
            except Exception as e:
                error_msg = str(e)[:30]
                self.stats.add_error(url, error_msg)
                self.stats.failed += 1
                self.progress["done"] += 1
                self.print_progress("error")
                return False
    
    async def download_all(self, urls: List[str]):
        """Download all URLs"""
        self.stats.total = len(urls)
        self.stats.start_time = datetime.now()
        self.progress = {"done": 0, "total": len(urls)}
        
        print(f"\nStarting download of {self.stats.total} files")
        print(f"Output folder: {self.base_dir.absolute()}")
        print(f"Max concurrent: {self.max_concurrent}")
        print("-" * 50)
        
        # Create tasks
        tasks = []
        for i, url in enumerate(urls):
            task = asyncio.create_task(self.download_file(url, i))
            tasks.append(task)
        
        # Wait for all tasks
        try:
            await asyncio.gather(*tasks, return_exceptions=True)
        except Exception as e:
            print(f"\nWarning: {e}")
        
        # Close client
        await self.close_client()
        
        self.stats.end_time = datetime.now()
        print()  # Clear the progress line
    
    def print_statistics(self):
        """Print download statistics"""
        print("\n" + "="*50)
        print("DOWNLOAD STATISTICS")
        print("="*50)
        
        duration = self.stats.duration
        mins, secs = divmod(duration, 60)
        time_str = f"{int(mins)}m {int(secs)}s"
        
        print(f"Total URLs:          {self.stats.total}")
        print(f"Successfully saved:  {self.stats.successful}")
        print(f"Skipped (exists):    {self.stats.skipped}")
        print(f"Failed downloads:    {self.stats.failed}")
        print(f"  - 404 Not Found:   {self.stats.not_found}")
        print(f"  - Rate limited:    {self.stats.rate_limited}")
        print(f"URLs resolved:       {self.stats.resolved}")
        
        if self.stats.total > 0:
            success_rate = self.stats.success_rate
            print(f"Success rate:        {success_rate:.1f}%")
            
            # Add user feedback about success rate
            if success_rate >= 70:
                print(f"Status:              Excellent! ({success_rate:.1f}% success)")
            elif success_rate >= 50:
                print(f"Status:              Good ({success_rate:.1f}% success)")
            elif success_rate >= 30:
                print(f"Status:              Normal ({success_rate:.1f}% success - many gifs actually saved)")
            else:
                print(f"Status:              Low ({success_rate:.1f}% success - you should be good for the most part)")
        
        print(f"Time elapsed:        {time_str}")
        print("="*50)
        
        # Show downloaded files summary
        if self.stats.downloaded_files:
            print(f"\nDownloaded to folders:")
            folders = {}
            for file in self.stats.downloaded_files:
                folder = Path(file).parent.name
                folders[folder] = folders.get(folder, 0) + 1
            
            for folder, count in sorted(folders.items()):
                print(f"  {folder}/ - {count} file{'s' if count != 1 else ''}")
    
    def save_reports(self):
        """Save reports to logs folder"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # Save failed URLs
        if self.stats.failed_urls:
            failed_path = self.logs_dir / f"failed_urls_{timestamp}.txt"
            with open(failed_path, 'w', encoding='utf-8') as f:
                f.write(f"Failed URLs - {timestamp}\n")
                f.write("="*60 + "\n\n")
                for url, error in self.stats.failed_urls.items():
                    f.write(f"{url}\n")
                    f.write(f"Error: {error}\n\n")
            print(f"Failed URLs saved: {failed_path}")
        
        # Save successful downloads list
        if self.stats.downloaded_files:
            list_path = self.logs_dir / f"downloaded_files_{timestamp}.txt"
            with open(list_path, 'w', encoding='utf-8') as f:
                f.write(f"Downloaded Files - {timestamp}\n")
                f.write("="*60 + "\n\n")
                for file in self.stats.downloaded_files:
                    f.write(f"{file}\n")
            print(f"File list saved: {list_path}")
        
        # Save statistics
        stats_path = self.logs_dir / f"statistics_{timestamp}.json"
        stats_data = {
            "timestamp": datetime.now().isoformat(),
            "total_urls": self.stats.total,
            "successful": self.stats.successful,
            "skipped": self.stats.skipped,
            "failed": self.stats.failed,
            "not_found": self.stats.not_found,
            "rate_limited": self.stats.rate_limited,
            "resolved": self.stats.resolved,
            "success_rate": self.stats.success_rate,
            "duration_seconds": self.stats.duration,
            "output_folder": str(self.base_dir.absolute()),
        }
        with open(stats_path, 'w', encoding='utf-8') as f:
            json.dump(stats_data, f, indent=2)
        print(f"Statistics saved: {stats_path}")


async def main():
    """Main function"""
    print("Discord Favorite GIF Downloader")
    print("Author: nloginov")
    print("="*50)

    # Get Discord token for refreshing URLs later
    global DISCORD_TOKEN
    token_input = input("Enter your Discord token (leave blank to skip): ").strip()
    if token_input:
        DISCORD_TOKEN = token_input

    # Find input file
    input_files = ['data.json', 'data.txt', 'input.json', 'input.txt']
    input_file = None
    
    for filename in input_files:
        if os.path.exists(filename):
            input_file = filename
            break
    
    if not input_file:
        print("Error: No input file found!")
        print("Please create one of these files:")
        for filename in input_files[:2]:
            print(f"  {filename}")
        sys.exit(1)
    
    print(f"Reading from: {input_file}")
    
    # Read and parse input data
    try:
        with open(input_file, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read().strip()
        
        if not content:
            print("Error: Input file is empty")
            sys.exit(1)
        
        # Parse JSON if needed
        if input_file.endswith('.json'):
            try:
                data = json.loads(content)
                content = data.get('settings', '')
                if not content:
                    print("Error: JSON file doesn't contain 'settings' key")
                    sys.exit(1)
            except json.JSONDecodeError:
                print("Warning: Invalid JSON, treating as raw data")
        
        # Decode base64
        try:
            protobuf_data = base64.b64decode(content)
            print(f"Decoded {len(protobuf_data):,} bytes")
        except:
            print("Warning: Not valid base64, treating as raw text")
            protobuf_data = content.encode('utf-8')
        
    except Exception as e:
        print(f"Error reading file: {e}")
        sys.exit(1)
    
    # Extract URLs
    print("\nExtracting URLs...")
    parser = ProtobufParser()
    urls = parser.extract_urls_simple(protobuf_data)

    # Fix some URLs' formatting
    badurl = re.compile("http.+/https?/")
    urls = [badurl.sub("https://", u) for u in urls]
    
    if not urls:
        print("Error: No URLs found!")
        sys.exit(1)
    
    print(f"Found {len(urls):,} unique URLs")
    
    # Filter URLs
    filtered_urls = []
    for url in urls:
        if URLResolver.is_valid_url(url) and len(url) > 10 and not url.startswith('data:'):
            filtered_urls.append(url)
    
    print(f"After filtering: {len(filtered_urls):,} valid URLs")
    
    # Initialize downloader
    downloader = GifDownloader(base_dir="downloads", max_concurrent=5)
    downloader.setup_folders()
    
    # Resolve special URLs
    resolved_urls = await downloader.resolve_urls(filtered_urls)
    print(f"After resolution: {len(resolved_urls):,} URLs to download")
    
    # Download files
    await downloader.download_all(resolved_urls)
    
    # Print statistics and save reports
    downloader.print_statistics()
    downloader.save_reports()
    
    # Final summary
    print("\n" + "="*50)
    if downloader.stats.successful > 0:
        print(f"Download complete: {downloader.stats.successful} files saved")
        print(f"Location: downloads/ folder")
    else:
        print("No files were downloaded")
        print("Note: Many Discord files get deleted over time")
    print("="*50)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n\nDownload interrupted by user")
        sys.exit(0)
    except Exception as e:
        print(f"\nUnexpected error: {e}")

        sys.exit(1)
