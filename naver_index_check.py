"""네이버 site: 검색으로 색인 여부를 확인합니다. 로그인은 쓰지 않습니다."""
from __future__ import annotations

import re
from urllib.parse import urlencode, urljoin, urlparse
from urllib.request import Request, urlopen

SEARCH_SSC = "tab.nx.all"
DEFAULT_DELAY_SEC = 1.5

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "ko-KR,ko;q=0.9",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Referer": "https://search.naver.com/",
}

NO_RESULT_PATTERNS = (
    "검색 결과가 없습니다",
    "검색결과가 없습니다",
    "에 대한 검색결과가 없습니다",
    "결과가 없습니다",
)

TITLE_LINK_RE = re.compile(
    r'<a\b(?=[^>]*\bnocr="1")(?=[^>]*data-heatmap-target="\.link")[^>]*href="(https?://[^"]+)"',
    re.I,
)
JSON_DESK_HREF_RE = re.compile(r'"deviceType":"desk","href":"(https?://[^"]+)"')


def normalize_href(href: str) -> str:
    return href.replace("\\/", "/").replace("&amp;", "&")


def normalize_site(value: str) -> str:
    raw = (value or "").strip().lower()
    if not raw:
        raise ValueError("URL이 비어 있습니다.")
    if "://" not in raw:
        raw = f"https://{raw}"
    parsed = urlparse(raw)
    host = (parsed.hostname or "").removeprefix("www.")
    path = (parsed.path or "").rstrip("/")
    return host + path


def url_matches(result_url: str, target: str) -> bool:
    result = normalize_site(result_url)
    target_norm = normalize_site(target)
    result_host = result.split("/", 1)[0]
    target_host = target_norm.split("/", 1)[0]
    if result_host != target_host:
        return False
    result_path = result[len(result_host):].lstrip("/")
    target_path = target_norm[len(target_host):].lstrip("/")
    if not target_path or not result_path:
        return True
    return result_path.startswith(target_path) or target_path.startswith(result_path)


def site_search_query(site: str) -> str:
    value = site.strip().rstrip("/")
    if not value.startswith("http"):
        value = f"https://{value}"
    return f"site:{value}"


def build_search_url(query: str, start: int = 1) -> str:
    params = urlencode(
        {
            "where": "nexearch",
            "sm": "tab_hty.top",
            "query": query,
            "ssc": SEARCH_SSC,
            "start": str(start),
        }
    )
    return f"https://search.naver.com/search.naver?{params}"


def fetch_html(url: str, timeout: float = 20) -> str:
    request = Request(url, headers=HEADERS)
    with urlopen(request, timeout=timeout) as response:
        raw = response.read()
        charset = response.headers.get_content_charset() or "utf-8"
    return raw.decode(charset, errors="replace")


def html_has_no_results(html: str) -> bool:
    if not html:
        return False
    lowered = html.lower()
    return any(pattern in html for pattern in NO_RESULT_PATTERNS) or "search_not_found" in lowered


def strip_suggest_blocks(html: str) -> str:
    text = re.sub(
        r'<div[^>]*class="[^"]*suggest_wrap[^"]*"[\s\S]*?</div>\s*</div>',
        "",
        html or "",
        flags=re.I,
    )

    def _drop_suggest(match: re.Match[str]) -> str:
        chunk = match.group(0)
        return "" if re.search(r"suggest", chunk, re.I) else chunk

    return re.sub(
        r'<div[^>]*class="[^"]*sp_nreview[^"]*api_subject_bx[^"]*"[\s\S]{0,8000}',
        _drop_suggest,
        text,
        flags=re.I,
    )


def extract_json_desk_urls(html: str) -> list[str]:
    urls: list[str] = []
    seen: set[str] = set()
    for match in JSON_DESK_HREF_RE.finditer(html or ""):
        link = normalize_href(match.group(1))
        if link in seen:
            continue
        seen.add(link)
        urls.append(link)
    return urls


def extract_generic_http_urls(html: str, host: str) -> list[str]:
    if not host:
        return []
    urls: list[str] = []
    seen: set[str] = set()
    host_re = re.escape(host)
    pattern = re.compile(rf"https?://(?:www\.)?{host_re}[^\"'\s<>]*", re.I)
    for match in pattern.finditer(html or ""):
        link = normalize_href(match.group(0)).rstrip("),.;")
        try:
            from urllib.parse import unquote

            link = unquote(link)
        except Exception:
            pass
        if link in seen:
            continue
        seen.add(link)
        urls.append(link)
    return urls


def extract_page_results(html: str, site_url: str = "") -> list[str]:
    results: list[str] = []
    seen: set[str] = set()
    for match in TITLE_LINK_RE.finditer(html or ""):
        link = normalize_href(match.group(1))
        if link in seen:
            continue
        seen.add(link)
        results.append(link)
    if results:
        return results
    json_urls = extract_json_desk_urls(html)
    if json_urls:
        return json_urls
    try:
        host = normalize_site(site_url).split("/", 1)[0]
    except ValueError:
        return []
    body_only = re.sub(r"<head[\s\S]*?</head>", "", html or "", count=1, flags=re.I)
    body_only = re.sub(r"<script[\s\S]*?</script>", "", body_only, flags=re.I)
    body_only = re.sub(r"<style[\s\S]*?</style>", "", body_only, flags=re.I)
    host_plain = re.escape(host)
    href_re = re.compile(
        rf"""href\s*=\s*["'](https?://(?:www\.)?{host_plain}[^"']*)["']""",
        re.I,
    )
    from urllib.parse import unquote

    found: list[str] = []
    for match in href_re.finditer(body_only):
        link = normalize_href(match.group(1)).rstrip("),.;")
        try:
            link = unquote(link)
        except Exception:
            pass
        if link in seen:
            continue
        seen.add(link)
        found.append(link)
    return found


def extract_suggest_follow_url(html: str, expected_query: str) -> str | None:
    if not html or not re.search(r"suggest_wrap", html, re.I):
        return None
    expected = (expected_query or "").strip()
    expected_host = ""
    try:
        raw = re.sub(r"^site:", "", expected, count=1, flags=re.I).strip()
        expected_host = urlparse(raw if "://" in raw else f"https://{raw}").hostname or ""
        expected_host = expected_host.lower()
    except Exception:
        expected_host = ""
    blocks = re.findall(
        r'<div[^>]*class="[^"]*suggest_wrap[^"]*"[^>]*>[\s\S]*?</div>\s*</div>',
        html,
        flags=re.I,
    )
    if not blocks:
        idx = re.search(r'class="[^"]*suggest_wrap', html, re.I)
        if idx:
            blocks = [html[idx.start(): idx.start() + 5000]]
    for block in blocks:
        for match in re.finditer(r"""href\s*=\s*["']([^"']+)["']""", block, re.I):
            raw_href = normalize_href(match.group(1))
            if re.search(r"help\.naver\.com", raw_href, re.I):
                continue
            try:
                absolute = urljoin("https://search.naver.com/search.naver", raw_href)
                parsed = urlparse(absolute)
            except Exception:
                continue
            if not re.search(r"search\.naver\.com", parsed.hostname or "", re.I):
                continue
            query = ""
            for part in (parsed.query or "").split("&"):
                if part.startswith("query="):
                    from urllib.parse import unquote

                    query = unquote(part[6:])
                    break
            query_norm = query.strip()
            if not query_norm:
                continue
            exact = (
                query_norm == expected
                or query_norm.lower() == expected.lower()
                or query_norm.replace(" ", "") == expected.replace(" ", "")
            )
            has_host = bool(expected_host and expected_host in query_norm.lower())
            looks_like_site = query_norm.lower().startswith("site:")
            if (exact or has_host) and looks_like_site:
                return absolute
    return None


def evaluate_search_html(html: str, site_url: str, query: str) -> dict:
    body = strip_suggest_blocks(html)
    if html_has_no_results(body) or html_has_no_results(html):
        return {
            "indexed": False,
            "message": "미인덱싱",
            "sample_url": None,
            "result_count": 0,
            "query": query,
        }
    urls = extract_page_results(body, site_url)
    matching = []
    for item in urls:
        try:
            if url_matches(item, site_url):
                matching.append(item)
        except ValueError:
            continue
    try:
        domain = normalize_site(site_url).split("/", 1)[0]
    except ValueError:
        domain = ""
    domain_urls = []
    if domain:
        for item in urls:
            try:
                if normalize_site(item).split("/", 1)[0] == domain:
                    domain_urls.append(item)
            except ValueError:
                continue
    if matching:
        return {
            "indexed": True,
            "message": "인덱싱됨",
            "sample_url": matching[0],
            "result_count": len(domain_urls) or len(urls),
            "query": query,
        }
    if domain_urls:
        return {
            "indexed": True,
            "message": f"도메인 인덱싱 ({len(domain_urls)}건)",
            "sample_url": domain_urls[0],
            "result_count": len(domain_urls),
            "query": query,
        }
    if domain:
        host_plain = re.escape(domain)
        resultish = re.compile(rf"""href=["']https?://(?:www\.)?{host_plain}[^"']*["']""", re.I)
        if resultish.search(body):
            sample = extract_generic_http_urls(body, domain)
            return {
                "indexed": True,
                "message": "인덱싱됨 (결과 링크)",
                "sample_url": (sample[0] if sample else f"https://{domain}/"),
                "result_count": 1,
                "query": query,
            }
    return {
        "indexed": False,
        "message": "미인덱싱",
        "sample_url": None,
        "result_count": 0,
        "query": query,
    }


def check_naver_index(site_url: str) -> dict:
    query = site_search_query(site_url)
    try:
        html = fetch_html(build_search_url(query, 1))
    except Exception as exc:
        return {
            "indexed": None,
            "message": f"확인 실패 ({exc})",
            "sample_url": None,
            "result_count": 0,
            "query": query,
        }
    follow = extract_suggest_follow_url(html, query)
    if follow:
        try:
            followed_html = fetch_html(follow)
        except Exception as exc:
            return {
                "indexed": None,
                "message": f"제안 링크 확인 실패 ({exc})",
                "sample_url": None,
                "result_count": 0,
                "query": query,
            }
        followed = evaluate_search_html(followed_html, site_url, query)
        message = followed["message"]
        if followed["indexed"] is True:
            if message == "인덱싱됨":
                message = "인덱싱됨 (제안 링크)"
            else:
                message = f"{message} (제안 링크)"
        return {**followed, "message": message, "suggest_followed": True}
    return evaluate_search_html(html, site_url, query)


def _self_check() -> None:
    assert url_matches("https://a.blogspot.com/2026/01/x.html", "https://a.blogspot.com/")
    assert not url_matches("https://b.blogspot.com/", "https://a.blogspot.com/")
    query = "site:https://a.blogspot.com"
    none = evaluate_search_html("<div>검색결과가 없습니다</div>", "https://a.blogspot.com/", query)
    assert none["indexed"] is False
    hit = (
        '<a nocr="1" href="https://a.blogspot.com/2026/01/post.html" '
        'class="bw6s5j6PgZwBpJOh" data-heatmap-target=".link">'
    )
    found = evaluate_search_html(hit, "https://a.blogspot.com/", query)
    assert found["indexed"] is True
    suggest = '<div class="suggest_wrap">https://a.blogspot.com</div>검색결과가 없습니다'
    skipped = evaluate_search_html(suggest, "https://a.blogspot.com/", query)
    assert skipped["indexed"] is False
    desk = '"deviceType":"desk","href":"https://a.blogspot.com/p/1.html"'
    from_json = evaluate_search_html(desk, "https://a.blogspot.com/", query)
    assert from_json["indexed"] is True
    assert site_search_query("a.blogspot.com") == "site:https://a.blogspot.com"


if __name__ == "__main__":
    _self_check()
    print("ok")
