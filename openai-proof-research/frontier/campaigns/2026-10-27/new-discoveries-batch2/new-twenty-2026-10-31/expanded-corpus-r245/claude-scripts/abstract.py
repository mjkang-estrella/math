"""Print title, authors, versions and abstract from cached arXiv abs bodies (read-only)."""
import html
import re
import sys

for path in sys.argv[1:]:
    t = open(path, encoding='utf-8', errors='replace').read()
    title = re.search(r'<meta name="citation_title" content="([^"]*)"', t)
    authors = re.findall(r'<meta name="citation_author" content="([^"]*)"', t)
    ab = re.search(r'<meta name="citation_abstract" content="([^"]*)"', t, re.S)
    sub = re.search(r'<div class="submission-history">(.*?)</div>', t, re.S)
    print('##', path.rsplit('/', 1)[-1])
    print('title:', html.unescape(title.group(1)) if title else None)
    print('authors:', '; '.join(authors))
    if sub:
        print('history:', ' '.join(re.sub(r'<[^>]+>', ' ', html.unescape(sub.group(1))).split())[:600])
    print('abstract:', html.unescape(ab.group(1)) if ab else None)
    print()
