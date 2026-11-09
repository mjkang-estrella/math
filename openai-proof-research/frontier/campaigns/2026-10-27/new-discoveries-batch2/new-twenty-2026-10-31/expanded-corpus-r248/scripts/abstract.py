"""Print title, authors, versions, journal ref and abstract from cached arXiv abs bodies (read-only)."""
import html, re, sys, glob
paths = []
for a in sys.argv[1:]:
    paths += sorted(glob.glob(a))
for path in paths:
    t = open(path, encoding='utf-8', errors='replace').read()
    title = re.search(r'<meta name="citation_title" content="([^"]*)"', t)
    authors = re.findall(r'<meta name="citation_author" content="([^"]*)"', t)
    ab = re.search(r'<meta name="citation_abstract" content="([^"]*)"', t, re.S)
    sub = re.search(r'<div class="submission-history">(.*?)</div>', t, re.S)
    jr = re.search(r'<td class="tablecell jref">(.*?)</td>', t, re.S)
    doi = re.search(r'<td class="tablecell doi">(.*?)</td>', t, re.S)
    cm = re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>', t, re.S)
    clean = lambda s: ' '.join(re.sub(r'<[^>]+>', ' ', html.unescape(s)).split())
    print('##', path.rsplit('/', 1)[-1])
    print('title:', html.unescape(title.group(1)) if title else None)
    print('authors:', '; '.join(authors))
    if sub:
        h = clean(sub.group(1))
        print('history:', re.sub(r'From: .*?\[', '[', h)[:500])
    if jr: print('jref:', clean(jr.group(1)))
    if doi: print('doi:', clean(doi.group(1)))
    if cm: print('comments:', clean(cm.group(1)))
    print('abstract:', ' '.join(html.unescape(ab.group(1)).split())[:1200] if ab else None)
    print()
