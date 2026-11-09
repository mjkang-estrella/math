"""Extract title, authors, version history, comments and journal ref from cached arXiv abs pages (read-only)."""
import html
import json
import pathlib
import re
import sys

d = pathlib.Path(sys.argv[1])
for p in sorted(d.glob('abs-*.body')):
    if p.name == 'abs-1803.body':
        continue
    t = p.read_text(errors='replace')
    title = re.search(r'<meta name="citation_title" content="([^"]*)"', t)
    authors = re.findall(r'<meta name="citation_author" content="([^"]*)"', t)
    vers = re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*?)\s*\(', t)
    com = re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>', t, re.S)
    jr = re.search(r'<td class="tablecell jref">(.*?)</td>', t, re.S)
    doi = re.search(r'<td class="tablecell doi">(.*?)</td>', t, re.S)
    print(p.name)
    print('  title:', html.unescape(title.group(1)) if title else None)
    print('  authors:', '; '.join(authors))
    print('  versions:', vers)
    if com:
        print('  comments:', re.sub(r'<[^>]+>', '', html.unescape(com.group(1))).strip())
    if jr:
        print('  jref:', re.sub(r'<[^>]+>', '', html.unescape(jr.group(1))).strip())
    if doi:
        print('  doi:', re.sub(r'<[^>]+>', '', html.unescape(doi.group(1))).strip())
ph = d / 'pool-head.body'
if ph.exists():
    j = json.loads(ph.read_text())
    print('pool HEAD', j.get('sha'), j.get('commit', {}).get('committer', {}).get('date'))
for n in ('omega-head.body', 'openai-head.body'):
    q = d / n
    if q.exists():
        j = json.loads(q.read_text())
        print(n, j.get('sha'), j.get('commit', {}).get('committer', {}).get('date'))
