import sys,re,html
from pathlib import Path
for p in sorted(Path(sys.argv[1]).glob('sources/abs-*/body')):
    t=p.read_text(errors='replace')
    title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    vers=re.findall(r'<strong><a href="/abs/[^"]*">(\[v\d+\])</a></strong>\s*([^<]*)',t)
    vers2=re.findall(r'\[v(\d+)\]</[^>]*>\s*([^<]{0,40})',t)
    com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',t,re.S)
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    ab=re.search(r'<meta name="citation_abstract" content="([^"]*)"',t,re.S)
    print('==',p.parent.name.split('-2026')[0], '|', title and html.unescape(title.group(1)), '|', auth[:5])
    print('  versions:', vers2)
    print('  comments:', com and re.sub('<[^>]+>','',com.group(1)).strip()[:200], '| jref:', jr and re.sub('<[^>]+>','',jr.group(1)).strip())
    print('  abstract:', ab and html.unescape(ab.group(1))[:700])
