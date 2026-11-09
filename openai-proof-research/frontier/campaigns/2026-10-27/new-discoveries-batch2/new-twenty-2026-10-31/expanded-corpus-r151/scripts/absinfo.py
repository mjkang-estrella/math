import sys,re,html,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('abs-*.body')):
    t=p.read_text(errors='replace')
    title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    abst=re.search(r'<meta name="citation_abstract" content="([^"]*)"',t,re.S)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)<',t)
    jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',t,re.S)
    print('=====',p.name[4:-5], '|', html.unescape(title.group(1)) if title else None)
    print('  authors:', '; '.join(html.unescape(a) for a in auth))
    print('  versions:', [(v,s.strip()[:40]) for v,s in vers])
    if jref: print('  jref:', re.sub('<[^>]+>','',html.unescape(jref.group(1))).strip())
    if com: print('  comments:', re.sub('<[^>]+>','',html.unescape(com.group(1))).strip()[:200])
    if abst: print('  abstract:', html.unescape(abst.group(1)).replace('\n',' ')[:900])
