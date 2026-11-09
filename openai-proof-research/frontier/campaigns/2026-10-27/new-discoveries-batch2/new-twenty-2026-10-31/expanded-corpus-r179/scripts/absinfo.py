import sys,re,html,pathlib
for f in sys.argv[1:]:
    t=pathlib.Path(f).read_text(errors='replace')
    title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
    auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
    ab=re.search(r'<meta name="citation_abstract" content="([^"]*)"',t,re.S)
    vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
    jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
    com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',t,re.S)
    print('==',f); print('T:',html.unescape(title.group(1)) if title else None)
    print('A:','; '.join(auth)); print('V:',vers)
    if jref: print('J:',re.sub('<[^>]+>','',jref.group(1)).strip())
    if com: print('C:',re.sub('<[^>]+>','',html.unescape(com.group(1))).strip()[:200])
    print('AB:',html.unescape(ab.group(1))[:900].replace('\n',' ') if ab else None)
