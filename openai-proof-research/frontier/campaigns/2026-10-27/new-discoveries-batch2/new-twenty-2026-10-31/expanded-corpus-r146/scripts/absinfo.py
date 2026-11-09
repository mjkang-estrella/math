import re,html,pathlib,sys
for p in sorted(pathlib.Path('sources').glob('*.abs')):
  t=p.read_text(errors='replace')
  title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
  auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
  ab=re.search(r'<meta name="citation_abstract" content="([^"]*)"',t,re.S)
  vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
  jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
  doi=re.search(r'data-doi="([^"]*)"|<td class="tablecell doi">.*?href="([^"]*)"',t,re.S)
  print('==',p.stem,'|',html.unescape(title.group(1)) if title else None,'|',auth[:6])
  print('  versions:',[(v,d.strip()[:40]) for v,d in vers],'| jref:',html.unescape(re.sub('<[^>]+>','',jref.group(1))).strip() if jref else None)
  if '-v' in sys.argv: print('  ABS:',html.unescape(ab.group(1))[:1500] if ab else None)
