import sys,pathlib,re,html
D=pathlib.Path(sys.argv[1]).resolve()/'sources'
for p in sorted(D.glob('abs-*.body')):
  b=p.read_text('utf8','replace')
  title=re.search(r'<meta name="citation_title" content="([^"]*)"',b)
  auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',b)
  ab=re.search(r'<meta name="citation_abstract" content="([^"]*)"',b,re.S)
  vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',b)
  com=re.search(r'<td class="tablecell comments[^"]*">(.*?)</td>',b,re.S)
  jref=re.search(r'<td class="tablecell jref">(.*?)</td>',b,re.S)
  print('=====',p.stem, html.unescape(title.group(1)) if title else None)
  print(' authors:','; '.join(auth))
  print(' versions:',[(v,d.strip()[:40]) for v,d in vers])
  if com: print(' comments:',html.unescape(re.sub('<[^>]+>','',com.group(1))).strip()[:300])
  if jref: print(' jref:',html.unescape(re.sub('<[^>]+>','',jref.group(1))).strip()[:300])
  if ab: print(' abstract:',html.unescape(ab.group(1)).strip()[:900])
