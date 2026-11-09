import pathlib,re,html,json,sys
L=pathlib.Path(__file__).resolve().parents[1]
out={}
for f in sorted((L/'sources').glob('*.abs')):
  t=f.read_text(errors='replace')
  title=re.search(r'<meta name="citation_title" content="([^"]*)"',t)
  auth=re.findall(r'<meta name="citation_author" content="([^"]*)"',t)
  vers=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
  jref=re.search(r'<td class="tablecell jref">(.*?)</td>',t,re.S)
  doi=re.search(r'<td class="tablecell doi">.*?href="([^"]*)"',t,re.S)
  com=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',t,re.S)
  ab=re.search(r'<blockquote class="abstract mathjax">(.*?)</blockquote>',t,re.S)
  o=dict(title=html.unescape(title.group(1)) if title else None,authors=auth,versions=[(a,b.strip()) for a,b in vers],
    jref=re.sub('<[^>]+>','',jref.group(1)).strip() if jref else None, doi=doi.group(1) if doi else None,
    comments=re.sub('<[^>]+>','',com.group(1)).strip() if com else None,
    abstract=re.sub(r'\s+',' ',re.sub('<[^>]+>','',html.unescape(ab.group(1)))).strip() if ab else None)
  out[f.stem]=o
(L/'outputs/abs-info.json').write_text(json.dumps(out,indent=1,ensure_ascii=False))
for k,o in out.items():
  print('=====',k,o['title'],'|',', '.join(o['authors']));print(' versions',o['versions'],'| jref',o['jref'],'| doi',o['doi'],'| comments',o['comments'])
  if '-a' in sys.argv: print(' ABS',o['abstract'][:900])
