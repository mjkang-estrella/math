import re,html,sys
t=open(sys.argv[1],errors='replace').read()
items=re.findall(r'<li class="arxiv-result">(.*?)</li>\s*(?=<li class="arxiv-result">|</ol>)',t,re.S)
print('results',len(items), re.search(r'Showing [^<]*',t).group(0) if re.search(r'Showing [^<]*',t) else '')
pat=sys.argv[2] if len(sys.argv)>2 else None
for it in items:
  aid=re.search(r'arxiv.org/abs/([\w./]+)',it); ti=re.search(r'<p class="title is-5 mathjax">(.*?)</p>',it,re.S)
  dt=re.search(r'Submitted</span>\s*([^;<]*)',it)
  ab=re.search(r'<span class="abstract-full[^>]*>(.*?)<a',it,re.S)
  title=re.sub(r'\s+',' ',re.sub('<[^>]+>','',html.unescape(ti.group(1)))).strip() if ti else ''
  abst=re.sub(r'\s+',' ',re.sub('<[^>]+>','',html.unescape(ab.group(1)))).strip() if ab else ''
  if pat and not re.search(pat,title+' '+abst,re.I): continue
  print(aid.group(1) if aid else '?', '|', dt.group(1).strip() if dt else '', '|', title)
  if pat: print('    ',abst[:700])
