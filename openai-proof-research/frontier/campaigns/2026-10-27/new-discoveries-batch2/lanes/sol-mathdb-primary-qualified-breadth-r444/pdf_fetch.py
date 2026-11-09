from pathlib import Path
import urllib.request,urllib.error,json,re,hashlib,subprocess
R=Path(__file__).resolve().parent; jobs=[]
for p in sorted((R/'sources').glob('*.html')):
 m=re.search(r'name="citation_pdf_url" content="([^"]+)"',p.read_text());assert m
 jobs.append((p.stem,m[1]))
jobs += [('spheres','https://www.math.utoronto.ca/roberth/papers/buzanohaslhoferhershkovits.pdf'),('matching','https://pages.cs.wisc.edu/~mwa/research/papers/adh13.pdf')]
out=[];blocked=set()
for n,u in jobs:
 host=urllib.request.urlparse(u).netloc if hasattr(urllib.request,'urlparse') else u.split('/')[2]
 if host in blocked:continue
 try:
  with urllib.request.urlopen(u,timeout=25) as f:b=f.read();status=f.status;final=f.url
  assert b.startswith(b'%PDF')
  p=R/'sources'/(n+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=20)
  out.append({'url':u,'final_url':final,'status':status,'file':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'text':str(p.with_suffix('.txt').relative_to(R))})
  print(n,'OK',len(b))
 except Exception as e:
  print(n,'FAIL',str(e));out.append({'url':u,'failure':str(e)})
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:blocked.add(host)
(R/'pdf-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
