from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,subprocess
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True)
items=[('orientation','https://lemon.cs.elte.hu/egres/open/Acyclic_orientation_with_parity_constraints','live canonical primary page'),('matroid','https://lemon.cs.elte.hu/egres/open/Bounded_degree_matroid_basis','live canonical primary page'),('orientation-successor','https://arxiv.org/pdf/2603.09475v1','arXiv2603.09475v1'),('matroid-successor','https://arxiv.org/pdf/1911.09890v1','arXiv1911.09890v1')]
log=json.loads((R/'sources.json').read_text())
for name,url,version in items:
 e={'name':name,'url':url,'version':version,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as f:
   data=f.read(12*1024*1024+1);e.update(status=f.status,final_url=f.url)
  assert len(data)<=12*1024*1024,'12MiB retrieval cap'
  e.update(size=len(data),sha256=hashlib.sha256(data).hexdigest())
  p=R/'sources'/(name+('.pdf' if data.startswith(b'%PDF') else '.html'));p.write_bytes(data);e['path']=str(p.relative_to(R))
  # Record hashes before any content extraction; challenge scan is access gate, not content acceptance.
  log.append(e);(R/'sources.json').write_text(json.dumps(log,indent=2)+'\n')
  probe=data[:150000].lower()
  if any(t in probe for t in [b'captcha',b'proof-of-work',b'checking your browser',b'cf-chl-',b'just a moment...',b'anubis']):
   e['failure']='challenge detected; no retry';continue
  e['accepted_content']=True
  if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as ex:
  e['failure']=repr(ex)
  if e not in log:log.append(e)
 (R/'sources.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
