from pathlib import Path
import urllib.request,subprocess,json,hashlib,concurrent.futures
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-structural-discovery-r142');D=R/'packet/private/primary';D.mkdir(exist_ok=True)
items=[('duval-relative','https://arxiv.org/pdf/math/9809195'),('bcr-distractions','https://arxiv.org/pdf/math/0308004')]
def get(item):
 name,url=item
 try:
  with urllib.request.urlopen(url,timeout=40) as f:b=f.read()
  assert b.startswith(b'%PDF')
  p=D/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(D/(name+'.txt'))],check=True)
  return dict(name=name,url=url,sha256=hashlib.sha256(b).hexdigest(),size=len(b),status='ok')
 except Exception as e:return dict(name=name,url=url,status=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:out=list(p.map(get,items))
(D/'acquisition-second.json').write_text(json.dumps(out,indent=2)); print(json.dumps(out,indent=2))
