#!/usr/bin/env python3
"""Optional original research capture; not used in verification. Refuses overwrite."""
from pathlib import Path
import urllib.request,datetime,json,hashlib,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i89_geometric_group_discovery/primary';S.mkdir(exist_ok=True)
urls=[('kondo','https://www.math.kyoto-u.ac.jp/preprint/2006/17kondo.pdf'),('gromov','https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/6106.pdf'),('ikn','https://arxiv.org/pdf/1210.5829')]
log=S/'responses.jsonl'
if log.exists():raise SystemExit('capture exists')
for name,url in urls:
 d={'name':name,'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=50) as r:
   b=r.read();d.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p=S/(name+'.pdf');p.write_bytes(b);d.update(local=p.relative_to(R).as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):
   out=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True).stdout;q=S/(name+'.txt');q.write_bytes(out)
   d.update(text=q.relative_to(R).as_posix(),text_sha256=hashlib.sha256(out).hexdigest())
 except Exception as e:d['error']=str(e)
 with log.open('a') as f:f.write(json.dumps(d,sort_keys=True)+'\n')
 print(name,d.get('status'),d.get('error',''))
