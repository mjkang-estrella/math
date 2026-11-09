import urllib.request,json,hashlib,datetime
from pathlib import Path
D=Path(__file__).resolve().parent
urls={'queue':'https://arxiv.org/html/1904.04791v5','gyarfas':'https://arxiv.org/html/2207.02920v2','hovey':'https://www-users.cse.umn.edu/~tlawson/hovey/','topp52':'https://topp.openproblem.net/p52'}
out=[]
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r.update(final_url=f.url,status=f.status)
  p=D/(name+'.html');p.write_bytes(b);r.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['failure']=str(e)
 out.append(r)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
