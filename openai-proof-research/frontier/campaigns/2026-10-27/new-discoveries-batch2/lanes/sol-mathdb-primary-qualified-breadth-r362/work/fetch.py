import urllib.request,urllib.error,json,hashlib,datetime,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[1];(R/'sources').mkdir(exist_ok=True)
log=[]
for name,url in [('mmwave','https://arxiv.org/pdf/1901.01894v1'),('subgroups','https://arxiv.org/pdf/2411.02219v1'),('trees','https://arxiv.org/pdf/0906.2183v1'),('localvol','https://arxiv.org/pdf/1001.4031v1')]:
 e=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version=url.rsplit('/',1)[-1]);log.append(e)
 try:
  with urllib.request.urlopen(url,timeout=35) as f: b=f.read(12000000);e.update(status=f.status,final_url=f.url)
  p=R/'sources'/f'{name}.pdf';p.write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b),path=str(p.relative_to(R)))
  (R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  if not b.startswith(b'%PDF'):e['failure']='non PDF; stop host';break
  subprocess.run(['pdftotext','-layout',str(p),str(R/'work'/f'{name}.txt')],check=True)
 except Exception as ex:
  e['failure']=str(ex)
  if isinstance(ex,urllib.error.HTTPError):
   b=ex.read();p=R/'sources'/f'{name}-failure.bin';p.write_bytes(b);e.update(status=ex.code,path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  break
(R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
