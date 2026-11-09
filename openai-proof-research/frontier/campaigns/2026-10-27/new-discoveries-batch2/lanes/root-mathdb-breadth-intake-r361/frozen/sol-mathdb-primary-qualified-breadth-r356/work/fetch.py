from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess
L=Path(__file__).resolve().parents[1];(L/'sources').mkdir(exist_ok=True)
urls=[('partition-original','https://arxiv.org/pdf/1708.01957v1'),('partition-successor','https://arxiv.org/pdf/2006.15287v2'),('matrix-successor','https://arxiv.org/pdf/2502.15394v2'),('pell-original','https://arxiv.org/pdf/2301.05758v1'),('matrix-original','https://arxiv.org/pdf/2309.03772v1')]
log=[]
for name,url in urls:
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':url.rsplit('/',1)[-1]}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=25) as r:
   b=r.read(12000000);e.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),size=len(b),path='sources/'+name+'.pdf');(L/e['path']).write_bytes(b)
 except Exception as x:
  e.update(error=str(x));log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');continue
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 # Original retained and hashed before extraction.
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(L/e['path']),str(L/'work'/ (name+'.txt'))],check=True)
print(json.dumps(log,indent=2))
