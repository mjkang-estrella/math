import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
P=Path(__file__).parent;log=[]
for id,a in [(356229,'2209.12436v1'),(357317,'2301.09846v1'),(357705,'2303.05673v1')]:
 url='https://arxiv.org/pdf/'+a
 r={'id':id,'url':url,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as f:b=f.read();r['final_url']=f.url
  assert b.startswith(b'%PDF')
  p=P/(a+'.pdf');p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  log.append(r);(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  r['text']={'path':t.name,'sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'size':t.stat().st_size}
 except Exception as e:r['failure']=str(e);r['stopped']=True;log.append(r) if r not in log else None
 (P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
