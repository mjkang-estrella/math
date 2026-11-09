from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess
R=Path(__file__).resolve().parent;P=R/'primary';P.mkdir(exist_ok=True)
jobs=[('ohtsuki','https://msp.org/gtm/2002/04/gtm-2002-04-024s.pdf'),('virtual','https://arxiv.org/pdf/1409.2823'),('profinite','https://arxiv.org/pdf/1512.04620'),('farb','https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf')]
log=[]
for name,url in jobs:
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'as served; correspondence pending body inspection'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=35) as f:
   data=f.read(18000001);e.update(status=f.status,final_url=f.url)
  assert len(data)<=18000000,'bounded response exceeded'
  p=P/(name+'.pdf');p.write_bytes(data);e.update(sha256=hashlib.sha256(data).hexdigest(),size=len(data),path=str(p))
  log.append(e);(R/'provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  assert data.startswith(b'%PDF'),'not PDF; stop, no alternate route'
  subprocess.run(['pdftotext','-layout',str(p),str(P/(name+'.txt'))],check=True,timeout=30)
 except Exception as ex:e['failure']=str(ex);log.append(e) if e not in log else None
 (R/'provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 print(name,e)
