from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
D=Path(__file__).parent; S=D/'sources';S.mkdir(exist_ok=True)
entries=[];fail=[]
for aid in ['2109.00722','2109.03129','2110.04263','2110.10515','2111.12282','2112.15551','2202.09822','2203.02457','2203.07222','2112.09396','2202.07746','2110.14716']:
 url='https://arxiv.org/pdf/'+aid;p=S/(aid+'.pdf');t=S/(aid+'.txt')
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();status=r.status;ct=r.headers.get('Content-Type')
  assert b.startswith(b'%PDF'),ct
  p.write_bytes(b);e={'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':status,'pdf':str(p.resolve()),'pdf_size':len(b),'pdf_sha256':hashlib.sha256(b).hexdigest()};entries.append(e)
  (D/'source-provenance.json').write_text(json.dumps(entries,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=15)
  e.update(text=str(t.resolve()),text_size=t.stat().st_size,text_sha256=hashlib.sha256(t.read_bytes()).hexdigest())
 except Exception as ex:fail.append({'url':url,'error':repr(ex),'retry':False})
 (D/'source-provenance.json').write_text(json.dumps(entries,indent=2)+'\n');(D/'source-access-failures.json').write_text(json.dumps(fail,indent=2)+'\n')
 print(aid,'bound' if t.exists() else 'failed',flush=True)
