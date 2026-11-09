from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
L=Path(__file__).resolve().parent
ids=['2312.08544v2','2311.05542v2','2212.12473v3','2212.11818v1','2210.02035v1','2207.10961v1','2207.08007v2','2202.07529v1']
logs=[]
for ident in ids:
 p=L/'sources'/(ident+'.pdf');url='https://arxiv.org/pdf/'+ident
 e=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=25) as r:data=r.read(8*1024*1024);e['status']=r.status
  p.write_bytes(data);e.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(data).hexdigest())
  if not data.startswith(b'%PDF'):raise ValueError('not PDF; do not retry')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=25)
  e['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as ex:e['failure']=str(ex)
 logs.append(e);print(e,flush=True)
 (L/'body-access.json').write_text(json.dumps(logs,indent=2)+'\n')
