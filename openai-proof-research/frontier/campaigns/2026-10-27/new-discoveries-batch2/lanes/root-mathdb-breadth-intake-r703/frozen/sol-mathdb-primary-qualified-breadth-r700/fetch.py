from pathlib import Path
import json,hashlib,urllib.request,datetime,subprocess
D=Path(__file__).parent; events=[]
for ident,aid in [(330063,'1503.02151'),(333790,'1608.03951'),(330506,'1505.04658')]:
 url='https://arxiv.org/pdf/'+aid+'v1'; ev={'mathdb_id':ident,'url':url,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as r: b=r.read(12000000); ev['resolved_url']=r.url
  assert b.startswith(b'%PDF'); p=D/(str(ident)+'.pdf');p.write_bytes(b); ev['pdf']={'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
  events.append(ev);(D/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n')
  t=D/(str(ident)+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  b=t.read_bytes();ev['text']={'path':str(t.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)};ev['status']='bound PDF before extraction; bound derivative before reading'
 except Exception as e:
  ev['failure']=str(e);ev['status']='STOP no retry';
  if ev not in events: events.append(ev)
 (D/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n')
 print(ident,ev['status'],ev.get('failure',''))
