import resource,signal,json,hashlib
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(30)
b=Path(__file__).resolve().parent;p=b.parent
reg=json.loads((p/'sol-fresh-discrete-algebra-r23/registry.json').read_text())
files=[(k,Path(reg[k]['base_file'])) for k in ['openai','count','aim']]
files += [('omega OLD '+t['prefix'],Path(t['file'])) for t in reg['omega']['trees']]
records=[]
for label,f in files:
 data=f.read_bytes();j=json.loads(data)
 assert j.get('truncated') is False
 terms=['schemmel','defant','1412.3080','1506.05426','329432','329433','330740','farhi','1004.2269','319785','totient','primesquare','prime-square']
 hits=[x['path'] for x in j['tree'] if any(t in x['path'].lower() for t in terms)]
 records.append(dict(label=label,file=str(f),sha256=hashlib.sha256(data).hexdigest(),entries=len(j['tree']),truncated=False,hits=hits,coverage='OLD saved snapshot path screen only, not semantic body clearance'))
(b/'screen-output.json').write_text(json.dumps(dict(utc=datetime.now(timezone.utc).isoformat(),terms=terms,prior_registry=reg,records=records),indent=2))
print(json.dumps([dict(label=x['label'],entries=x['entries'],hits=x['hits'][:35],total_hits=len(x['hits'])) for x in records],indent=2))
