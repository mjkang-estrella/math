from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent; L=R.parent
refs={}
def bind(p,h=None,s=None):
 p=p.resolve(); b=p.read_bytes(); d=hashlib.sha256(b).hexdigest()
 if h is not None: assert d==h and (s is None or len(b)==s),str(p)
 refs[str(p)]={'original':str(p),'sha256':d,'size':len(b)}
for name in ['AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md']:
 bind(Path(name))
for lane in ['root-mathdb-breadth-intake-r443','pi-mathdb-full-corpus-inventory-r301','root-mathdb-coverage-reconcile-r304','root-mathdb-breadth-intake-r363']:
 p=L/lane
 if not p.exists():
  matches=list(L.glob('*'+lane[-4:])); assert len(matches)==1; p=matches[0]
 m=p/'manifest.json';bind(m); obj=json.loads(m.read_text()); entries=obj['files'] if isinstance(obj,dict) else obj
 for e in entries: bind(p/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 if lane.endswith('r443'):
  for e in json.loads((p/'bindings.json').read_text()):bind(Path(e['original']),e['sha256'],e['size'])
(R/'bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(R/'preflight.json').write_text(json.dumps({'status':'PASS','flat_originals':len(refs),'expansion':'r443 direct originals only; complete four manifests in place; no corpus copies'},indent=2)+'\n')
print('FREEZE PASS',len(refs))
