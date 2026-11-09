from pathlib import Path
import json,hashlib
L=Path('frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes').resolve(); O=L/'sol-mathdb-primary-qualified-breadth-r434'
bind={}; checks=[]
def h(p):
 s=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):s.update(b)
 return s.hexdigest()
def bindone(p,sha=None,size=None):
 p=p.resolve(); a={'path':str(p),'sha256':h(p),'size':p.stat().st_size}
 assert sha is None or a['sha256']==sha,(str(p),'hash')
 assert size is None or a['size']==size,(str(p),'size')
 bind[str(p)]=a
for lane in ['root-mathdb-breadth-intake-r433','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/lane;m=d/'manifest.json';bindone(m);data=json.loads(m.read_text());entries=data if isinstance(data,list) else data['files']
 for e in entries:bindone(d/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 checks.append({'lane':lane,'entries':len(entries),'complete':True})
# Direct originals only, deliberately no transitive bindings traversal.
for e in json.loads((L/'root-mathdb-breadth-intake-r433/bindings.json').read_text()):
 bindone(Path(e['original']),e['sha256'],e.get('size',e.get('bytes')))
for p in [Path('AGENTS.md'),L.parent/'AGENTS.md',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():bindone(p)
(O/'bindings.json').write_text(json.dumps(list(bind.values()),indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps({'checks':checks,'originals':len(bind),'science_read_after_complete':True},indent=2)+'\n')
print(json.dumps(checks))
