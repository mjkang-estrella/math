from pathlib import Path
import json,hashlib
R=Path.cwd(); L=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'; O=L/'sol-mathdb-primary-qualified-breadth-r430'; I=L/'root-mathdb-breadth-intake-r429'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'original':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
bind={}; checks=[]
def bindone(p):
 s=sig(p);bind[str(p)]=s;return s
def check(p,e,sizekey='size'):
 s=bindone(p);assert s['sha256']==e['sha256'] and s['size']==e[sizekey],str(p)
m=load(I/'manifest.json');bindone(I/'manifest.json')
for e in m['files']:check(I/e['path'],e)
for e in load(I/'bindings.json'):check(Path(e['original']),e)
cm=load(C/'manifest.json');bindone(C/'manifest.json');print('r301 keys',cm.keys())
chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(C/e['path'],e,'bytes')
for lane,names in [('root-mathdb-accepted-exclusions-r304',['manifest.json','accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['manifest.json','disposition.json','DECISION.md','reserved-ids.json'])]:
 for name in names:bindone(L/lane/name)
for p in [R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bindone(p)
(O/'bindings.json').write_text(json.dumps(list(bind.values()),indent=2)+'\n')
(O/'freeze-receipt.json').write_text(json.dumps({'status':'PASS','r429_manifest_files':len(m['files']),'r429_direct_originals':len(load(I/'bindings.json')),'r301_original_chunks':20,'binding_count':len(bind),'recursive_expansion':False},indent=2)+'\n')
print('PASS',len(bind))
