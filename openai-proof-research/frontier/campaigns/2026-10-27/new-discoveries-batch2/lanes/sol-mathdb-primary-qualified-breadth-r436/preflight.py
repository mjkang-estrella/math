from pathlib import Path
import hashlib,json
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); L=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'; O=L/'sol-mathdb-primary-qualified-breadth-r436'
def digest(p):
 h=hashlib.sha256(); n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
bindings={}; audits=[]
def bind(p,sha=None,size=None):
 p=p.resolve();h,n=digest(p)
 assert sha is None or h==sha,(str(p),'hash')
 assert size is None or n==size,(str(p),'size',n,size)
 bindings[str(p)]={'original':str(p),'sha256':h,'size':n}
for name in ['root-mathdb-breadth-intake-r435','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/name;m=d/'manifest.json';bind(m);v=json.loads(m.read_text()); rows=v if isinstance(v,list) else v['files']
 for x in rows:bind(d/x['path'],x['sha256'],x.get('size',x.get('bytes')))
 audits.append({'lane':name,'manifest_entries_validated':len(rows),'status':'PASS'})
 if name.endswith('r435'):
  for x in json.loads((d/'bindings.json').read_text()):bind(Path(x['original']),x['sha256'],x.get('size',x.get('bytes')))
for p in [R/'AGENTS.md', R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md', L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'] :bind(p)
chunks=sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl'));assert len(chunks)==20
assert all(str(p.resolve()) in bindings for p in chunks)
(O/'bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(O/'preflight.json').write_text(json.dumps({'audits':audits,'original_chunks':20,'binding_count':len(bindings),'scientific_reading_started':False},indent=2)+'\n')
print(json.dumps(audits));print('bound',len(bindings))
