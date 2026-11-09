from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; P=L.parents[4]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
refs=[]
def bind(p):
 e={'path':str(p.resolve()),'sha256':h(p),'size':p.stat().st_size};refs.append(e)
 return e
names=['root-mathdb-cayley-review-intake-r363','root-mathdb-accepted-exclusions-r304','pi-mathdb-full-corpus-inventory-r301']
for n in names:
 d=L/n
 for p in sorted(d.rglob('*')):
  if p.is_file() and (n!='pi-mathdb-full-corpus-inventory-r301' or p.parent.name=='corpus' or p.name=='manifest.json'):bind(p)
for n in ['root-mathdb-breadth-intake-r361','root-mathdb-gram-intake-r359']:
 bind(L/n/'reserved-ids.json')
for p in [L.parents[0]/'AGENTS.md',Path('openai-proof-research/AGENTS.md'),Path('openai-proof-research/sources/upstream.json'),Path('openai-proof-research/sources/CONTENTS.md'),Path('openai-proof-research/sources/preprints-tree.json'),L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 if p.exists():bind(p)
(R/'bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'flat original refs, no scientific copies','files':refs},indent=2)+'\n')
print('FROZEN',len(refs),'files');print('r301 manifest', (L/names[2]/'manifest.json').read_text()[:1800]);print('corpus',list((L/names[2]/'corpus').iterdir()));print('r304 exclusions', (L/names[1]/'accepted-exclusions.json').read_text()[:800])
