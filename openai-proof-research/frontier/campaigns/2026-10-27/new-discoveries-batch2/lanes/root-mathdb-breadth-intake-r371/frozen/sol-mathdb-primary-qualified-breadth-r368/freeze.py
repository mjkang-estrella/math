from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent
refs=[]
def bind(p):
 if not p.is_file():return
 refs.append({'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
for n in ['root-mathdb-breadth-intake-r367','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for p in sorted((L/n).iterdir()):bind(p)
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').iterdir()):bind(p)
bind(L/'pi-mathdb-full-corpus-inventory-r301/manifest.json')
for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r365']:bind(L/n/'reserved-ids.json')
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',Path('openai-proof-research/sources/upstream.json'),Path('openai-proof-research/sources/CONTENTS.md'),Path('openai-proof-research/sources/preprints-tree.json')]:bind(p)
(R/'bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'flat immutable in-place refs; hash before scientific reading','files':refs},indent=2)+'\n')
print('Frozen',len(refs))
