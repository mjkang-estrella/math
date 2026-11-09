from pathlib import Path
import hashlib,json,datetime
L=Path('openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes').resolve(); O=L/'sol-mathdb-primary-qualified-breadth-r400'
def ref(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
paths=[]
for name in ['root-mathdb-breadth-intake-r399','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 paths.extend(p for p in (L/name).rglob('*') if p.is_file())
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',Path('openai-proof-research/sources/upstream.json').resolve(),Path('openai-proof-research/sources/CONTENTS.md').resolve()]:
 if p.exists():paths.append(p)
paths.append(L/'pi-mathdb-full-corpus-inventory-r301/manifest.json')
f=O/'initial-freeze.json';assert not f.exists();f.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':[ref(p) for p in sorted(set(paths))]},indent=2)+'\n');f.chmod(0o444)
print('frozen',len(paths),'references; no scientific content emitted')
