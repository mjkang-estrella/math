"""Check frozen source/report hashes only; no universal mathematical claim."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
d=json.loads((p/'provenance.json').read_text())
for row in d['files']:
 f=p/row['path'];assert f.stat().st_size==row['bytes'],str(f)
 assert hashlib.sha256(f.read_bytes()).hexdigest()==row['sha256'],str(f)
assert d['credit']==0
assert all(not x['counterexamples'] for x in d['checks']['networks'])
assert sum(x['triangles'] for x in d['checks']['networks'])==3613632
assert d['multicolor']['central_coefficient']==d['multicolor']['max_coefficient']==12
assert d['multicolor']['constraint_rank_on_support']==d['multicolor']['support']==17
print('PASS frozen hashes and recorded finite diagnostics; source question unresolved')
