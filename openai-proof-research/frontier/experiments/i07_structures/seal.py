from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i07_structures';E=R/'frontier/experiments/i07_structures';manifest=S/'artifact-hashes.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
paths=[R/'frontier/iterations/i07-structures.md']+sorted(p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in str(p))
if '--verify' not in sys.argv:
 manifest.write_text(json.dumps([dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size) for p in paths],indent=2)+'\n')
records=json.loads(manifest.read_text());bad=[x['path'] for x in records if not (R/x['path']).is_file() or sha(R/x['path'])!=x['sha256']]
extra=sorted(set(str(p.relative_to(R)) for p in paths)-set(x['path'] for x in records))
up=json.loads((S/'retrieval-manifest.json').read_text());badup=[x['path'] for x in up if 'sha256' not in x or sha(S/'upstream'/x['path'])!=x['sha256']]
inputs=json.loads((S/'input-snapshot.json').read_text());changed=[x['path'] for x in inputs if sha(R/x['path'])!=x['sha256']]
result=dict(artifacts=len(records),artifact_mismatches=bad,unsealed_files=extra,upstream_files=len(up),upstream_mismatches=badup,historical_inputs_changed=changed,status='PASS' if not bad and not badup and not extra else 'FAIL')
print(json.dumps(result,indent=2));sys.exit(bool(bad or badup or extra))
