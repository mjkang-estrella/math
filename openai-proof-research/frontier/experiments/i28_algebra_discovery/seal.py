"""Seal only the assigned I28 artifacts; no Git/index operations.

The manifest is an integrity inventory, not a digital signature.
Run after all content edits; do not regenerate merely to hide verifier failures.
"""
from pathlib import Path
import datetime, hashlib, json
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i28_algebra_discovery')
E=Path('frontier/experiments/i28_algebra_discovery')
REPORT=Path('frontier/iterations/i28-algebra-discovery.md')
EXCLUDED={str(S/'artifact-manifest.json'), str(E/'verification.json')}
files=[ROOT/REPORT]
for directory in (S,E): files.extend(p for p in (ROOT/directory).rglob('*') if p.is_file())
rows=[]
for p in sorted(files):
 rel=str(p.relative_to(ROOT))
 if rel in EXCLUDED: continue
 b=p.read_bytes(); rows.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
manifest={'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
 'kind':'Unkeyed SHA-256 artifact inventory; not a signature or proof certification.',
 'excluded':sorted(EXCLUDED),'files':rows}
dest=ROOT/S/'artifact-manifest.json'
dest.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'files':len(rows),'artifact_manifest_sha256':hashlib.sha256(dest.read_bytes()).hexdigest()},indent=2))
