"""One-time own-artifact seal. Never updates this or any prior seal."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i42_four_time_profile_r2'
E=R/'frontier/experiments/i42_four_time_profile_r2'
target=S/'artifact-seal.json'
assert not target.exists(),'Refuse to refresh a seal'
paths=[R/'frontier/reviews/i42-four-time-profile-r2.md']+list(S.rglob('*'))+list(E.rglob('*'))
files={}
for p in sorted(paths):
    if p.is_file() and p!=target:
        b=p.read_bytes();files[str(p.relative_to(R))]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
with target.open('x') as f:
    json.dump({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','scope':'I42 independent review only; prior seals untouched','files':files},f,indent=2);f.write('\n')
print(json.dumps({'sealed_files':len(files)}))
