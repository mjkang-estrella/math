"""Seal completed I55 artifacts once. No old seal is refreshed."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i55_sharp_entropy_stability_r2';E=R/'frontier/experiments/i55_sharp_entropy_stability_r2'
if (S/'seal.json').exists():raise SystemExit('Refusing to overwrite the I55 seal')
files=[R/'frontier/reviews/i55-sharp-entropy-stability-r2.md']
for d in (S,E):files+=sorted(p for p in d.rglob('*') if p.is_file() and p not in {S/'seal.json',S/'verification.json'})
o={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'excluded':['self seal.json','verification.json (derived replay output)']}
(S/'seal.json').write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
print(json.dumps({'sealed_artifacts':len(files)}))
