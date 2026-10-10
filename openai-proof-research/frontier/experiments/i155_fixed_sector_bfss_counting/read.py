"""Supply exact text ranges, recording display attempts, not claiming comprehension."""
import sys,json,hashlib
from pathlib import Path
S=Path('frontier/sources/i155_fixed_sector_bfss_counting')
p=Path(sys.argv[1]);b=p.read_bytes();t=b.decode();a=int(sys.argv[2]);e=min(int(sys.argv[3]),len(t));part=t[a:e]
r=dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),start=a,end=e,characters=len(t),range_sha256=hashlib.sha256(part.encode()).hexdigest(),ending=part[-160:],raw_lf=t.count('\n'),splitlines=len(t.splitlines()),status='display-attempt')
log=S/'read-manifest.json';v=json.loads(log.read_text()) if log.exists() else [];v.append(r);log.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(r,ensure_ascii=False));print(part)
