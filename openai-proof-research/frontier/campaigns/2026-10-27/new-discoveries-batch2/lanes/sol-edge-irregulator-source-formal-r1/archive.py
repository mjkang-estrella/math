import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
import json,hashlib,zipfile,datetime
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
files=[p for p in (R/'formal').glob('*.lean')]+[R/n for n in ['guard.py','replay.py','pins.json','dependency-hashes.json']]
files += [p for p in (R/'inputs').rglob('*') if p.is_file()]
manifest={str(p.relative_to(R)):sha(p) for p in sorted(files)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(R/'edge-irregulator-component.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files+[R/'manifest.json']):
  assert p.suffix not in ['.olean','.ilean','.ir','.o','.so']
  i=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,p.read_bytes())
(R/'archive-sha256.txt').write_text(sha(R/'edge-irregulator-component.zip')+'  edge-irregulator-component.zip\n')
# Both complete memberships and all frozen hashes, originals and private copies.
d=json.loads((R/'inputs/root-edge-irregulator-review-freeze-r1/review-freeze.json').read_text())
for base in [Path(d['source_lane']),R/'inputs/candidate']:
 assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}==set(d['files'])
 for n,h in d['files'].items(): assert sha(base/n)==h,n
(R/'freeze-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_and_copy_membership_and_all_hashes_match':True,'count':79},indent=2)+'\n')
print('Archive and 79-file after-check complete')
