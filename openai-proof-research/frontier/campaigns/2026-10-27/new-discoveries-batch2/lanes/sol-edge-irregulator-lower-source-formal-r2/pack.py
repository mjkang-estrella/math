from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).parent/'component'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[p for p in (R/'formal').glob('*.lean')]
files += [R/n for n in ['guard.py','replay.py','pins.json','dependency-hashes.json','inheritance-check.json','SUMMARY.md','FAILURES.md']]
for folder in ['inputs','failures']:
 files += [p for p in (R/folder).rglob('*') if p.is_file()]
manifest={str(p.relative_to(R)):sha(p) for p in sorted(files)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(R.parent/'edge-irregulator-lower-source-component.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files+[R/'manifest.json']):
  assert p.suffix not in ['.olean','.ilean','.ir','.o','.so']
  i=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,p.read_bytes())
p=R.parent/'edge-irregulator-lower-source-component.zip'
(R.parent/'archive-sha256.txt').write_text(sha(p)+'  '+p.name+'\n')
print(sha(p))
