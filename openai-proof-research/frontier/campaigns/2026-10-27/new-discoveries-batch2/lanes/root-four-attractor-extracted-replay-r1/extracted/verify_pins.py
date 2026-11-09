from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert sha(lean)==pins['lean_sha256']
mf=Path(pins['manifest_original']);assert sha(mf)==pins['manifest_sha256']
heads={}
for pin in pins['packages']:
 p=mf.parent/'.lake/packages'/pin['name']
 gd=p/'.git'
 if gd.is_file():gd=(p/gd.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(gd/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:]
  if (gd/ref).exists():head=(gd/ref).read_text().strip()
  else:head=next(x.split()[0] for x in (gd/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert head==pin['rev'],(pin['name'],head,pin['rev'])
 heads[pin['name']]=head
assert len(heads)==9
print(json.dumps({'compiler_sha256':sha(lean),'package_heads':heads},indent=2))
