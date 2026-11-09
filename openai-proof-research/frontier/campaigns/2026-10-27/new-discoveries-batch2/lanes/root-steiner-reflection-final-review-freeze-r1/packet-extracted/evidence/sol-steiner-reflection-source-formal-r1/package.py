import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,zipfile,signal
from pathlib import Path
signal.alarm(230)
R=Path(__file__).resolve().parent
pins=json.loads((R/'pins.json').read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
# Hash the actual imported upstream sources/oleans; this freezes the reused local cache,
# not an independent certification of the upstream build.
roots=[Path(p['path'])/'.lake/build/lib/lean' for p in pins['packages']]
roots+=[Path(pins['lean_binary']).parent.parent/'lib/lean']
imports=(R/'formal/dependencies.txt').read_text().splitlines()
own={p.stem for p in (R/'formal').glob('*.lean')};deps=[]
for m in imports:
 if m in own:continue
 matches=[r/(m.replace('.','/')+'.olean') for r in roots]
 p=next((p for p in matches if p.exists()),None);assert p,m
 deps.append({'module':m,'path':str(p),'sha256':sha(p)})
 if '.lake/build/lib/lean' in str(p):
  src=Path(str(p).replace('/.lake/build/lib/lean/','/')).with_suffix('.lean')
  if src.exists():deps.append({'module':m,'path':str(src),'sha256':sha(src)})
(R/'dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
files=[p for p in (R/'formal').glob('*.lean')]+[R/n for n in ['guard.py','replay.py','pins.json','dependency-hashes.json','REPRODUCE.md']]
manifest={str(p.relative_to(R)):sha(p) for p in sorted(files)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');files.append(R/'manifest.json')
with zipfile.ZipFile(R/'steiner-source-component.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files):
  info=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
  z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
print('Archive',sha(R/'steiner-source-component.zip'),'dependency files',len(deps))
