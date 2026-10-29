import hashlib,json,re,zipfile
from pathlib import Path
root=Path(__file__).resolve().parent
mods=['Pointwise','Majorant','Tail','Density','LogConcavity','InputMoment','Profile','Result','Deficit','Baseline','Endpoint']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
pins=json.loads((root/'pins.json').read_text())
deps=[]
for mod in (root/'formal/dependencies.txt').read_text().splitlines():
 if mod in mods:continue
 rel=Path(*mod.split('.')).with_suffix('.olean')
 hits=[Path(p['path'])/'.lake/build/lib/lean'/rel for p in pins['packages']]
 hits=[p for p in hits if p.is_file()]
 if hits:
  assert len(hits)==1
  for suffix in ['', '.private', '.server']:
   artifact=Path(str(hits[0])+suffix)
   if artifact.is_file():deps.append({'path':str(artifact),'sha256':sha(artifact)})
 else:assert (Path(pins['lean_binary']).parent.parent/'lib/lean'/rel).is_file(),mod
(root/'dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
files=['guard.py','helper_guard.py','replay_guard.py','pins.json','dependency-hashes.json',
 'SUMMARY.md','frozen-before.json','verify_frozen.py','verify_inputs.py','inputs-before.json','replay.py']
files+=['formal/'+m+'.lean' for m in mods+['FullAudit']]
files+=['formal/OriginAudit.lean']
files+=['inputs/PROOF.md','inputs/review.md','inputs/arxiv-v3.html']
manifest={n:sha(root/n) for n in sorted(files)}
(root/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
with zipfile.ZipFile(root/'component-source.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n in sorted(files+['manifest.json']):
  i=zipfile.ZipInfo(n,(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,(root/n).read_bytes())
print(json.dumps({'archive':'component-source.zip','sha256':sha(root/'component-source.zip'),'members':len(files)+1,'own_prebuilt_members':0}))
