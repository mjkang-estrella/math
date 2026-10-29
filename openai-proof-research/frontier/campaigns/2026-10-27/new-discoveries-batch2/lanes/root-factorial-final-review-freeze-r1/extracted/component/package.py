import hashlib,json,zipfile
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
pins=json.loads((R/'pins.json').read_text())
actual=set()
for mod in (R/'formal/dependencies.txt').read_text().splitlines():
 if mod=='FactorialProduct':continue
 rel=Path(*mod.split('.')).with_suffix('.olean')
 hits=[Path(p['path'])/'.lake/build/lib/lean'/rel for p in pins['packages']]
 hits=[p for p in hits if p.is_file()]
 if hits:
  assert len(hits)==1
  for suffix in ['', '.private', '.server']:
   p=Path(str(hits[0])+suffix)
   if p.is_file():actual.add(p)
 else:assert (Path(pins['lean_binary']).parent.parent/'lib/lean'/rel).is_file(),mod
(R/'dependency-hashes.json').write_text(json.dumps([{'path':str(p),'sha256':sha(p)} for p in sorted(actual)],indent=2)+'\n')
files=['formal/FactorialProduct.lean','formal/FullAudit.lean','guard.py','pins.json',
 'verify.py','replay.py','package.py','setup.py','frozen-before.json',
 'dependency-hashes.json','SUMMARY.md','PROVENANCE.md','FAILURES.md','README.md']
files += [str(p.relative_to(R)) for p in sorted((R/'inputs').iterdir())]
files += [str(p.relative_to(R)) for p in sorted((R/'logs').glob('*failed*'))]
manifest={n:sha(R/n) for n in sorted(files)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
def build():
 import io
 b=io.BytesIO()
 with zipfile.ZipFile(b,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for n in sorted(files+['manifest.json']):
   i=zipfile.ZipInfo(n,(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
   z.writestr(i,(R/n).read_bytes())
 return b.getvalue()
a=build();assert a==build();(R/'source-only.zip').write_bytes(a)
(R/'archive-receipt.json').write_text(json.dumps({'archive_sha256':hashlib.sha256(a).hexdigest(),
 'manifest_sha256':sha(R/'manifest.json'),'deterministic_two_builds_identical':True,
 'source_only':True,'payload_entries':len(files)},indent=2)+'\n')
print((R/'archive-receipt.json').read_text())
