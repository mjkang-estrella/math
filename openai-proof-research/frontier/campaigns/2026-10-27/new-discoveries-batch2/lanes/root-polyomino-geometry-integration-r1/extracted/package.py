from pathlib import Path
import hashlib,json,zipfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=sorted([str(p.relative_to(L)) for p in (L/'formal').glob('*.lean')]+['run.py','replay.py','package.py','pins.json','provenance.json','SUMMARY.md','INTERFACE.md'])
manifest={f:dict(sha256=sha(L/f),bytes=(L/f).stat().st_size) for f in files}
(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(L/'source-only-component.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in files+['source-manifest.json']:
  i=zipfile.ZipInfo(f,date_time=(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o644<<16
  z.writestr(i,(L/f).read_bytes())
print(sha(L/'source-only-component.zip'))
