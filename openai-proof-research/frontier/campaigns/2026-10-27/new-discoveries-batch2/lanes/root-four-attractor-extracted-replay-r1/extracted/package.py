from pathlib import Path
import json,hashlib,zipfile
root=Path(__file__).resolve().parent
names=['Closure.lean','Words.lean','Geometry.lean','Attractor.lean','Endpoint.lean','Audit.lean',
       'lean_guard.py','verify_pins.py','verify_sources.py','audit_verify.py','RUN','pins.json',
       'frozen-inputs.json','SUMMARY.md','PROVENANCE.md','FAILURES.md','package.py','final_verify.py']
files=[root/n for n in names]+[p for d in ['frozen','administrative'] for p in (root/d).rglob('*') if p.is_file()]
with zipfile.ZipFile(root/'source-only.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(files):
  info=zipfile.ZipInfo(p.relative_to(root).as_posix(),(2024,1,1,0,0,0));info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(info,p.read_bytes())
replay=root/'fresh-replay';replay.mkdir()
with zipfile.ZipFile(root/'source-only.zip') as z:z.extractall(replay)
print(json.dumps({'archive_sha256':hashlib.sha256((root/'source-only.zip').read_bytes()).hexdigest(),'source_files':len(files),'extracted_to':str(replay)}))
