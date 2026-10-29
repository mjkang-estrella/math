from pathlib import Path
import hashlib,json,zipfile
L=Path(__file__).resolve().parent
files=['run.py','pins.json','replay.py','SUMMARY.md','INTERFACE.md','component-context.json']+['formal/'+x for x in ['Grid.lean','Potential.lean','Bridge.lean','OriginAudit.lean']]
manifest={f:dict(sha256=hashlib.sha256((L/f).read_bytes()).hexdigest(),bytes=(L/f).stat().st_size) for f in sorted(files)}
(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
with zipfile.ZipFile(L/'source-only-component.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in sorted(files+['source-manifest.json']):
  i=zipfile.ZipInfo(f,date_time=(2026,10,29,0,0,0));i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(i,(L/f).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
