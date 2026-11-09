from pathlib import Path
import json,zipfile,hashlib
L=Path(__file__).resolve().parent
files=['Literal.lean','InstanceG.lean','InstanceH.lean','Audit.lean','Inventory.lean','runner.py','pins.json','RUN.md']
(L/'archive-files.json').write_text(json.dumps({s:hashlib.sha256((L/s).read_bytes()).hexdigest() for s in files},indent=2)+'\n')
with zipfile.ZipFile(L/'geometry-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for s in files+['archive-files.json']:
  info=zipfile.ZipInfo(s,(2026,10,30,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
  z.writestr(info,(L/s).read_bytes())
print('deterministic source-only archive written')
