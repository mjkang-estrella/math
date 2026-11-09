#!/usr/bin/env python3
"""Build a deterministic archive containing sources and replay metadata only."""
import hashlib,json,zipfile
from pathlib import Path
p=Path(__file__).resolve().parent.parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
c=json.loads((p/'component.json').read_text())
files=['formal/'+n+'.lean' for n in c['build_order']]
files+=['formal/run_lean.py','formal/guard.py','scripts/replay.py','scripts/build_packet.py',
        'pins.json','component.json','provenance.json','README-replay.md']
manifest={n:sha(p/n) for n in sorted(files)}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
packet=p/'packet/source-claim-component.zip'
with zipfile.ZipFile(packet,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n in sorted(files+['manifest.json']):
  i=zipfile.ZipInfo(n,date_time=(1980,1,1,0,0,0));i.create_system=3
  i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(i,(p/n).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
print(sha(packet),packet)
