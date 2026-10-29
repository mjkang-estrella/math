import hashlib,json,zipfile
from pathlib import Path
r=Path(__file__).parent
names=['SUMMARY.md','guard.py','replay_guard.py','replay.py','pins.json','dependency-hashes.json','inherited-identity.json','audit-inventory.json']
names += [str(p.relative_to(r)) for p in (r/'formal').glob('*.lean')]
names += [str(p.relative_to(r)) for p in (r/'inputs').rglob('*') if p.is_file()]
names += [str(p.relative_to(r)) for p in (r/'probes').rglob('*') if p.is_file() and p.suffix in {'.lean','.log','.json'}]
# Include successful audit/build/resource evidence, not any compiled artifact.
names += [str(p.relative_to(r)) for p in (r/'evidence').glob('*') if p.is_file()]
names=sorted(set(names)); assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in names)
manifest={n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in names}
(r/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
with zipfile.ZipFile(r/'upper-witness-component.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n in sorted(names+['manifest.json']):
  zi=zipfile.ZipInfo(n,(2026,10,29,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o100644<<16
  z.writestr(zi,(r/n).read_bytes())
h=hashlib.sha256((r/'upper-witness-component.zip').read_bytes()).hexdigest()
(r/'archive-sha256.txt').write_text(h+'  upper-witness-component.zip\n');print(h)
