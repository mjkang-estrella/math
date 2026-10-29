import json,hashlib,zipfile,sys
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'manifest.json').read_text())
assert {p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file()}==set(m)|{'manifest.json'}
for n,h in m.items():assert sha(R/n)==h,n
with zipfile.ZipFile(sys.argv[1],'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n in sorted(set(m)|{'manifest.json'}):
  p=R/n
  assert not any(x in n for x in ['__pycache__','.olean','.ilean','.ir.sig'])
  zi=zipfile.ZipInfo(n,(2026,10,29,0,0,0));zi.create_system=3;zi.external_attr=0o100644<<16;zi.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(zi,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
print(sha(Path(sys.argv[1])))
