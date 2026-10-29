from pathlib import Path
import hashlib,json,sys,zipfile
R=Path(__file__).resolve().parent
manifest=json.loads((R/'manifest.json').read_text())
files={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}
assert files==set(manifest)|{'manifest.json'},files^(set(manifest)|{'manifest.json'})
with zipfile.ZipFile(Path(sys.argv[1]),'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n in sorted(files):
  b=(R/n).read_bytes()
  if n in manifest:assert hashlib.sha256(b).hexdigest()==manifest[n],n
  i=zipfile.ZipInfo(n,(2026,10,29,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,b)
