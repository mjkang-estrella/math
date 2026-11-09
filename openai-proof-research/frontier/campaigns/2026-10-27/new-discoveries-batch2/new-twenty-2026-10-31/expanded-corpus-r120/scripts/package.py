from pathlib import Path
import zipfile,hashlib,json
D=Path(__file__).resolve().parents[1];z=D/'355525-lean-source.zip'
with zipfile.ZipFile(z,'w',compression=zipfile.ZIP_DEFLATED) as f:
 for n in ['Code.lean','Audit.lean']:
  info=zipfile.ZipInfo(n,(2026,11,3,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;f.writestr(info,(D/'lean'/n).read_bytes())
P=D/'fresh-packet';P.mkdir(exist_ok=False)
with zipfile.ZipFile(z) as f:
 assert sorted(f.namelist())==['Audit.lean','Code.lean']
 for n in f.namelist():
  assert '/' not in n and '\\' not in n
  (P/n).write_bytes(f.read(n))
print(json.dumps({'packet':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((P/'Code.lean').read_bytes()).hexdigest(),'fresh_directory':str(P)},indent=2))
