from pathlib import Path
import hashlib,json,sys,zipfile
P=Path(__file__).resolve().parent
M=json.loads((P/'manifest.json').read_text())
with zipfile.ZipFile(sys.argv[1],'w',compression=zipfile.ZIP_STORED) as z:
 for name in sorted(list(M)+['manifest.json']):
  data=(P/name).read_bytes()
  if name!='manifest.json':assert hashlib.sha256(data).hexdigest()==M[name],name
  i=zipfile.ZipInfo(name,(2026,10,29,0,0,0));i.create_system=3;i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_STORED
  z.writestr(i,data)
print(hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest())
