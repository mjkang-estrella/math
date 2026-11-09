from pathlib import Path
import zipfile,json,hashlib,sys
P=Path(__file__).resolve().parent
files=json.loads((P/'package-files.json').read_text())
for n,h in files.items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
out=Path(sys.argv[1]);out.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_STORED) as z:
 for n in sorted([*files,'package-files.json']):
  i=zipfile.ZipInfo(n,date_time=(1980,1,1,0,0,0));i.create_system=3;i.external_attr=0o100644<<16
  z.writestr(i,(P/n).read_bytes())
print(hashlib.sha256(out.read_bytes()).hexdigest())
