from pathlib import Path
import zipfile,json,hashlib,sys
R=Path(__file__).resolve().parent
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
manifest=json.loads((R/'manifest.json').read_text())
for n,h in manifest.items():assert sha(R/n)==h,n
out=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else R.parent/'merged-source.zip'
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_STORED) as z:
 for n in sorted([*manifest,'manifest.json']):
  assert not n.endswith(('.olean','.olean.private','.olean.server','.ir','.ir.sig','.o','.so','.pyc'))
  i=zipfile.ZipInfo(n,(2026,10,30,0,0,0));i.create_system=3;i.external_attr=0o100644<<16
  z.writestr(i,(R/n).read_bytes())
print(sha(out))
