from pathlib import Path
import zipfile,hashlib,json
D=Path(__file__).resolve().parents[1];names=['Comb.lean','Audit.lean','README.txt','PROOF-373367.md','EXCLUSION-373367.md']
p=D/'373367-lean-packet.zip'
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:
 for n in names:z.write(D/'proof-packet'/n,n)
f=D/'fresh-extracted';f.mkdir(exist_ok=True)
with zipfile.ZipFile(p) as z:
 assert set(z.namelist())==set(names)
 for n in names:(f/n).write_bytes(z.read(n))
(D/'outputs/packet-manifest.json').write_text(json.dumps({'packet_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_sha256':{n:hashlib.sha256((f/n).read_bytes()).hexdigest() for n in names}},indent=2))
