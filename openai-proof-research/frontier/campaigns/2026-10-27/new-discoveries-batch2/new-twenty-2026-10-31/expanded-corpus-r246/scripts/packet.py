import pathlib,zipfile,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'proof-packet-full.zip'
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:
 for n in ['Mobius.lean','Audit.lean','README.md']:z.write(D/'lean'/n,n)
(D/'packet-manifest.json').write_text(json.dumps({'packet':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':{n:hashlib.sha256((D/'lean'/n).read_bytes()).hexdigest() for n in ['Mobius.lean','Audit.lean','README.md']}},indent=2))
