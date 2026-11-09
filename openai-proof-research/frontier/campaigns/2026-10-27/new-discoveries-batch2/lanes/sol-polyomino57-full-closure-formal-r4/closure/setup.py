import hashlib,json,zipfile,shutil,resource,signal,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,30));signal.alarm(40)
L=Path(__file__).resolve().parent;S=L.parent/'sol-polyomino57-efficient-certificate-r2'
(L/'formal').mkdir(exist_ok=True)
inputs={}
for name,want in [('source-only-certificate.zip','da1721fa1a693fe48f8669a3e8ec4c848f3f9acb05d430029cf26c40c1a76a5f'),('source-only-sorted-addon.zip','8e1f36257c1259f1688dcc4cc6e563719ebc3878679c4bd5784a8a6b1a9fb9ad')]:
 p=S/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==want
 inputs[name]=want
 with zipfile.ZipFile(p) as z:
  assert not any(n.endswith(('.olean','.ilean','.o','.so')) for n in z.namelist())
  for n in z.namelist():
   if n.endswith('.lean') and '/formal/' in '/'+n:
    dst=L/'formal'/Path(n).name
    data=z.read(n)
    if dst.exists():assert dst.read_bytes()==data
    else:dst.write_bytes(data)
for n in ['pins.json','run.py']:shutil.copyfile(S/n,L/n)
(L/'input-hashes.json').write_text(json.dumps(inputs,indent=2)+'\n')
(L/'immutable-copy-hashes.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((L/'formal').glob('*.lean'))},indent=2)+'\n')
