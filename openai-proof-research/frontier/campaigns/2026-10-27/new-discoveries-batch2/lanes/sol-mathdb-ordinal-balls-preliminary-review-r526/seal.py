from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parent
# Include guard as a direct immutable administrative dependency.
p=D.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';b=p.read_bytes()
f=D/'flatbindings.json';refs=json.loads(f.read_text());refs.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()));f.write_text(json.dumps(refs,indent=2)+'\n')
excluded=['manifest.json','verification-receipt.txt'];out=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();out.append(dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'manifest.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),excluded_exact_paths=excluded,files=out),indent=2)+'\n')
print('sealed',len(out),'files')
