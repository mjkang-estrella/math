from pathlib import Path
import json,hashlib,subprocess,datetime
O=Path(__file__).resolve().parent;rows=[]
for p in sorted((O/'primary').glob('*.pdf')):
 d=p.read_bytes();rows.append(dict(path=str(p),size=len(d),sha256=hashlib.sha256(d).hexdigest(),meta=str(p.with_suffix('.meta.json'))))
f=O/'primary-bindings.json';assert not f.exists();f.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),refs=rows),indent=2)+'\n');f.chmod(0o444)
for r in rows:
 p=Path(r['path']);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
