from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
exclude={'manifest.json','verification.log'}
files=[dict(path=str(p.relative_to(O)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in exclude]
(O/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
print(len(files),'files sealed')
