from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]; EX={'manifest.json','verification-receipt.json'}
files=sorted(str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in EX)
rows=[{'path':f,'size':(L/f).stat().st_size,'sha256':hashlib.sha256((L/f).read_bytes()).hexdigest()} for f in files]
(L/'manifest.json').write_text(json.dumps({'lane':L.name,'excluded':sorted(EX),'files':rows},indent=1)+'\n'); print('sealed',len(rows))
