from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
entries=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();entries.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps(dict(schema=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=entries,excluded=['manifest.json','final-receipt.json']),indent=2)+'\n')
print('Exact manifest sealed:',len(entries),'payload files')
