from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
rows={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print('final manifest entries',len(rows))
