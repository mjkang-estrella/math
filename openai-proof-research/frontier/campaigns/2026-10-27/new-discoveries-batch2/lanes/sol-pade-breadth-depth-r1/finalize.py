from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for r in json.loads((L/'references.json').read_text()):assert sha(Path(r['path']))==r['sha256'],r['path']
rows=[{'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']]
(L/'finalmanifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print('manifest files',len(rows))
