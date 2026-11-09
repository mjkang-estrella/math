from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
hist=json.loads((L/'history-bindings.json').read_text())
for i,row in enumerate(hist):
 p=Path(row['original']);assert sha(p)==row['sha256'],str(p)
 q=L/'history-flat'/('%04d-'%i+p.parent.name+'-'+p.name)
 q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes());assert sha(q)==row['sha256']==sha(p)
 row['copy']=str(q.relative_to(L))
(L/'history-bindings.json').write_text(json.dumps(hist,indent=2)+'\n')
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:
  rows.append(dict(file=str(p.relative_to(L)),sha256=sha(p),size=p.stat().st_size))
(L/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print('manifest files',len(rows),'flat historical bindings',len(hist))
