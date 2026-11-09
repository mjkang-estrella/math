from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
records=[]
def freeze(p,d):
 h=hashlib.sha256(p.read_bytes()).hexdigest(); q=L/d/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 assert h==hashlib.sha256(q.read_bytes()).hexdigest()==hashlib.sha256(p.read_bytes()).hexdigest()
 records.append(dict(original=str(p),copy=str(q),sha256=h))
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:freeze(B/n,'administrative')
for p in [L.parent/'root-scout-r292-disposition'/'STATUS.md',L.parent/'sol-finite-certificate-primary-scout-r292'/'SCOUTING.md']:freeze(p,'frozen')
for p in (L.parent/'sol-finite-certificate-primary-scout-r292'/'sources').iterdir():
 if '1609' in p.name or 'semigroup' in p.name:freeze(p,'frozen')
(L/'bindings.json').write_text(json.dumps(records,indent=2))
for n in ['ledger.json','prior-campaign-context.json']:
 a=json.loads((L/'administrative'/n).read_text());print(n,'keys',list(a))
 print(json.dumps(a,ensure_ascii=False)[:0])
print('frozen',[(Path(x['copy']).name,x['sha256']) for x in records])
