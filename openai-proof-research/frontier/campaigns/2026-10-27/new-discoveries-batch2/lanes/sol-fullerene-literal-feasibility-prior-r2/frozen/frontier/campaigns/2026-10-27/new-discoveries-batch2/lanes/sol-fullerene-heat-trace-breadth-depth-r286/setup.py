from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for rel in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/rel;q=L/'administrative'/rel;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 records.append(dict(original=str(p),copy=str(q),sha256=sha(p),kind='administrative snapshot'))
P=L.parent/'sol-primary-diverse-certifiable-scout-r285'
for rel in ['SCOUTING.md','bindings.jsonl','candidates.json','semantic-hits.json','duplicate-filter-bindings.json']:
 p=P/rel;q=L/'frozen'/rel;q.parent.mkdir(exist_ok=True);h=sha(p);shutil.copyfile(p,q);assert h==sha(q)==sha(p)
 records.append(dict(original=str(p),copy=str(q),sha256=h,kind='scientific frozen'))
(L/'freeze.json').write_text(json.dumps(records,indent=2))
print((L/'frozen/SCOUTING.md').read_text())
print((L/'frozen/bindings.jsonl').read_text())
