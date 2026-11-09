from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-new-analysis-r227'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['ATTACK.md','SCOUTING.md','SUMMARY.md','provenance.json','sourcebytes.jsonl','history-screen.json','history-supplement.json']:
 p=S/name
 if p.exists():
  q=L/'frozen'/name;q.parent.mkdir(parents=True,exist_ok=True)
  before=h(p);shutil.copyfile(p,q);assert before==h(q)==h(p)
  rows.append(dict(original=str(p),copy=str(q),sha256=before))
for p in (S/'primary').glob('*'):
 if p.is_file():
  q=L/'frozen'/'primary'/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  before=h(p);shutil.copyfile(p,q);assert before==h(q)==h(p)
  rows.append(dict(original=str(p),copy=str(q),sha256=before))
(L/'freeze.json').write_text(json.dumps(rows,indent=2))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 q=L/'administrative'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(B/name,q)
 d=q.read_text(); print(name,d if name=='AGENTS.md' else json.dumps(json.loads(d),ensure_ascii=False))
print('FROZEN',len(rows))
for name in ['ATTACK.md','SCOUTING.md','SUMMARY.md','provenance.json','history-supplement.json']:
 print('\nFILE',name);print((L/'frozen'/name).read_text()[:35000])
