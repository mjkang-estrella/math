from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for lane in ['sol-median-dynamics-breadth-depth-r1','sol-median-temporal-preliminary-review-r1','sol-median-temporal-source-prior-r2','root-median-bounded-investment-r1']:
 p=L.parent/lane
 files=[f for f in p.iterdir() if f.is_file() and f.suffix in ['.md','.json','.py']]
 if lane=='sol-median-dynamics-breadth-depth-r1':files += [p/'frozen/1911.08613v2.txt',p/'frozen/1911.08613v2.pdf']
 for f in files:
  target=L/'frozen'/lane/f.relative_to(p)
  target.parent.mkdir(parents=True,exist_ok=True)
  h=sha(f);shutil.copyfile(f,target)
  assert sha(f)==h==sha(target)
  records.append({'original':str(f),'copy':str(target.relative_to(L)),'sha256':h})
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 t=L/'administrative'/name;t.parent.mkdir(exist_ok=True);shutil.copyfile(B/name,t)
(L/'freeze.json').write_text(json.dumps(records,indent=2)+'\n')
print('frozen',len(records),'scientific files; administrative snapshots only')
