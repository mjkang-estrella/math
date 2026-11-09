from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
jobs=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']
for lane,names in {
'root-semigroup-r297-disposition':['STATUS.md','review.md','discovery.md'],
'sol-semigroup-support-review-empty-lines-r297':['discovery.md','review.md','intersections.md','check.py','checks.json','correct_source.py','SCOUTING.md','provenance.json','failures.json'],
'sol-permutation-semigroup-boundary-closure-r294':['discovery.md','line_data.py','symbolic.py','symbolic-result.json','apery.py','apery-result.json','source-bindings.json','SCOUTING.md'],
}.items():
 jobs += [L.parent/lane/n for n in names]
jobs+=list((L.parent/'sol-semigroup-support-review-empty-lines-r297'/'sources').glob('*.txt'))
jobs+=list((L.parent/'sol-permutation-semigroup-boundary-closure-r294'/'sources').glob('*.txt'))
jobs += [L.parent/'sol-semigroup-support-review-empty-lines-r297'/'frozen'/n for n in ['38-099-063-1609.01133v2.txt','39-100-062-1609.01133v2.pdf','40-055-arrangement-result.json']]
(L/'frozen').mkdir(exist_ok=True)
rows=[]
for i,p in enumerate(jobs):
 data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); q=L/'frozen'/f'{i:02d}-{p.parent.name}-{p.name}'
 q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':h})
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),'flat files frozen and original/copy verified')
