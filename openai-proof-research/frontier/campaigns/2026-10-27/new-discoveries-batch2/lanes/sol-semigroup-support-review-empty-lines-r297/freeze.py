import pathlib,hashlib,json
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
items=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B.parents[3]/'AGENTS.md']
for lane,names in [('root-semigroup-r296-disposition',['STATUS.md']),('sol-semigroup-ap-review-next-lines-r296',['discovery.md','review.md','next-ratio.json','next_supports.py','support_check.py','support2_check.py','support-checks.json','support2-checks.json','SCOUTING.md','dedup.json','provenance.json']),('sol-permutation-semigroup-boundary-closure-r294',['discovery.md','apery.py','apery-result.json','symbolic.py','symbolic-result.json','line_data.py','lines-result-12.json','source-bindings.json','SCOUTING.md'])]:
 for name in names:items.append(L.parent/lane/name)
for lane in ['sol-semigroup-ap-review-next-lines-r296','sol-permutation-semigroup-boundary-closure-r294']:
 items+=list((L.parent/lane/'sources').glob('*.txt'))
for name in ['099-063-1609.01133v2.txt','100-062-1609.01133v2.pdf','055-arrangement-result.json']:
 items.append(L.parent/'sol-semigroup-ap-review-next-lines-r296'/'frozen'/name)
out=[]
(L/'frozen').mkdir(exist_ok=True)
for i,p in enumerate(items):
 if not p.exists():raise FileNotFoundError(p)
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q=L/'frozen'/('%02d-'%i+p.name);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 out.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('frozen',len(out))
