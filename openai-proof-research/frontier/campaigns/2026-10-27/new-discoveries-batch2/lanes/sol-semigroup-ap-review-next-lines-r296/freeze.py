import pathlib, hashlib, json, shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
items=[B/'AGENTS.md',B/'NEXT.md',B/'RESULTS.md',B/'ledger.json',B/'prior-campaign-context.json',L.parent/'root-semigroup-r295-disposition/STATUS.md']
for lane in ['sol-permutation-semigroup-universal-lines-r295','sol-permutation-semigroup-boundary-closure-r294']:
 p=L.parent/lane
 items += [x for x in p.iterdir() if x.is_file()]
 items += [x for x in (p/'sources').iterdir() if x.is_file()]
items += [L.parent/'sol-permutation-semigroup-universal-lines-r295/frozen/063-1609.01133v2.txt',L.parent/'sol-permutation-semigroup-universal-lines-r295/frozen/062-1609.01133v2.pdf']
(L/'frozen').mkdir(exist_ok=True)
rows=[]
for i,p in enumerate(items):
 data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); q=L/'frozen'/f'{i:03d}-{p.name}'
 q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Frozen and reverified',len(rows),'flat bindings')
