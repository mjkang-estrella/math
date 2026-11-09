exec(open(__file__.replace('read_inputs.py','freeze.py')).read().split('roots=')[0])
def check(p,h,n):
 b=p.read_bytes(); assert (n is None or len(b)==n) and hashlib.sha256(b).hexdigest()==h,str(p)
for row in json.loads((L/'bindings.json').read_text())['files']:check(Path(row['path']),row['sha256'],row['size'])
R=P/'root-mathdb-breadth-intake-r371'
for r in [R,P/'root-mathdb-accepted-exclusions-r304',P/'root-mathdb-cayley-review-intake-r363']:
 m=json.loads((r/'manifest.json').read_text()); m=m['files'] if isinstance(m,dict) else m
 for x in m:check(r/x['path'],x['sha256'],x.get('size',x.get('bytes')))
C=P/'pi-mathdb-full-corpus-inventory-r301'; inventory=json.loads((C/'manifest.json').read_text())
chunks=[r for r in inventory['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
for r in chunks:check(C/r['path'],r['sha256'],r.get('bytes',r.get('size')))
ids=json.loads((R/'reserved-ids.json').read_text())['ids'];q=json.loads((R/'queue.json').read_text()); assert len(ids)==len(set(ids))==len(q)==50 and set(ids)=={r['mathdb_id'] for r in q}
for n in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r369']:assert not set(ids)&set(json.loads((P/n/'reserved-ids.json').read_text())['ids'])
coverage=json.loads((R/'coverage-delta.json').read_text());print('COVERAGE KEYS',list(coverage))
rows=[]
for ch in chunks:
 with (C/ch['path']).open() as f:
  for ln,line in enumerate(f,1):
   r=json.loads(line)
   if r.get('mathdb_id',r.get('id')) in ids:
    rows.append(r);print(json.dumps(r,ensure_ascii=False))
assert len(rows)==50
(L/'records.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(L/'input-checks.json').write_text(json.dumps(dict(root_manifest=True,corpus_chunks=20,r304_manifest=True,r363_manifest=True,exact_fifty=True,both_active_disjoint=True,originals=True),indent=2)+'\n')
