import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r637';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def entry(p):
 b=p.read_bytes();return dict(path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=entry(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
out=list(j(P/'initial-bindings.json'))
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:out.append(check(pathlib.Path(e[k]),e))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:out.append(check(C/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 out.append(entry(p))
(P/'flat-bindings.json').write_text(json.dumps(list({e['path']:e for e in out}.values()),indent=2)+'\n')
# content accessed only after bindings persisted
cov=j(I/'coverage-delta.json');assert len(cov)==6833
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids']) and r['active_hypothesis_ids']==[]
ids=set(j(I/'reserved-ids-r638.json')['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r638.json')}
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append(dict(mathdb_id=r['mathdb_id'],corpus_chunk=str(p.resolve()),corpus_line=n,record=r,canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),statement_utf8_sha256=hashlib.sha256(r['statement'].encode()).hexdigest()))
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(P/'binding-check.json').write_text(json.dumps(dict(intake_exact=True,direct_pairs=len(j(I/'bindings.json')),chunks=20,frozen_inputs=8,coverage=6833,reserved_sets=3,reserved_disjoint=True,assigned=50),indent=2)+'\n')
for r in rows:print(r['mathdb_id'],json.dumps(r['record'],ensure_ascii=False))
