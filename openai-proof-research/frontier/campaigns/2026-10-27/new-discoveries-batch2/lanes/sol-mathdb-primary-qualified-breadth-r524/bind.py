from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent;L=O.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r523';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return dict(path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=binding(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
flat=[]
for e in load(O/'initial-bindings.json'):flat.append(check(Path(e['path']),e))
m=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:flat.append(check(I/e['path'],e))
for e in load(I/'bindings.json'):
 for k in ['original','copy']:flat.append(check(Path(e[k]),e))
inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
for e in chunks+inv['frozen_inputs']:flat.append(check(R/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 flat.append(binding(p))
(O/'flat-bindings.json').write_text(json.dumps(list({e['path']:e for e in flat}.values()),indent=2)+'\n')
res=load(I/'reserved-ids.json');q=load(I/'queue.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json');assert len(cov)==4133
sets=[set(r['ids']) for r in active];protected=set(res['protected_ids'])
for i,s in enumerate(sets):
 assert len(s)==50 and not s&set(map(int,cov)) and not s&protected
 for t in sets[:i]:assert not s&t
assert set(res['ids'])=={r['mathdb_id'] for r in q} and len(q)==50
records=[]
for e in chunks:
 for line,b in enumerate((R/e['path']).read_bytes().splitlines(),1):
  r=json.loads(b)
  if r['mathdb_id'] not in res['ids']:continue
  records.append(dict(record=r,chunk=str((R/e['path']).resolve()),line=line,statement_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(records)==50
records.sort(key=lambda e:res['ids'].index(e['record']['mathdb_id']))
(O/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(O/'initial-verification.json').write_text(json.dumps(dict(intake_exact_payload=True,direct_pairs=len(load(I/'bindings.json')),chunks=20,frozen_inputs=8,coverage_baseline=4133,reservation_sets_disjoint=True,assigned_records=50),indent=2)+'\n')
for e in records: print(e['record']['mathdb_id'],e['record']['statement'],'\nSOURCE',e['record']['source_url'],'\n')
