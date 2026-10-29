import json,re,hashlib,shutil
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent.parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
paths=[B/'lanes/sol-factorial-product-full-final-review-r1/fresh-coverage.json',B/'lanes/sol-fresh-source-discovery-r119/registry-coverage.json',B/'lanes/sol-fresh-source-discovery-r119/sources/omega-delta.json',B/'lanes/sol-fresh-source-discovery-r119/sources/omega-head.json',B/'lanes/sol-fresh-source-discovery-r119/sources/openai-head.json']
receipts=[]
for i,p in enumerate(paths):
 data=p.read_bytes();dest=L/'sources'/('registry-%02d.json'%i);dest.write_bytes(data);receipts.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=sha(data),bytes=len(data)))
 j=json.loads(data)
 if i==0:
  print('factorial coverage top keys',list(j));print('bounded scalar fields',{k:v for k,v in j.items() if not isinstance(v,(list,dict))});print('first parent chain length',len(j.get('first_parent_chain',[])))
 if i==2:
  rx=re.compile('TI.?augment|Haynes|independent.?dominat',re.I)
  print('r119 comparison',j.get('total_commits'),len(j.get('commits',[])),len(j.get('files',[])))
  print('target filename matches',[f['filename'] for f in j.get('files',[]) if rx.search(f['filename'])])
dump('registry-receipts.json',receipts)
p=R/'frontier/campaigns/2026-10-25/twenty-proof-discrete-lane/sources/graph-theory.json'
j=json.loads(p.read_bytes());items=j.get('items',[]);rx=re.compile(r'TI-augment|Augmenting graphs|total dominating set and an independent',re.I)
hits=[x for x in items if rx.search(json.dumps(x))]
dump('historical-catalogue-target.json',dict(path=str(p),sha256=sha(p.read_bytes()),items=len(items),target_hits=hits,scope='Only the matched single-line graph catalogue parsed; not an original-proof clearance.'))
print('catalogue target hits',len(hits))
# Separate compact reconciliation avoids reprinting long copied reviews or corpus bodies.
rows=[]
for n in ['ledger.json','prior-campaign-context.json']:
 j=json.loads((B/n).read_bytes())
 for key in ['excluded','held_candidates','candidates']:
  vals=j.get(key,[])
  if isinstance(vals,dict):vals=[dict(id=k,content=v) for k,v in vals.items()]
  for x in vals:
   if isinstance(x,dict):rows.append(dict(file=n,category=key,id=x.get('id',x.get('mathdb_id',x.get('source_target'))),path=x.get('lane',x.get('path')),reason=x.get('reason',x.get('status')),target_overlap=bool(rx.search(json.dumps(x)))))
dump('context-reconciliation.json',rows);print('context records',len(rows),'target overlaps',sum(x['target_overlap'] for x in rows))
dump('registry-coverage.json',dict(status='NO_CURRENT_PRIOR_CLEARANCE',last_observed_omega='a7769c386bd6072628a21cf4680756d2a49bf221',last_observed_openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',observation_time='2026-10-29T22:21:24Z (reused r119 receipts; not a new HEAD request)',factorial_review_head='c3e8754b8890ac2c4da1d45d41cf530fac36d85d',limits='Factorial fresh coverage is target-specific, not TI semantic clearance. Renyi fixed closure is not a TI clearance. r119 uncapped 47 commits/207 paths is structurally bounded but no TI body semantics or baseline all-body coverage. No additional network registry refresh; no full proof exists here.'))
