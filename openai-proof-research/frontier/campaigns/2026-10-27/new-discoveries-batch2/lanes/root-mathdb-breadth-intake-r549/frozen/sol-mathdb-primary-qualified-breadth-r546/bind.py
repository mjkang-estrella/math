from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r545';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
refs={}
def bind(p,e=None):
 p=Path(p);b=p.read_bytes();r={'path':str(p),'size':len(b),'sha256':h(b)}
 if e:assert r['size']==e.get('size',e.get('bytes')) and r['sha256']==e['sha256'],str(p)
 refs[str(p)]=r
 return r
def exact(root,m):
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
 for e in m['files']:bind(root/e['path'],e)
bind(I/'manifest.json');exact(I,j(I/'manifest.json'));bind(I/'verification-receipt.json')
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(e[k],e)
for e in j(L/'sol-mathdb-primary-qualified-breadth-r542/flat-bindings.json'):bind(e['path'],e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n)
for n in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md','sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(L/n)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==4583
res=j(I/'reserved-ids.json');queue=j(I/'queue.json');ids=set(res['ids']);assert len(ids)==len(queue)==50 and ids=={r['mathdb_id'] for r in queue} and res['lane']==P.name
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert len(seen)==150
for r in j(I/'active-breadth-reservations.json'):assert set(r['other_active_reservations'])==seen-set(r['ids'])
found=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:found.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement_utf8':r['statement'],'statement_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':r})
assert len(found)==50 and {r['mathdb_id'] for r in found}==ids
found.sort(key=lambda r:res['ids'].index(r['mathdb_id']))
(P/'assigned-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
(P/'initial-verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':len(refs),'intake_exact':True,'direct_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'disjoint_reserved_sets':3,'baseline':4583,'assigned':50,'scientific_acceptance':False},indent=2)+'\n')
print('BOUND AND VERIFIED',len(refs),'references; 50 records extracted; no upstream code executed')
