from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r519';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def digest(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def check(p,e):
 d=digest(p);assert d['sha256']==e['sha256'] and d['size']==e.get('size',e.get('bytes')),str(p)
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
refs={}
def bind(p):
 d=digest(p);refs[str(p)]=d
# Bind before reading administrative or scientific payloads.
for n in ['manifest.json','bindings.json','queue-r522.json','reserved-ids-r522.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','active-breadth-reservations.json','routing-queue.jsonl']:bind(I/n)
assert refs[str(I/'manifest.json')]['sha256']=='f4cd9614780cc82f8cd1ef3f11b1ca07e0e6d2b6ac85f2ec97eed91cc7530071'
m=j(I/'manifest.json');names={e['path'] for e in m['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==names
for e in m['files']:check(I/e['path'],e);bind(I/e['path'])
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(Path(e[k]),e);bind(Path(e[k]))
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);bind(C/e['path'])
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n)
for pat in ['*r304*/accepted-exclusions.json','*r304*/historical-dispositions.json','*r363*/*']:
 for p in L.glob(pat):
  if p.is_file():bind(p)
for n in ['upstream.json','CONTENTS.md','preprints-tree.json']:bind(B.parents[3]/'sources'/n) if (B.parents[3]/'sources'/n).exists() else None
write('flat-bindings.json',list(refs.values()))
q=j(I/'queue-r522.json');ids={r['mathdb_id'] for r in q};cov=j(I/'coverage-delta.json');assert len(cov)==4083
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert ids==set(j(I/'reserved-ids-r522.json')['ids']) and len(ids)==50
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
rows.sort(key=lambda r:next(i for i,q0 in enumerate(q) if q0['mathdb_id']==r['mathdb_id']))
write('records.json',rows)
write('intake-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'baseline_literal_reviews':4083,'reservation_disjoint':True,'flat_reference_count':len(refs),'upstream_verifier_executed':False})
print('bound',len(refs),'references; records',len(rows));print('record keys',list(rows[0]['record']));print('context paths',*[p for p in refs if 'r304' in p or 'r363' in p],sep='\n')
