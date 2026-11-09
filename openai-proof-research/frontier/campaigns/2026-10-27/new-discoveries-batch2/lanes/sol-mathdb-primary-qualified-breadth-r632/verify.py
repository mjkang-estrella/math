#!/usr/bin/env python3
"""Read-only verifier. Run under the fixed helper_guard.py; never writes files."""
from pathlib import Path
import json,hashlib,sys
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r631';R=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def chk(p,e):
 d=p.read_bytes();need(len(d)==e.get('size',e.get('bytes')),'size mismatch: '+str(p));need(sha(d)==e['sha256'],'hash mismatch: '+str(p))
def exact(root,m,excluded,negative=None):
 need(set(m['excluded_exact_paths'])==set(excluded),'exclusion mismatch')
 files=m['files'];need(len(files)==len({e['path'] for e in files}),'duplicate payload path')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 expected={e['path'] for e in files}|set(excluded)
 # Bounded negatives inject one adversarial mismatch into the exact same validator.
 if negative=='extra':actual.add('__injected_extra_file__')
 need(actual==expected or actual==expected-{'final-verification-receipt.json'},'extra/missing payload file')
 for n,e0 in enumerate(files):
  e=dict(e0)
  if n==0 and negative=='hash':e['sha256']='0'*64
  if n==0 and negative=='size':e['size']=e.get('size',e.get('bytes'))+1;e.pop('bytes',None)
  need(not Path(e['path']).is_absolute() and '..' not in Path(e['path']).parts,'unsafe manifest path')
  chk(root/e['path'],e)
def verify(negative=None):
 m=j(O/'manifest.json');exact(O,m,['manifest.json','final-verification-receipt.json'],negative)
 initial=j(O/'initial-bindings.json')
 for e in initial:chk(Path(e['path']),e)
 flat=j(O/'flat-bindings.json');need(len(flat)==len({e['path'] for e in flat}),'duplicate flat reference')
 for e in flat:chk(Path(e['path']),e)
 exact(I,j(I/'manifest.json'),['manifest.json','verification-receipt.json'])
 pairs=j(I/'bindings.json')
 for e in pairs:
  chk(Path(e['original']),e);chk(Path(e['copy']),e)
 inv=j(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]
 need(len(chunks)==20 and len(inv['frozen_inputs'])==8,'inventory counts')
 for e in chunks+inv['frozen_inputs']:chk(R/e['path'],e)
 cov=j(I/'coverage-delta.json');need(len(cov)==6683,'baseline count');covered=set(map(int,cov))
 active=j(I/'active-breadth-reservations.json');need(len(active)==3,'reservation count')
 protected={337963,338290,338366,338408,339564,364119,365437,365439,366370,368940,372627,372628,404067}
 ss=[]
 for a in active:
  s=set(a['ids']);need(len(s)==len(a['ids'])==50,'reservation uniqueness')
  need(not s&covered and not s&protected,'coverage/protected overlap')
  for t in ss:need(not s&t,'reservation overlap')
  ss.append(s)
 res=j(I/'reserved-ids-r632.json');q=j(I/'queue-r632.json');ids=set(res['ids'])
 need(res['lane']==O.name and res['coverage_baseline']==6683,'assignment authority')
 need(ids==ss[2]=={r['mathdb_id'] for r in q},'queue reservation mismatch')
 need(not res['active_hypothesis_ids'] and set(res['protected_ids'])==protected,'protected/hypothesis mismatch')
 records=j(O/'literal-records.json');ds=j(O/'dispositions.json');ps=j(O/'proposals.json')
 need(len(records)==len(ds)==50 and len(ps)<=3,'output counts')
 need({x['mathdb_id'] for x in records}=={x['mathdb_id'] for x in ds}==ids,'literal disposition coverage')
 found={}
 for e in chunks:
  p=R/e['path']
  with p.open(encoding='utf-8') as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r.get('mathdb_id') in ids:
     need(r['mathdb_id'] not in found,'duplicate original ID');found[r['mathdb_id']]=(str(p),n,r)
 need(set(found)==ids,'missing original record')
 dmap={x['mathdb_id']:x for x in ds}
 for x in records:
  i=x['mathdb_id'];p,n,r=found[i];d=dmap[i]
  h=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  need((p,n,r)==(x['chunk'],x['line'],x['record']),'record provenance mismatch')
  need(h==x['canonical_record_sha256']==d['canonical_record_sha256'],'canonical hash mismatch')
  need(d['corpus_chunk']==p and d['corpus_line']==n,'disposition coordinates')
  need(d['exact_utf8_statement']==r['statement'] and d['statement_utf8_sha256']==sha(r['statement'].encode('utf-8')),'literal statement mismatch')
  need(set(d['flags'])=={'complete_literal_statement','incomplete','definition_dependent','scope_ambiguous'},'flags missing')
  need(d['flags']['complete_literal_statement'] != d['flags']['incomplete'],'inconsistent literal completeness')
  need(len(d['quantifiers_and_scope_review'])>80 and d['accepted_credit']==0,'missing review or unauthorized credit')
 for e in j(O/'fetch-provenance.json'):
  if e.get('status')==200:chk(O/(e['name']+'.html'),e)
 for e in j(O/'derivative-bindings.json'):chk(O/e['path'],e)
 receipt=O/'final-verification-receipt.json'
 if receipt.exists():
  z=j(receipt);raw=(O/'manifest.json').read_bytes()
  need(z['manifest_sha256']==sha(raw) and z['manifest_size']==len(raw),'final manifest binding mismatch')
 return {'status':'PASS_INTEGRITY_ONLY','intake_exact_payload':True,'original_copy_pairs':len(pairs),'flat_original_references':len(flat),'original_corpus_chunks':20,'frozen_inputs':8,'baseline':6683,'reservations_pairwise_disjoint':True,'records_literal_and_canonical_checked':50,'proposals':len(ps),'math_novelty_pass':False}
if __name__=='__main__':
 try:
  negative=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
  need(negative in [None,'hash','size','extra'],'unknown negative mode')
  print(json.dumps(verify(negative),sort_keys=True))
 except Exception as e:
  print(json.dumps({'status':'FAIL','error':str(e)}));sys.exit(1)
