"""Independent byte/assignment/hash verifier. Imports no upstream or lane builder code."""
import json,hashlib,sys,datetime,copy
from pathlib import Path
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r485';C=L/'pi-mathdb-full-corpus-inventory-r301'
def get(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def require(ok,why):
 if not ok:raise ValueError(why)
def bytecheck(p,e):
 b=p.read_bytes();require(len(b)==e.get('size',e.get('bytes')) and digest(b)==e['sha256'],'byte binding mismatch: '+str(p))
def exact(root,m,excluded):
 require(m['excluded_exact_paths']==excluded,'exclusion mismatch')
 names=[e['path'] for e in m['files']];require(len(set(names))==len(names),'duplicate manifest paths')
 require({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(excluded)==set(names),'exact payload mismatch')
 for e in m['files']:bytecheck(root/e['path'],e)
def assignments(ids,others):
 require(len(ids)==len(set(ids))==50,'own assignment cardinality')
 require(len(others)==len(set(others))==100,'other assignment cardinality')
 require(not set(ids)&set(others),'reservation overlap')
 require(not set(ids)&{372627,372628,368940,404067,364119},'forbidden ID')
def recordcheck(d,x,chunk,n):
 require(d['mathdb_id']==x['mathdb_id'],'record ID')
 require(d['literal_statement']==x['statement'],'literal statement')
 require(d['statement_utf8_sha256']==digest(x['statement'].encode('utf-8')),'literal hash')
 require(d['canonical_record_sha256']==digest(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')),'canonical hash')
 require(d['original_chunk']==str(chunk.resolve()) and d['original_line']==n,'original locator')
 require(d['accepted_credit']==0,'nonzero credit')
 require(bool(d['technical_reason']) and not d['prior_cleared'],'evidence/credit gate')
def negative(fn):
 try:fn()
 except (ValueError,AssertionError):return True
 raise ValueError('negative mutation was accepted')
def main():
 exact(O,get(O/'manifest.json'),['manifest.json','final-receipt.json'])
 exact(I,get(I/'manifest.json'),['manifest.json','verification-receipt.json'])
 for e in get(O/'initial-bindings.json'):bytecheck(Path(e['path']),e)
 flat=get(O/'flat-bindings.json');require(len({e['path'] for e in flat})==len(flat),'duplicate flat references')
 for e in flat:bytecheck(Path(e['path']),e)
 binds=get(I/'bindings.json')
 for e in binds:
  bytecheck(Path(e['original']),e);bytecheck(Path(e['copy']),e)
 im=get(C/'manifest.json');chunks=[e for e in im['files'] if e['path'].startswith('corpus/')]
 require(len(chunks)==20 and len(im['frozen_inputs'])==8,'corpus scope')
 for e in chunks+im['frozen_inputs']:bytecheck(C/e['path'],e)
 rs=get(I/'reserved-ids.json');assignments(rs['ids'],rs['other_active_reservations'])
 a=get(L/'root-mathdb-breadth-intake-r479/reserved-ids.json');b=get(L/'root-mathdb-circulant-13-prior-adjudication-r481/reserved-ids.json')
 require(a['lane']=='claude-mathdb-primary-qualified-breadth-r480' and b['lane']=='sol-mathdb-primary-qualified-breadth-r482','other reservation lanes')
 require(len(a['ids'])==len(set(a['ids']))==len(b['ids'])==len(set(b['ids']))==50,'other individual counts')
 require(not set(a['ids'])&set(b['ids']),'other reservations intersect')
 require(set(a['ids'])|set(b['ids'])==set(rs['other_active_reservations']),'other union')
 ids=set(rs['ids']);queue=get(I/'queue.json');require(len(queue)==50 and {x['mathdb_id'] for x in queue}==ids,'queue assignment')
 prior=get(I/'coverage-delta.json');require(len(prior)==3383 and not ids&{int(k) for k in prior},'baseline assignment overlap')
 require(get(I/'adjudications.json')['372627']['disposition']=='EXCLUDE_ROUTINE_PUBLISHED_SUBSUMPTION','adjudication carry')
 ds=get(O/'dispositions.json');require(len(ds)==50 and len({x['mathdb_id'] for x in ds})==50 and {x['mathdb_id'] for x in ds}==ids,'disposition scope')
 by={d['mathdb_id']:d for d in ds};found={};loc={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   x=json.loads(line)
   if x['mathdb_id'] in ids:
    require(x['mathdb_id'] not in found,'duplicate corpus ID');found[x['mathdb_id']]=x;loc[x['mathdb_id']]=(p,n);recordcheck(by[x['mathdb_id']],x,p,n)
 require(set(found)==ids,'original records incomplete')
 for e in get(O/'source-provenance.json')+get(O/'supplement-provenance.json'):
  bytecheck(Path(e['path']),e);bytecheck(Path(e['text_path']),{'size':e['text_size'],'sha256':e['text_sha256']})
 require(get(O/'proposals.json')['qualified_briefs']==[],'unexpected brief')
 require(get(O/'coverage.json')['counts_unchanged']==dict(additional=9,total=39,next=40),'count mutation')
 neg=[]
 i=ds[0]['mathdb_id'];d=by[i];x=found[i];p,n=loc[i]
 for key,val in [('literal_statement',d['literal_statement']+'!'),('statement_utf8_sha256','0'*64),('canonical_record_sha256','0'*64),('original_line',n+1),('accepted_credit',1)]:
  v=copy.deepcopy(d);v[key]=val;negative(lambda:recordcheck(v,x,p,n));neg.append(key)
 negative(lambda:assignments(rs['ids'][:-1],rs['other_active_reservations']));neg.append('missing own ID')
 bad=rs['other_active_reservations'].copy();bad[0]=rs['ids'][0];negative(lambda:assignments(rs['ids'],bad));neg.append('other reservation overlap')
 ee=copy.deepcopy(flat[0]);ee['size']+=1;negative(lambda:bytecheck(Path(ee['path']),ee));neg.append('actual size mismatch')
 ee=copy.deepcopy(flat[0]);ee['sha256']='0'*64;negative(lambda:bytecheck(Path(ee['path']),ee));neg.append('actual hash mismatch')
 mm=copy.deepcopy(get(O/'manifest.json'));mm['files'].pop();negative(lambda:exact(O,mm,['manifest.json','final-receipt.json']));neg.append('unlisted payload')
 mm=copy.deepcopy(get(O/'manifest.json'));mm['files'].append({'path':'missing-payload','size':0,'sha256':digest(b'')});negative(lambda:exact(O,mm,['manifest.json','final-receipt.json']));neg.append('missing payload')
 return dict(status='PASS',integrity_only=True,mathematics_pass=False,novelty_pass=False,own_literal_records=50,other_reservations=[50,50],baseline=3383,intake_payloads=len(get(I/'manifest.json')['files']),direct_original_copy_bindings=len(binds),flat_references=len(flat),original_corpus_chunks=20,separate_frozen_inputs=8,exact_payloads=len(get(O/'manifest.json')['files']),negative_tests_rejected=neg,accepted_credit=0,counts=dict(additional=9,total=39,next=40),manifest_sha256=digest((O/'manifest.json').read_bytes()),verified_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
try:
 receipt=main();(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
except Exception as ex:
 (O/'final-receipt.json').write_text(json.dumps(dict(status='FAIL',error=str(ex)),indent=2)+'\n');raise
