#!/usr/bin/env python3
"""Run only through the assigned helper_guard; reads upstream data, never upstream code."""
import pathlib,json,hashlib,datetime,collections,sys
R=pathlib.Path(__file__).resolve().parent;L=R.parent
EXCLUDE={'manifest.json','final-receipt.json'}
def load(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def canon(j):return hashlib.sha256(json.dumps(j,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode('utf-8')).hexdigest()
def check(p,e):
 assert p.is_file() and not p.is_symlink(),f'missing/symlink: {p}'
 assert sha(p)==e['sha256'],f'hash mismatch: {p}'
 size=e.get('bytes',e.get('size'))
 if size is not None:assert p.stat().st_size==size,f'size mismatch: {p}'
def files(d,ex):return {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-ex
def validate(n):
 d=L/n;m=load(d/'manifest.json');es=m if isinstance(m,list) else m['files']+m.get('frozen_inputs',[])
 names=[e['path'] for e in es];assert len(names)==len(set(names))
 assert set(names)==files(d,{'manifest.json','verification-receipt.json'}),f'exact upstream payload: {n}'
 for e in es:check(d/e['path'],e)
 return len(es)
def related(obj,ids):
 found=set()
 if isinstance(obj,dict):
  for k,v in obj.items():
   if k.isdigit() and int(k) in ids:found.add(int(k))
   if k in ('mathdb_id','related_mathdb_id') and isinstance(v,int) and v in ids:found.add(v)
   found|=related(v,ids)
 elif isinstance(obj,list):
  for v in obj:found|=related(v,ids)
 return found
def main():
 manifest=load(R/'manifest.json')['files'];names=[e['path'] for e in manifest]
 assert len(names)==len(set(names)) and set(names)==files(R,EXCLUDE),'exact lane payload mismatch'
 for e in manifest:check(R/e['path'],e)
 bindings=load(R/'bindings.json');bmap={x['original']:x for x in bindings};assert len(bmap)==len(bindings)
 for e in bindings:check(pathlib.Path(e['original']),e)
 I=L/'root-mathdb-breadth-intake-r445';C=L/'pi-mathdb-full-corpus-inventory-r301'
 upstream={n:validate(n) for n in ['root-mathdb-breadth-intake-r445','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']}
 direct=load(I/'bindings.json')
 for e in direct:
  p=pathlib.Path(e['original']);check(p,e);assert str(p.resolve()) in bmap
 chunks=sorted((C/'corpus').glob('*.jsonl'));assert len(chunks)==20
 for p in chunks:assert str(p.resolve()) in bmap
 for p in [I/'queue.json',I/'reserved-ids.json',I/'coverage-delta.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/disposition.json']:
  assert str(p.resolve()) in bmap
 res=load(I/'reserved-ids.json');ids=res['ids'];S=set(ids);assert len(ids)==len(S)==50
 assert S=={x['mathdb_id'] for x in load(I/'queue.json')};assert res['lane']==R.name
 cov=load(I/'coverage-delta.json');assert len(cov)==2533
 assert not S&(set(map(int,cov))|set(res['other_active_reservations'])|{372627,372628,368940,404067,364119})
 assert len(res['other_active_reservations'])==50
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert not related(load(L/'root-mathdb-accepted-exclusions-r304'/n),S)
 assert load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['mathdb_id']==364119
 actual={}
 for p in chunks:
  with p.open() as f:
   for num,line in enumerate(f,1):
    j=json.loads(line)
    if j['mathdb_id'] in S:
     assert j['mathdb_id'] not in actual
     actual[j['mathdb_id']]=(j,str(p.resolve()),num)
 assert set(actual)==S
 extracted=load(R/'assigned-records.json');assert len(extracted)==50
 for x in extracted:
  j,p,num=actual[x['record']['mathdb_id']];assert x['record']==j and x['original']==p and x['line']==num
  assert x['literal_sha256']==hashlib.sha256(j['statement'].encode()).hexdigest() and x['canonical_sha256']==canon(j)
 D=load(R/'dispositions.json');assert len(D)==50 and {x['mathdb_id'] for x in D}==S
 for d in D:
  j,p,num=actual[d['mathdb_id']]
  assert d['literal_statement']==j['statement'] and d['literal_statement_sha256']==hashlib.sha256(j['statement'].encode()).hexdigest()
  assert d['canonical_record_sha256']==canon(j) and d['canonical_statement_sha256']==canon(j['statement'])
  assert d['original_record']=={'path':p,'line':num}
  assert d['scope_quantifiers'] and d['reason_and_general_mechanism'] and d['proof_level']
  assert d['registry_level']['status']=='HOLD' and d['discovery_credit']==0 and not d['brief_proposed']
 assert load(R/'proposals.json')==[]
 for name in ['source-access.json','body-access.json','successor-access.json']:
  for e in load(R/name):
   if e['status']=='downloaded':check(R/e['file'],e)
 counts=load(R/'history-reconciliation.json')['counts'];assert counts=={'additional':9,'total':39,'next':40}
 result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(R/'manifest.json'),'verifier_sha256':sha(R/'verify.py'),'payload_files':len(names),'flat_originals':len(bindings),'upstream_manifest_entries':upstream,'corpus_chunks_checked_in_place':20,'assigned_literal_reviews':50,'baseline_reported_distinct_reviews':2533,'other_active_reservations_excluded':50,'proposals':0,'current_registry':'HOLD','mathdb_requests':0,'independent_mathematical_proof_replay':False,'counts_unchanged':counts,'dispositions':dict(collections.Counter(d['disposition'].split('_')[0] for d in D))}
 (R/'final-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(f'FAIL {type(e).__name__}: {e}',file=sys.stderr);sys.exit(1)
