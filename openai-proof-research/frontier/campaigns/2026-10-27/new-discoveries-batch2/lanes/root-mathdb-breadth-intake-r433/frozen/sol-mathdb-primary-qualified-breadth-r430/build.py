from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r429';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def put(n,d):(O/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
rows={int(a):[b,c,d] for a,b,c,d in (x.split('\t') for x in (O/'assessments.tsv').read_text().splitlines())}
records=load(O/'assigned-records.json');ids=load(I/'reserved-ids.json')['ids'];assert set(rows)==set(ids) and len(rows)==50
locations={}
for p in sorted((C/'corpus').glob('*.jsonl')):
 for no,line in enumerate(p.open(),1):
  d=json.loads(line)
  if d['mathdb_id'] in rows:locations[d['mathdb_id']]={'original':str(p),'line':no,'canonical_record_sha256':sha(json.dumps(d,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode())}
accepted=load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');hist=load(L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json')
def matches(obj,ids):
 if isinstance(obj,dict):
  for k,v in obj.items():
   if k in ('mathdb_id','problem_id') and isinstance(v,int) and v in ids:yield v
   elif k in ('mathdb_ids','problem_ids') and isinstance(v,list):
    for i in v:
     if isinstance(i,int) and i in ids:yield i
   else:yield from matches(v,ids)
 elif isinstance(obj,list):
  for v in obj:yield from matches(v,ids)
aj=sorted(set(matches(accepted,set(ids))));hj=sorted(set(matches(hist,set(ids))))
put('registry-check.json',{'current_registry':'HOLD','mathdb_requests':0,'reason':'Inherited MathDB 429 HOLD; no live registry clearance. Historical open/empty solutions do not prove current status.','accepted_exact_id_matches':aj,'historical_exact_id_matches':hj,'r304_scope':'39 accepted families; associations only, not a whole-history novelty audit','cayley_excluded':364119,'other_excluded':[372627,372628,368940,404067]})
D=[]
for d in records:
 i=d['mathdb_id'];status,scope,reason=rows[i];target=i in [396069,396452,396553]
 e={'mathdb_id':i,'title':d['title'],'literal_statement':d['statement'],'literal_statement_sha256':sha(d['statement'].encode()),'canonical_record_sha256':locations[i]['canonical_record_sha256'],'canonical_serialization':'whole cached record; sorted keys; ensure_ascii=False; compact separators; UTF-8','corpus_origin':locations[i],'disposition':status,'scope':scope,'mechanism_and_obstacle':reason,'statement_review':'literal full cached statement read, including quantifiers and corruption; metadata ranking not used as a technical conclusion','source_url':d['source_url'],'primary_evidence_level':'selected original report body read' if target else 'cached full statement only; source body not inspected for this record','proof_evidence_level':('successor Section 4 proofs read; no independent implementation or full dependency audit' if i==396553 else 'original report example and reduction read; foundational symplectic dependencies not audited' if i==396452 else 'source negative answer and torsion criterion exposition read; cited proofs not audited' if i==396069 else 'none inspected; no claim of proof/solution or hardness'),'registry_evidence_level':'HOLD: no current registry; zero MathDB requests','successor_evidence_level':'1210.0206v3 body inspected; v1/v2 bodies not inspected' if i==396553 else 'not investigated beyond bounded screen; no clearance','certificate':'none claimed','promoted':False,'credit':0}
 D.append(e)
put('dispositions.json',sorted(D,key=lambda d:d['mathdb_id']));put('proposals.json',[])
ex=[]
for name,lo,hi,purpose in [('4133',1030,1105,'396069 original question, negative answer, torsion criterion and scope'),('4426',380,455,'396553 original definitions, open question and computational context'),('4411',2186,2215,'396452 closed ellipsoid/ball parameter conventions'),('4411',2260,2318,'396452 reduction, strict inequalities, DB system and worked E(1,2) example'),('1210.0206v3',135,170,'396553 successor matching Definition 2'),('1210.0206v3',542,765,'396553 successor Section 4 proofs, decomposition, counterexample to complex generalization, membership test')]:
 p=O/'primary'/(name+'.txt');lines=p.read_text().splitlines();ex.append({'file':str(p.relative_to(O)),'line_start':lo,'line_end':hi,'purpose':purpose,'text':'\n'.join(lines[lo-1:hi]),'scope':'selected sections only, not whole report or full cited dependencies'})
put('excerpts.json',ex)
# A bounded replay of the source-known exceptional class and identity inclusion.
w=[1,1];m=[1,1];degree=1
assert 3*degree-1==sum(m) and degree*degree+1==sum(x*x for x in m)
assert sum(x*y for x,y in zip(w,m))/degree==2
# x+y/2<=1 for x,y>=0 implies (x+y)/2<=1, so E(1,2) subset E(2,2).
assert all(a<=b for a,b in zip([1/2,1/2],[1,1/2]))
put('calculation.json',{'executed':'source-known E(1,2) certificate: (d;m)=(1;1,1) satisfies both DB equations; weight pairing/d=2; target quadratic coefficients <= source coefficients','result':'PASS','certificate_size':'three integers (1,1,1), two weights, two coefficient comparisons','limit':'Arithmetic replay only. Lower-bound theorem is the report-cited symplectic packing theorem, not re-proved. No new hypothesis; no expensive sweep.','planned_calculations':[]})
logs=load(O/'downloads.json')+load(O/'body-downloads.json');put('sourcebytes.json',logs)
put('failures.json',{'new_failures':[x for x in logs if 'failure' in x],'guard_failures':[],'inherited_access_holds':['MathDB 429: zero requests','AIM / Kourovka / EGRES denied routes parked','AIProofWatch 403 parked','rigid-body successor 403 parked'],'blocked_routes_retried':False,'uninspected_prior_gaps':'All dispositions explicitly distinguish missing primary/proof/current registry evidence. No access gap is claimed as hardness.'})
put('provenance.json',{'freeze':'freeze-receipt.json; completed before scientific reading','flat_original_bindings':'bindings.json','baseline_reported_distinct_statement_reviews':2133,'new_literal_statement_reviews':50,'bounded_reported_union_if_parent_reconciles':2183,'whole_corpus_claim':False,'counts':{'additional':9,'total':39,'next':40},'r301_chunks':20,'corpus_copies':False,'selected_record_extract':'assigned-records.json contains exactly assigned fifty, not a corpus snapshot','primary_scope':'3 original report selected contributions, 1 successor selected proof section; no full dependencies audited','successor_versions':{'1210.0206':'arXiv page inspected: v1 2012-09-30, v2 2012-10-02, v3 2014-03-25 corrected/improved revision; only v3 proof body read; journal LMS J Comput Math 17 (2014) 565-581 DOI 10.1112/S1461157014000400'},'search_scope':'bounded public search for ring/ellipsoid/polyhedral source and cone successor; no general novelty search or clearance','network_policy':'No MathDB, Google, barred GitHub routes, ScienceDirect, browser, accounts, TLS bypass, messages/uploads/publication','canonical_hash_definition':'sha256(json.dumps(entire original normalized record,sort_keys=True,ensure_ascii=False,separators=(comma,colon)).encode(UTF-8))'})
print('built',len(D),'accepted/history matches',aj,hj)
