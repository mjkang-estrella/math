from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r401'
def read(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(r):return json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()
def write(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
ids=read(I/'reserved-ids.json')['ids'];rows=read(O/'statements.json');notes=read(O/'assessments.json');assert set(map(int,notes))==set(ids)
r304=L/'root-mathdb-accepted-exclusions-r304';acc=read(r304/'accepted-exclusions.json');hist=read(r304/'historical-dispositions.json')
def named_ids(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['mathdb_id','mathdb_related_id'] and isinstance(v,int):out.add(v)
   elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list):out.update(a for a in v if isinstance(a,int))
   elif k=='mathdb_lookup' and isinstance(v,dict):out.update(int(a) for a in v if str(a).isdigit())
   out.update(named_ids(v))
 elif isinstance(x,list):
  for v in x:out.update(named_ids(v))
 return out
assert not set(ids)&named_ids(acc);assert not set(ids)&named_ids(hist)
result=[]
for a in rows:
 r=a['record'];i=r['mathdb_id']; d,reason=notes[str(i)]
 primary=[]
 if i in [386463,386471,386472,386474]:primary=['primary/fi.meta.json']
 if i in [386662,386672,386675]:primary=['primary/edge.meta.json']
 if i in [386811,386812]:primary=['primary/aj.meta.json']
 result.append({'mathdb_id':i,'canonical_url':r['canonical_url'],'source_url':r['source_url'],'title':r['title'],'literal_statement':r['statement'],'statement_sha256':sha(r['statement'].encode()),'canonical_record_sha256':sha(canonical(r)),'canonical_url_sha256':sha(r['canonical_url'].encode()),'canonical_serialization':'UTF-8 JSON; ensure_ascii=false, sort_keys=true, separators=comma:colon','corpus_path':a['corpus_path'],'corpus_line':a['line'],'exact_scope':r['statement'],'scope_policy':'All literal clauses and quantifiers retained; no instance, wording/domain repair, or missing-context completion counted.','disposition':d,'concrete_reason':reason,'evidence_level':'literal_statement_plus_related_primary_body' if primary else 'literal_cached_full_statement_read','related_primary_evidence':primary,'original_workshop_body_read':False,'closest_successor_resolution_proof_read':False,'related_concluding_proof_read':i in [386463,386672,386811,386812],'proof_dependency_audit':'partial' if primary else 'not_performed','source_scope_cleared':False,'dedup':{'r401_prior_1433_disjoint':True,'r400_reservations_disjoint':True,'explicit_exclusions_disjoint':True,'r304_exact_id_overlap':False,'family_or_literature_clearance':False},'registry_clearance':'HOLD_current_head_not_obtained','accepted_credit':0,'brief_qualified':False})
result.sort(key=lambda r:ids.index(r['mathdb_id']));write('dispositions.json',result)
write('proposals.json',{'lane':O.name,'proposals':[],'qualified_count':0,'accepted_credit':0,'reason':'No full-scope primary-qualified, novelty-cleared cheap mechanism. FI local example has a compound-source scope gap; other primary context is known machinery or does not supply a literal endpoint.','registry_status':'HOLD'})
write('bindings.json',{'frozen_input_references':'frozen-references.json','preflight_receipt':'preflight-receipt.json','assignment_origin':str(I/'reserved-ids.json'),'root_manifest':str(I/'manifest.json'),'root_bindings_actual_originals':str(I/'bindings.json'),'corpus_manifest':str(L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'),'r304_accepted':str(r304/'accepted-exclusions.json'),'r304_history':str(r304/'historical-dispositions.json'),'r363_disposition':str(L/'root-mathdb-cayley-review-intake-r363/disposition.json'),'primary_originals':[str(p.relative_to(O)) for p in sorted((O/'primary').glob('*.meta.json'))]})
write('provenance.json',{'generated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':O.name,'freeze_before_scientific_reading':True,'freeze_method':'Flat SHA256/size references resolved recursively from administrative JSON paths. Bytes hashed, not copied; path-like unresolved strings are not completeness or validity claims. Frozen refs are deliberately broader than actually used evidence. No history/corpus tree copied.','root_manifest_verification':'all listed file bytes checked read-only; upstream verifier not run','corpus_verification':'all twenty original chunks checked against original r301 manifest before selected-record parsing','corpus_origin':'dated third-party probxiv mirror per r301; not current MathDB validation','assignment_count':50,'previously_reviewed_count':1433,'r304_exact_id_intersection':[],'r304_family_clearance':False,'r363_rule':'No credit for a new smaller witness to a source-already-refuted assertion','counts_unchanged':{'additional':9,'total':39,'next':40},'network':{'MathDB_requests':0,'AIM_requests':0,'primary_public_HTTP_requests':3,'search_calls':2,'search_queries':5,'denied_route_retries':0,'browser_preview':0,'tls_bypass':False,'registry_head_verified':False},'evidence_limits':'Literal review of fifty; related primary bodies for nine records; no original workshop bodies; no full successor-resolution/dependency audit; no exhaustive corpus or literature coverage claim.'})
print('Built',len(result),'dispositions and zero proposals')
