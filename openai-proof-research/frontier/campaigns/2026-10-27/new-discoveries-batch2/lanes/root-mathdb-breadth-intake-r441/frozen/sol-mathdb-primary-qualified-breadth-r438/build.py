from pathlib import Path
import json,hashlib,collections
R=Path(__file__).resolve().parent;L=R.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
records=json.loads((R/'assigned-records.json').read_text());notes={}
for line in (R/'assessments.tsv').read_text().splitlines():
 i,status,scope,reason=line.split('\t');assert i not in notes;notes[i]=(status,scope,reason)
assert len(notes)==50 and set(notes)=={str(x['mathdb_id']) for x in records}
sections={399197:[('2014-36',230,294)],399273:[('2014-40',1380,1480)],399286:[('2014-40',2443,2458)],399287:[('2014-40',2459,2474)],399384:[('2014-51',80,155)],399385:[('2014-51',210,279)],399386:[('2014-51',210,279)],399395:[('2014-51',1560,1680)],399487:[('2015-13',2010,2040)],399488:[('2015-13',2010,2040)],399492:[('2015-13',2646,2669),('moebius',70,170),('moebius',224,463)],399541:[('mss',127,217),('mss',860,932)]}
# Only excerpts actually read are evidence; downloaded surrounding reports are not review.
for i in [399273,399384,399395]:sections.pop(i)
excerpts=[]
for i,ss in sections.items():
 for name,a,b in ss:
  p=R/'primary'/(name+'.txt');lines=p.read_text().splitlines();text='\n'.join(lines[a-1:b]);excerpts.append({'mathdb_id':i,'path':str(p.relative_to(R)),'start_line':a,'end_line':b,'text':text,'sha256':sha(text.encode())})
put('excerpts.json',excerpts)
rows=[]
for x in records:
 i=x['mathdb_id'];status,scope,reason=notes[str(i)]
 if i in [399385,399386]:status='RETIRE_SOURCE_REPORTED';reason+=' Both exact asymptotic endpoints are already printed as results 3 and 1 respectively in the original report (p.2878–2879); this is report-level retirement, not a verified complete proof.'
 if i==399286:reason+=' Original Problem 2 explicitly cites Toponogov Theorem 3.91 for monotonicity. Elementary-proof gap is not cleared, so no new monotonicity claim.'
 if i==399197:reason+=' Original report already states the conical gluing theorem and flat-half-space consequence for theta1<pi/2, with ADM convergence. Thus the example is source-reported resolved; global optimality and full gluing proof remain unreviewed.'
 rows.append({'mathdb_id':i,'canonical_url':x['canonical_url'],'literal_statement':x['statement'],'literal_statement_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'canonicalization':'entire original normalized record; sorted keys, ensure_ascii=False, compact JSON, UTF-8','source_url':x['source_url'],'disposition':status,'scope':scope,'reason':reason,'mechanism_status':'conceptual screen; no new full-scope proof or counterexample executed','decisive_check_executed':('Exact source/theorem matching and proof-section reading; see excerpts' if i in sections else 'Literal quantifier and candidate mechanism assessment only'),'decisive_check_planned':'No investment recommended without exact primary hypotheses and closest successor proof/registry review','certificate_size':'No new certificate; source dependencies not closed' if i!=399541 else 'Public corollary bridge is constant-size algebra; full MSS proof not independently replayed','formal_dependencies':'No Lean endpoint attempted; dependencies described in reason','primary_level':'selected source body/section read' if i in sections else 'cached literal statement only; primary body unreviewed','proof_level':('successor proof sections 2.1–2.3 read; classical bend-foliation and upper-construction dependencies not fully checked' if i==399492 else 'Corollary 1.5 proof and closing main-proof sections read; stability/interlacing dependencies not fully checked' if i==399541 else 'report result plus proof sketch only' if i in [399197,399385,399386] else 'no proof body reviewed'),'registry_level':'HOLD: no current public registry head/scope/chronology clearance','accepted_credit':0})
put('dispositions.json',rows);put('proposals.json',[])
sourcebytes=[]
for p in sorted((R/'primary').iterdir()):sourcebytes.append({'path':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'size':p.stat().st_size,'level':'download/extraction only unless referenced in excerpts.json'})
put('sourcebytes.json',sourcebytes)
put('failures.json',[{'kind':'helper_schema_error','preserved':'Initial inspect-schema.py run assumed manifest dict for r304 list and exited 1; no science was read. Original tool transcript contains traceback. freeze.log also records unintended import of the then-named inspect.py; renamed before successful freeze.'},{'kind':'manifest_check_failure','preserved':'freeze.log','detail':'First freeze excluded r301 frozen_inputs from entry list; assertion failed. Corrected by checking both declared lists; original failed output retained.'},{'kind':'registry_hold','detail':'No current registry clearance attempted or inferred. Inherited 403/429/challenge routes remain parked. Zero MathDB requests. No blocked-route retries.'},{'kind':'incidental_search_result','detail':'Public search returned an unassigned MathDB title/snippet (349077); no schema inspected, no technical review, substitution or coverage counted.'}])
put('registry-check.json',{'status':'HOLD','current_head':None,'scope_chronology_clearance':False,'MathDB_requests':0,'inherited_denied_routes':'AIM/Kourovka/EGRES; AIProofWatch403; rigid-body/triangle-gap successor403; unchanged/parked'})
# Reconcile administrative lists only against assigned IDs, without displaying unassigned records.
assigned={str(x['mathdb_id']) for x in records}
admin=[]
for name in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 d=json.loads((L/name).read_text());hits=[]
 def walk(v,path=''):
  if isinstance(v,dict):
   for k,w in v.items():
    if str(k) in assigned:hits.append(path+'/'+str(k))
    walk(w,path+'/'+str(k))
  elif isinstance(v,list):
   for j,w in enumerate(v):walk(w,path+'/'+str(j))
  elif isinstance(v,(str,int)) and str(v) in assigned:hits.append(path)
 walk(d);admin.append({'path':name,'assigned_id_hits':hits})
put('administrative-check.json',{'baseline_distinct_reported':2333,'assignment':50,'other_active_r436':50,'assigned_admin_hits':admin,'r363_exclusion':364119,'counts_unchanged':{'additional':9,'total':39,'next':40}})
put('provenance.json',{'flat_originals':'bindings.json','freeze_gate':'freeze-receipt.json; completed before statements extracted/read','assignment':'root-mathdb-breadth-intake-r437/reserved-ids.json and queue.json','corpus':'r301 original twenty normalized chunks read in place; no corpus copies','hash_scope':'literal UTF-8 statement and entire canonical normalized record','search':'Public search only for MSS/Moebius successors; authoritative downloaded bodies in body-downloads.json. Search snippets supplied no clearance.','review_scope':'Exactly fifty literal statements; selected sections for 10 IDs; downloads do not imply full-paper review; no full dependency closure','no_upstream_verifiers_or_receipt_writes':True})
c=collections.Counter(x['disposition'] for x in rows)
(R/'SUMMARY.md').write_text('''# r438 bounded fifty-record screen

Exactly the fifty r437 assigned IDs were read as full literal cached statements, with no substitutions. Disjoint from the 2,333 distinct reported-review baseline, the fifty active r436 reservations, and explicit exclusions. This is not a whole-corpus claim. Queue metadata was not technical evidence.

Zero proposals. No new certificate, novelty clearance, acceptance, manuscript, Lean work or costly sweep. Counts remain **9 additional / 39 total / next 40**.

Disposition counts: '''+str(dict(c))+'''. Every row preserves literal statement and canonical whole-record SHA256, exact scope, mechanism/obstacle and separate primary/proof/registry levels.

MSS (399541) is a direct public theorem: Corollary 1.5 of Interlacing Families II, with r=k and delta=epsilon, gives exactly the requested operator-norm bound. The block-vector corollary proof and main closing proof were read, not the full stability/interlacing dependency chain. Moebius (399492) is retired in the embedded, smooth isometric scope: the original report distinguishes immersions, and Schwartz arXiv:2308.12641v12 (14 October 2024) Theorem 1.1 supplies the lower bound. Sections 2.1–2.3 were read, including the T-pattern proof and geometric minimization; classical foliation and smoothing/existence dependencies are not independently closed.

The original spherical-angle problem (399286) already cites Alexandrov–Toponogov for monotonicity; the request is specifically elementary proof. No derivative sign proof was executed and no discovery claim is made. The sparse-independent-set bounds 399385/399386 are already stated as results in the report; retired at report/proof-sketch level only. Localization 399197 already has a source-reported half-space construction, but broad optimality and full gluing dependencies remain HOLD. Routine moment-pushforward, exhaustive matching, mesh quantifier-elimination and spline-nullity reformulations were not promoted as new results.

Seven PDFs and five landing pages were downloaded successfully; only selected excerpts listed in excerpts.json were read as evidence. All other primary/proof gaps remain explicit. No current public registry was cleared, so registry status is HOLD throughout. No MathDB request, blocked-source retry, browser, publication or shared-file edit occurred. Incidental unassigned search snippet was not reviewed/counted.

The freeze gate checked all four upstream manifests, r437 direct bound originals, r301 inventory including twenty original chunks using bytes fields, r304 accepted/history and r363 exclusion before scientific reading. bindings.json contains flat hashes/sizes only. Initial helper/schema and manifest-shape failures are preserved in failures.json and freeze.log; no upstream verifier was run.

Run verify.py through the mandated helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 guard python3 -B verify.py. It independently checks original hashes/sizes, all four manifests, exact assignment/disjointness, twenty chunks, literal/canonical hashes and exact payload set, exiting nonzero on mismatch. manifest.json and final-receipt.json alone are exact-path exclusions. Integrity PASS does not certify the mathematics or novelty.
''')
print('built',len(rows),dict(c))
