from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,v):(R/n).write_text(json.dumps(v,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
rows=json.loads((R/'assigned-records.json').read_text());ass={}
for line in (R/'assessments.tsv').read_text().splitlines():
 n,status,reason=line.split('\t',2);ass[int(n)]=(status,reason)
assert len(ass)==50 and set(ass)=={x['mathdb_id'] for x in rows}
spec={400336:[('owr2016-3',1644,1730)],400574:[('owr2016-49',1580,1650)],400758:[('owr2017-1',285,298),('equiangular',70,246)],400885:[('owr2017-14',2730,2798)],400920:[('owr2017-19',312,344),('cycles',267,296),('cycles',398,448)],400957:[('owr2017-20',1008,1050),('network',100,219),('network',475,490)],400963:[('owr2017-20',1985,2085)]}
ex=[]
for n,ss in spec.items():
 for name,a,b in ss:
  p=R/'sources'/(name+'.txt');lines=p.read_text().splitlines();ex.append({'mathdb_id':n,'file':str(p.relative_to(R)),'start_line':a,'end_line':b,'text':'\n'.join(lines[a-1:b]),'scope':'selected source section; not complete paper or dependency closure'})
put('excerpts.json',ex)
out=[]
for x in rows:
 n=x['mathdb_id'];st,reason=ass[n];primary='selected source body/section read' if n in spec else 'literal assigned record only; primary body not read'
 proof={400574:'source Theorem 2 plus proof outline read; cited proof dependencies not audited',400758:'Corollary 1.3 and complete main Theorem 1.2 proof read; Theorems 2.1/2.2 dependencies not audited',400920:'Theorem 2.1 and concluding recurrence/lower-bound proof read; partition and cycle-elimination dependencies not audited',400957:'Propositions 1/2 and cardinality-reduction proof read; Appendix D algorithm discussion; Caratheodory dependency not audited',400963:'source Theorem 2 and numerical Example 4 read; cited Prop 3.3 proof not retrieved'}.get(n,'no concluding proof-body review')
 out.append({'mathdb_id':n,'title':x['title'],'canonical_url':x['canonical_url'],'literal_statement':x['statement'],'literal_statement_sha256':sha(x['statement'].encode()),'canonical_record_sha256':sha(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'source_url':x['source_url'],'disposition':st,'scope_reason':reason,'quantifier_review':'Full literal statement read; assessment addresses its universal/existential and asymptotic scope, not tags. '+reason,'mechanism_and_obstacle':reason,'route_status':'retired from discovery routing' if st.startswith('RETIRE') else 'parked at bounded statement screen; source/prior qualification HOLD','primary_level':primary,'proof_level':proof,'registry_level':'HOLD: current registry head/proof bodies not obtained; no live-prior clearance','source_sections':[e for e in ex if e['mathdb_id']==n],'bounded_check_executed':'literal-scope comparison and analytic mechanism assessment; source/proof-section comparisons where explicitly listed; no finite computational sweep','certificate_size':'none produced; no full-scope certificate established','formal_dependencies':'not scoped for implementation; no Lean work authorized or performed','strongest_objection':reason,'accepted_credit':0,'novelty_cleared':False,'dependency_closure':False})
put('dispositions.json',out);put('proposals.json',[])
files=[]
for p in sorted((R/'sources').iterdir()):
 b=p.read_bytes();files.append({'path':str(p.relative_to(R)),'sha256':sha(b),'size':len(b),'level':'downloaded bytes' if p.suffix!='.txt' else 'text extraction; read sections enumerated in excerpts.json'})
put('sourcebytes.json',files)
put('registry-check.json',{'status':'HOLD','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'current_heads_obtained':False,'reason':'No current proof-registry snapshot/head obtained under assigned route restrictions. No promotion or significant new proof investment. Public mathematical papers are evidence of known scope, not registry clearance.','inherited_parked_routes':['MathDB zero requests due inherited 429 HOLD','AIM/Kourovka/EGRES denied','AIProofWatch 403','rigid-body/triangle-gap successor 403'],'barred_routes_used':False})
put('failures.json',[{'kind':'local manifest-check failure','file':'freeze.log','reason':'Initial r301 exact-set check omitted separately listed frozen_inputs. Failed before scientific read; corrected to check files+frozen_inputs, passed freeze-2.log.'},{'kind':'current-registry access gap','status':'HOLD','retry':False},{'kind':'incidental source context','reason':'A bounded source line selection in owr2017-19 showed adjacent Tverberg material rather than target section. Not a MathDB record display, no disposition/coverage credit; target section subsequently located at lines312-344.'}]+[e for name in ['downloads.json','body-downloads.json'] for e in json.loads((R/name).read_text()) if 'error' in e])
# Read administrative histories in full, emitting only assigned-ID matches.
ids={str(x['mathdb_id']) for x in rows};matches=[]
def scan(o,where):
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ('mathdb_id','mathdb_ids'):
    vs=v if isinstance(v,list) else [v]
    for n in vs:
     if str(n) in ids:matches.append({'mathdb_id':n,'file':where,'entry':o})
   scan(v,where)
 elif isinstance(o,list):
  for v in o:scan(v,where)
for fn in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/fn;scan(json.loads(p.read_text()),str(p))
put('administrative-check.json',{'assigned_matches':matches,'baseline_distinct_reported_reviews':2433,'counts_unchanged':{'additional':9,'total':39,'next':40},'r363_excluded_id':364119,'r363_scope':'source-known avoidance-count counterexample excluded; not reassigned','history_evidence_level':'administrative exclusions only, not technical review'})
# Bind the guard and applicable root guidance without altering any upstream files.
refs=json.loads((R/'bindings.json').read_text());seen={e['path'] for e in refs}
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parents[4]/'AGENTS.md']:
 if p.exists() and str(p.resolve()) not in seen:
  b=p.read_bytes();refs.append({'path':str(p.resolve()),'sha256':sha(b),'size':len(b)})
put('bindings.json',refs)
put('provenance.json',{'style':'flat in-place original references, no corpus copies, no recursive binding expansion','bindings':'bindings.json','corpus':'pi-mathdb-full-corpus-inventory-r301/corpus: all twenty original chunks, bytes field checked','assignment':'root-mathdb-breadth-intake-r441/reserved-ids.json + queue.json','download_logs':['downloads.json','body-downloads.json'],'source_versions':{'equiangular':'arXiv:1907.12466v5, 28 Feb 2022; Annals 194 (2021) 729-743 public successor','cycles':'arXiv:1512.00358v2 [cs.CG], header 8 Jun 2016; body title date October 20 2018; STOC2016 precursor cited in primary report','network':'arXiv:1709.00707 PDF unversioned endpoint, body dated June12 2017; journal 2018; exact fetched bytes pinned here'},'primary_versions':'OWR2016/3,49 and OWR2017/1,14,19,20 published reports; only listed sections read','source_internal_comparisons':{'400336':'S=G Theorem1 is restricted, cannot solve general S','400574':'Theorem2 already characterizes solution group; outline addresses exact Laurent tower','400885':'Example3 continuous moment/Stieltjes class already known, discrete Q1 remains separate','400920':'same report already presents near N^1.5 result','400957':'primary distinguishes practical fixed-d problem from algorithm for infinite union','400963':'Theorem2 and Example4 answer own Question1'}})
