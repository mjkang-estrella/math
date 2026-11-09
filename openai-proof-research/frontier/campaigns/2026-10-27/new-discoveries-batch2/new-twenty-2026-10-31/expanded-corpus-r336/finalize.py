import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,datetime,re,sys
P=pathlib.Path(__file__).resolve().parent; start=time.monotonic()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d): (P/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
r=json.loads((P/'reservation.json').read_text()); ids=r['ids']; prov=json.loads((P/'literal-provenance.json').read_text()); assert len(ids)==20
for i in ids:
 d=prov[str(i)];raw=(P/f'{i}.raw.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==d['raw_sha256'] and json.loads(raw)==d['record']
 d['statement_utf8_sha256']=sha(d['record']['statement'].encode());d['parsed_hash_serialization']='UTF-8 json.dumps(ensure_ascii=False,sort_keys=True,separators=(comma,colon)), no final newline'
save('literal-provenance.json',prov);save('full-records.json',{str(i):prov[str(i)]['record'] for i in ids})
http=[json.loads(x) for x in (P/'http.jsonl').read_text().splitlines()]
meta={
358344:('PARKED_cardinality_gap','Conjecture 2.6; Lemma 2.1 and Theorem 2.3 proof context','Complement injection targets C, not B; metadata refutation concerns A empty. Need injection A to B or true count violation.'),
358557:('EXCLUDED_complete_classical_bridge','Conjecture 1, (30), norm/trace definitions; boundary lemma and actual proof','Full modulo-p proof in ATTEMPTS; direct boundary Chevalley-Warning reduction. Journal body and full version comparison incomplete.'),
358589:('PARKED_maximality_gap','Conjecture 1 and adjacent Proposition 14/17 context','Need universal maximal length within same Rabc directive language, including standard-conjugate fallback.'),
358590:('PARKED_generic_rank_gap','Conjecture 4.13 and matroid-union proof opening','Need generic nonzero Jacobian minors for every sparse hypergraph, with degree/field conventions recovered.'),
358615:('PARKED_full_analytic_endpoint','Conjecture 1.2 and condensation discussion','Need exact interval extremality and diameter-free estimate; affine invariance does not compress arbitrary sets.'),
358638:('PARKED_all_loop_orders','Conjectures 1 and 2, loop-counterterm discussion','Need loop-level compactification/counterterm invariance; tree-level theorem insufficient.'),
358642:('PARKED_metric_scope','Conjecture 1, Section 5.2 text and figure caption','Arbitrary-metric transport would be excluded domain correction; no intended intrinsic-metric endpoint.'),
358986:('PARKED_three_permutation_gap','Conjecture 1 and closing comparison discussion','Need a three-order permutation realizer for every comparability graph with representation at most two.'),
359109:('PARKED_refined_scope','Introduction and selected S4 path-morphism proof context','Unrefined path counterexamples do not supply longest-element paths passing prescribed source and sink.'),
359130:('PARKED_general_necessity','Section 4 definitions/functional formula; Conjecture 4.31 in preprint and 2025 journal','Need collision or outside-class permutation for all-prime necessity; period and two affine classes only proven.'),
359149:('PARKED_extremal_certificate','Conjecture 6.3 and surrounding search report','Need source spectral diameter-maximal equality certificate and girth analysis; maximum-diameter substitution disallowed.'),
359310:('PARKED_degenerate_vertex_links','Conjecture 1 and condition-removal discussion','Need remove no-collinear-triples condition with convex faces/no partially-flat vertices. Spherical refutation is different.'),
359338:('PARKED_sigmaQ_obstruction','Conjecture 3.9, conditional proof and Problem 3.10','Need unconditional Delta-space obstruction for sigma(Q); earlier claimed proof remains unverified here.'),
359353:('HOLD_primary_definition_unread','Introductory conjecture discussion only','Need exact action/adjacency normalization and density-to-action/partition converse; body not reviewed.'),
359379:('HOLD_primary_unread','Literal record only; source fetched, no target-body review','Need covariance parameterization and admissibility; neither generic-identifiability proof nor equal-image pair supplied.'),
359502:('DUPLICATE_unresolved_historical_family','Conjecture 1.1 attribution and ordinal-sum theorem context','Same endpoint as completed historical 357510; general d-complete cactus relations still unproved, no duplicate credit.'),
359585:('EXCLUDED_complete_source_construction_bridge','Conjecture 6.1, Proposition 5.20 proof; 2005 bicircular definitions and looped-tree counting proof; small-sum CF Corollary 2','Full rooted-state reduction in ATTEMPTS transfers existing Euclidean concise-count construction. No qualified novelty/significance or journal-proof clearance.'),
359588:('PARKED_integer_realization_gap','Section 6.7 and Conjecture 6.4','Need every sufficiently large count on rational general-position point sets; abstract triangulation realizability is insufficient.'),
359590:('HOLD_literal_missing_theorem','Literal damaged theorem reference; source available','Need identify exact theorem, dimension and tiles before a full simply connected extension can even be stated; no repair counted.'),
359599:('PUBLIC_refutation_lead','Primary introduction, embedded pseudo-triangulation definitions','Literal and source report existing refutation; older full counterexample proof not reconstructed, no new result.')}
results={}
for i in ids:
 d=prov[str(i)]; record=d['record'];status,depth,gap=meta[i]
 src=[x for x in http if record['source_url'].split('/')[-1] in x['url']]
 results[str(i)]=dict(mathdb_id=i,title=record['title'],literal_statement=record['statement'],literal_provenance={k:v for k,v in d.items() if k!='record'},full_parsed_record=record,outcome=status,credit=0,review_depth=depth,ordinary_attempts='ATTEMPTS.md',precise_gap_or_exclusion=gap,sources=src,gates=dict(scope='literal preserved; see ATTEMPTS for definition/fidelity limits',source='selected primary passages only; full qualification NOT claimed',prior='completed allowlist ID/source-family screen and bounded current public routing screen; no global absence claim',subsumption='complete classical/source bridge detailed' if i in (358557,359585) else 'not cleared; specific limitation in ATTEMPTS',novelty='NOT a qualified new discovery',significance='excluded complete routine bridge' if i in (358557,359585) else 'not established for a complete new endpoint',formal='none; no Lean execution'),pi=dict(dispatched=False,dormant_plan=None,reason='No qualified new ordinary endpoint survived all eligibility/source gates'))
assert set(results)==set(map(str,ids)) and len(results)==20;save('results.json',results)
# Retain compact linked completed metadata, without duplicating full historical result files.
old=json.loads((P/'history-hits.json').read_text()); filtered=[]
needles=[str(i) for i in ids]+[x['source_url'].split('/')[-1] for x in r['rows']]+['d-complete','Zagreb']
def leaves(o):
 if isinstance(o,dict):
  if 'mathdb_id' in o: yield o
  else:
   for v in o.values():yield from leaves(v)
 elif isinstance(o,list):
  for v in o:yield from leaves(v)
for h in old:
 for v in leaves(json.loads(h['text']) if 'text' in h else h['record']):
  text=json.dumps(v,ensure_ascii=False)
  match=[s for s in needles if s.lower() in text.lower()]
  if match:filtered.append(dict(path=h['path'],matched=match,record=v))
save('history-hits.json',filtered)
readinv=[]
for x in http:
 if x.get('file'):
  n=x['file']; txt=P/(n+'.txt')
  readinv.append(dict(url=x['url'],file=n,bytes=x['bytes'],sha256=x['sha256'],download_complete=x['complete'],text_extracted=txt.exists(),depth='See results and ATTEMPTS for actual selected passages; download/extraction alone is not reading or proof clearance'))
save('source-read-inventory.json',readinv)
b=(P/'reservation.json').read_bytes(); expected=(P/'reservation.sha256').read_text().strip();assert sha(b)==expected==json.loads((P/'reservation-before.json').read_text())['sha256'];save('reservation-after.json',dict(ids=ids,count=20,sha256=sha(b),expected=expected,verified=True))
save('search-inventory.json',dict(date='2026-11-06',tool='managed web search, public read only; no browser',queries=['Hermitian affine Frobenius intersections Aguglia Csajbok Giuzzi','Reversed Dickson polynomials Fang Fernando Wu journal and conjecture','bicircular concise basis counting continued fractions Larcher','Chevalley Warning boundary highest homogeneous parts','LeanPool public proof registry'],primary_leads=['https://plclark.github.io/PeteLClark/Research/Chevalley_Warning_on_the_Boundary.pdf','https://arxiv.org/abs/2210.14095','https://msp.org/involve/2025/18-2/p06.xhtml','https://arxiv.org/abs/2401.09723'],limits='Search snippets supplied leads only. Managed search lacks local CPU/group/network byte telemetry; byte receipts are for explicit Python GETs. Denied sites were not opened from search results.'))
save('verification.json',dict(exact_results_count=20,ids_unchanged=True,raw_final_newlines=True,raw_hashes_match=True,parsed_records_match=True,reservation_sha256=sha(b),credit=0,formal_execution=False,agent_children=False,live_local_jobs=0,job_state_basis='All exec sessions returned completed exit 0; each pdftotext/conversion subprocess was synchronously reaped. No process scan used.',tool_exit_evidence='Bootstrap chunk a15577 exit 0; pre-logger bounded reads 74beda and 142e5d exit 0. One repeat finalize failed exit 1 (95e359, compact-history KeyError), corrected for idempotence; other exec tools returned exit 0; fetch sessions 96245,51841,54187,65671,72381 fully completed. Tool transcript is authoritative.'))
u=resource.getrusage(resource.RUSAGE_SELF)
with (P/'resources.jsonl').open('a') as f:f.write(json.dumps(dict(argv=sys.argv,affinity=sorted(os.sched_getaffinity(0)),cpu_limit=120,AS_limit=6*1024**3,external_wall_limit=140,wall=time.monotonic()-start,self_cpu=u.ru_utime+u.ru_stime,self_peak_RSS_KiB=u.ru_maxrss,exit_status=0,telemetry='self only; no subprocesses in finalize; not group/cgroup/service telemetry'))+'\n')
manifest={f.name:dict(bytes=f.stat().st_size,sha256=sha(f.read_bytes())) for f in sorted(P.iterdir()) if f.is_file() and f.name!='manifest.json'}
save('manifest.json',dict(excluded_self='manifest.json (self-hash cannot be embedded)',artifacts=manifest))
print(json.dumps(dict(results=len(results),reservation_sha256=sha(b),artifacts=len(manifest),credit=0,all_jobs_reaped=True)))
