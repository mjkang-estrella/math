import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parent;L=D.parent;B=L.parent
load=lambda p:json.loads(p.read_text())
write=lambda n,v:(D/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
notes={}
for line in (D/'assessments.tsv').read_text().splitlines():
 i,flag,disp,q,note=line.split('\t');notes[int(i)]=(flag,disp,q,note)
assert len(notes)==50
out=[]
for x in load(D/'literal-records.json'):
 r=x['record'];i=r['mathdb_id'];flag,disp,q,note=notes[i];s=r['statement']
 out.append({'mathdb_id':i,'canonical_url':r['canonical_url'],'title':r['title'],'corpus_path':x['corpus_path'],'corpus_line':x['line'],'canonical_record_sha256':x['canonical_record_sha256'],'statement_exact_utf8':s,'statement_utf8_sha256':hashlib.sha256(s.encode()).hexdigest(),'inherited_statement_completeness':r.get('statement_completeness'),'independent_statement_flag':flag,'complete_self_contained_statement':flag=='self-contained','quantifiers_and_scope':q,'disposition':disp,'technical_assessment':note,'source_url':r.get('source_url'),'primary_passage_read':i in [342406,344316,343872,343832],'whole_body_read':False,'full_dependency_audit':False,'closest_successor_bodies_cleared':False,'current_registry_cleared':False,'novelty_pass':False,'accepted_credit':0,'local_full_scope_proof':False})
write('dispositions.json',out);write('proposals.json',[])
write('source-coverage.json',{'literal_records_reviewed':50,'self_contained':sum(x['complete_self_contained_statement'] for x in out),'flags':dict(collections.Counter(x['independent_statement_flag'] for x in out)),'primary_selected_passage_records':[342406,343832,343872,344316],'whole_bodies_read':0,'dependency_audits':0,'closest_prior_successor_body_clearances':0,'current_registry_clearances':0,'live_mathdb_requests':0,'new_proposals':0,'source_readings':[{'id':342406,'version':'1904.05214v1','passages':'Definitions1.1-1.3; Question1.5; Conjecture2.1; Lemma2.3; Theorem2.4 and random-walk proof outline','scope':'Exact public theorem statement, source proof outline; original cited proof [4] not independently audited.'},{'id':344316,'version':'1910.13433v2','passages':'Theorem1.1; threshold and weak p-small definitions; comparison to Talagrand conjecture; selected concluding Theorem1.6 proof paragraphs','scope':'Stronger source theorem and direct ell<=|X| bridge; not a complete independent proof audit; log and trivial-family conventions retained.'},{'id':343872,'version':'1909.09037v2','passages':'Section4.1 Definition12, Eq24, Lemma15; AppendixB Jacobian derivation and eigenvalue proof','scope':'Body-confirmed narrower proved result and material definition mismatch; no literal whole-scope retirement.'},{'id':343832,'version':'1909.07141v1','passages':'Section3 lower construction; Conjecture3.1; following n=2 known/n=3 limitation','scope':'Primary statement agrees, no general proof or prior-body clearance.'}]})
paths=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']
# Traverse only these already bound JSON documents; associations are administrative, never mathematical clearance.
ids=set(notes);matches=[]
def visit(o,path):
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ('mathdb_id','mathdb_related_id','related_mathdb_id') and isinstance(v,int) and v in ids:matches.append({'id':v,'path':path,'key':k})
   visit(v,path)
 elif isinstance(o,list):
  for v in o:visit(v,path)
for p in paths:visit(load(p),str(p))
write('prior-context-check.json',{'documents':[str(p) for p in paths],'exact_id_associations':matches,'interpretation':'Administrative associations only; not independent literature clearance. r363 Cayley source-restriction exclusion read. r603 adjudications and hypothesis queue govern protected IDs; none promoted. Current counts 9 additional/39 total/next40 unchanged.'})
write('failures.json',{'fetch_failures':load(D/'fetch-failures.json'),'stopped_routes':['No full-scope proof route survived literal screening; no substantial proof attempt or repeated sweep.','343771 missing theorem hypotheses;343973 absent density hypothesis: incomplete, no reconstructed target.','343872 record domain and eigenvalue conventions differ from source; domain correction earns no credit.','343832 two-variable endpoint motion does not control changing minimum index sets.'],'access_holds':['MathDB429: zero requests.','Current public proof registry unavailable; HOLD without absence-of-hits inference.','Parked AIM/Kourovka/EGRES/AIProofWatch, DMGT TLS, ProjectEuclid challenge, ResearchGate403 and OEIS A274199/internal403: no requests or alternative routes.'],'process_deviations':['Initial SHA256-only binding preceded displaying manifest/bindings/reservation and a short coverage head; explicit independent SHA256+size flat binding followed before scientific literal screening. Timing requirement not retroactively satisfied.','An overbroad rg --files listing returned truncated path output; no historical tree content copied or recursively expanded.'],'resource_failures':[],'math_novelty_pass':False})
counts=collections.Counter(x['independent_statement_flag'] for x in out)
(D/'SUMMARY.md').write_text('''# r604 breadth handback

Reviewed exactly the 50 literal records reserved by immutable root r603. Baseline remains **6,033 reported literal reviews**, not complete technical corpus coverage. This lane contributes 50 distinct literal screens for root reconciliation; it does not edit shared coverage. The routing queue contains 8,000 metadata rows, not reviews. Campaign counts remain 9 additional / 39 total / next40.

**Zero proposals and zero discovery credit.** No full-scope proof/counterexample route passed source, prior-body and registry gates. Each disposition retains exact UTF-8 statement, canonical record SHA256, original chunk/line, individual quantifiers and an honest technical obstruction. Statement flags: '''+json.dumps(dict(counts))+'''. The two incomplete records are not complete-statement reviews.

Selected primary passages were inspected for four records, using freshly byte-bound arXiv HTML and separately bound text derivatives. 342406 is already an exact theorem in its cited source (Theorem2.4); 344316 follows directly from its source's stronger Theorem1.1. These are source-internal eligibility exclusions, not independently replayed complete proof bodies. 343872 materially mismatches the source domain and eigenvalue convention; its narrower proved Lemma15 is not a full literal retirement. 343832 matches Conjecture3.1 but supplies no new all-n route. No abstracts are upgraded to proof-body retirements. No whole-body reading, complete dependency audit or closest-successor clearance is claimed.

Integrity check independently matched intake exact payload, direct original/copy pairs, all 20 original r301 corpus chunks in place and all 8 separately listed frozen inputs. The r301 manifest matched the intake binding. All three current reservations (Claude r602, Sol r600, Sol r604) are disjoint from 6,033 coverage IDs, one another and protected IDs. Completed r504/r598 are not reserved anew. r304 accepted/historical records, r363 Cayley decision and current r603 adjudications were bound and consulted. No corpus or historical tree was copied.

Access: zero MathDB requests; current registry remains unavailable/HOLD. Four lawful primary HTML fetches succeeded with generic headers; no forbidden service, browser, API, publication or contact was used. No bounded mathematical enumeration was executed or claimed. No Lean/manuscript/credit changes.

**Process limitation:** the initial binding captured SHA256 before a short administrative coverage display but did not yet explicitly capture size; the later full SHA256+size binding preceded scientific screening. This timing deviation is preserved in failures.json. Integrity PASS is not mathematics or novelty PASS.

Run the independent read-only verifier through the fixed helper guard, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and python3 -B. It checks exact payload (only manifest.json and final-verification-receipt.json excluded), originals, corpus inventory, reservation disjointness and literal/canonical hashes. Negative tests exercise hash, size and extra-file rejection entirely in memory without changing originals. The separate final receipt binds manifest SHA256 and size.
''')
