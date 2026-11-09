from pathlib import Path
import json,collections,datetime
D=Path(__file__).resolve().parent;L=D.parent
def load(p):return json.loads(p.read_text())
def save(n,x):(D/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
notes={}
for line in (D/'review-notes.tsv').read_text().splitlines():
 i,c,d,n=line.split('\t',3);notes[int(i)]=(c,d,n)
rows=load(D/'literal-records.json');assert len(rows)==len(notes)==50
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];c,d,n=notes[i]
 primary=i in [387253,387279,387311,387315,387346,387367,387368,387371,387372,387386,387398,387461,387465]
 out.append({'mathdb_id':i,'title':r['title'],'statement':r['statement'],'statement_utf8_sha256':x['statement_utf8_sha256'],'canonical_record_sha256':x['canonical_record_sha256'],'corpus_path':x['corpus_path'],'corpus_line':x['line'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'corpus_statement_completeness':r['statement_completeness'],'independent_scope_classification':c,'literal_record_review':True,'quantifiers_route_objection':n,'disposition':d,'source_evidence':{'literal_statement':'read in full','primary_passage':'selected question and surrounding definitions read' if primary else 'not read; HOLD','whole_primary_body':'not read in full','successor_body':'selected theorem/proof passages read; see source-coverage.json' if i in [387368,387371] else 'not cleared','local_proof':'short hand argument; see bounded-checks.json' if i==387104 else 'no credited proof','full_dependency_audit':False,'current_registry':'unavailable HOLD; no inference from absence of hits'},'prior_cleared':False,'source_scope_cleared':False,'accepted_credit':0,'remaining_obligations':'Exact primary definitions/version, full applicable prior and source-internal subsumption, current registry, substantive eligibility, proof and independent review remain uncleared; public theorem match bars a new claim.' if i==387371 else 'No hypothesis promotion. Retain scope/access/prior gates; do not extend finite diagnostics or silently repair the statement.'})
save('dispositions.json',out);save('proposals.json',[])
counts=dict(collections.Counter(x['independent_scope_classification'] for x in out))
save('source-coverage.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_reported_literal_reviews':6583,'new_literal_reviews':50,'intake_routing_rows':8000,'routing_rows_are_technical_coverage':False,'scope_classes':counts,'primary_question_passages':13,'whole_primary_bodies_read':0,'successor_selected_bodies':2,'full_dependency_audits':0,'proof_or_novelty_passes':0,'promoted_hypotheses':0,'sources':[
{'ids':[387253,387279,387311,387315,387346],'url':'https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf','version':'unversioned cached original; exact bytes in flat-bindings.json','snapshot':'sol-mathdb-primary-qualified-breadth-r404/evidence/bestvina.pdf','derivative':'sol-mathdb-primary-qualified-breadth-r404/evidence/bestvina.txt','coverage':'Q1.10 lines94-97; Q2.18 lines348-355; Q8.10 and preceding definitions; Q10.2 lines728-733; Q13.3 lines967-971. Selected question/context only; no PDF visual/layout audit or whole-body proof audit.'},
{'ids':[387367,387368,387371,387372,387386,387398],'url':'https://www.renyi.hu/~abert/questions.pdf','version':'unversioned snapshot requested 2026-10-31T08:53:54.193180+00:00','snapshot':'sol-mathdb-primary-qualified-breadth-r406/primary/abert.pdf','derivative':'sol-mathdb-primary-qualified-breadth-r406/primary/abert.txt','coverage':'Q14/15 lines128-140; Q18/19 lines155-165; Q32/33 lines230-236; Q45 lines279-283. Selected passages only. No whole-body or PDF visual audit.'},
{'ids':[387461,387465],'url':'https://arxiv.org/html/1503.05295v1','version':'v1, 18 March 2015; cached source original in r576','coverage':'Section II Lemma1, ODE(1.1), Omega_k and Problem1; Problem4 and surrounding discussion. Source HTML plus bound derivative; no full-body audit.'},
{'ids':[387368],'url':'https://arxiv.org/html/1201.3861v3','version':'v3','coverage':'Definitions and Theorem1.1 lines165-215; Theorem3.4 selected Newton-identity passage lines1123-1178; selected proof of Theorem1.1 lines1250-1350. Absolute degree bound retained. Not a complete proof/dependency replay.'},
{'ids':[387371],'url':'https://arxiv.org/html/0912.2444v3','version':'v3','coverage':'Independent-set objective; configuration/simple passage lines542-567; Theorem3 lines929-956; Theorem7 statement lines2395-2418; proof of Theorem3 lines2926-2959. Proposition5 and interpolation proof not fully replayed. Published theorem match, not new proof.'}]})
save('failures.json',{'new_HTTP_failures':[],'stopped_routes':['MathDB inherited429: zero requests','AIM, Kourovka, EGRES, AIProofWatch remain parked; no request','DMGT TLS; ProjectEuclid challenge; ResearchGate403 remain parked','OEIS A274199/internal r542 HTTP403 remains parked','current proof registry unavailable: HOLD'],'stopped_mathematical_routes':[{'id':387169,'reason':'no divisibility counterexample n40..500; no all-n mechanism; no sweep extension'},{'id':387104,'reason':'short classical containment argument; primary/prior inaccessible, no eligible hypothesis'},{'id':387019,'reason':'real-closed-field algorithm is routine and real-input representation is a scope issue'},{'id':387368,'reason':'unbounded-degree diagnostic is wording/domain correction; bounded-degree case publicly proved'},{'id':387371,'reason':'actual public theorem matches intended full scope'}],'deviations':['During schema inspection before bind.py, head of queue exposed two titles and first two unrelated corpus rows with null statements. No scientific reasoning or historical summary relied on them before binding. Retained as a timing disclosure.'],'guard_failures':[],'upstream_verify_executed':False})
save('search-provenance.json',{'utc_date':'2026-10-31','tool':'web search','queries':['Abért Hubai Benjamini Schramm convergence distribution chromatic roots arxiv','random regular graphs independence ratio convergence Bayati Gamarnik Tetali arxiv'],'used_primary_leads':['https://arxiv.org/abs/1201.3861','https://arxiv.org/abs/0912.2444'],'evidence_limit':'Search/abstract results only located primary sources; actual retained HTML passages read before theorem-match disposition. No search absence claim. No prohibited result was opened.'})
save('negative-tests.json',{'method':'verify.py --negative hash|size|extra; isolated in-memory mutation of manifest or file-name set; no original/file mutation; expected nonzero exits','required_cases':['hash','size','extra'],'outcome':'See separately excluded final-verification-receipt.json for actual subprocess exits.'})
(D/'SUMMARY.md').write_text('''# r626 breadth screening

Reviewed all 50 reserved literal records individually against r625 authority (6,583 prior reported record reviews). This lane proposes **zero hypotheses** and awards **zero credit**. The 8,000 routing rows are metadata, not technical coverage. No shared coverage/index/ledger/NEXT or protected target was edited.

## Scope and technical results

'''+str(counts)+'''

All dispositions retain exact UTF-8 statement, its hash, canonical record hash, original chunk/line, quantifier/route notes, and separate source/proof/registry gates. Corpus “full” flags are preserved alongside independent incomplete, definition-dependent and scope-ambiguous flags. There are 13 selected primary question/context reviews and two selected successor-body reviews; zero whole-body or full dependency audits.

387371 matches Bayati–Gamarnik–Tetali arXiv0912.2444v3 Theorem3, including admissible vertex counts and the configuration-to-simple passage. This defeats new-outcome eligibility; the interpolation and Appendix B chain were not independently replayed. 387368 matches Abért–Hubai arXiv1201.3861v3 Theorem1.1 under bounded degree. Without that source convention the literal record is ambiguous; an elementary unbounded-degree diagnostic earns no credit. 387104 has a short cyclic-subgroup containment argument, retained only as a local classical route with primary/prior HOLD. 387019 has a routine real quantifier-elimination route for effectively represented inputs.

Executed one exact bounded diagnostic for 387169: no p(n) dividing n! for 40<=n<=500. This proves no universal claim; the route was stopped. No hard target, large formal chain or repeated sweep was pursued. No Lean/manuscript changes.

## Sources and access

Existing immutable PDFs/HTML/text were reused in place after manifest hash/size comparison, without corpus or historical-tree copying. New lawful primary fetches were only arXiv1201.3861v3 and arXiv0912.2444v3 HTML, with generic headers, exact URL/version/UTC/hash/size retained. Bytes were bound before extraction and derivative hashes recorded before content search. No PDF visual work was undertaken.

Zero MathDB requests. All listed parked routes, including OEIS A274199/internal, remained parked. Current proof registry is unavailable: HOLD for every row; absence of hits is never clearance. See failures.json for stops and the prebinding schema-inspection disclosure.

## Integrity and replay

flat-bindings.json binds the exact intake manifest and payload, receipt, direct original/copy pairs, all 20 r301 chunks in place and all eight separately listed frozen inputs, plus needed ledger/prior/r304/r363 context and source snapshots. The r301 manifest is matched to intake binding. No upstream verify.py was executed. Both breadth sets, baseline coverage and protected IDs are checked independently.

Run under the fixed helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and python3 -B, passing python3 -B followed by this lane's verify.py. The verifier is read-only, independently rechecks originals and exact payload, and exits nonzero on mismatch. Its --negative hash, --negative size and --negative extra modes deliberately fail without changing files. The manifest excludes only itself and final-verification-receipt.json, and covers every other payload including verifier scripts. Final receipt reports exact manifest SHA256/size and actual negative-test exits.

**Integrity PASS is neither mathematics PASS nor novelty PASS.** Counts remain 9 additional / 39 total / next40; root alone reconciles these 50 reviews.
''')
print('50 dispositions',counts)
