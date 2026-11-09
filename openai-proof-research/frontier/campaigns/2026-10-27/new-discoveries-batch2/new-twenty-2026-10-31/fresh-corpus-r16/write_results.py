from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
recs={str(r['mathdb_id']):r for r in map(json.loads,(p/'literal-records.jsonl').read_text().splitlines())};prov=json.loads((p/'corpus-provenance.json').read_text());receipts=json.loads((p/'sources/receipts.json').read_text())
notes={
335577:('parked','Qualitative near-additivity record gives no quantitative error/dimension quantifiers. Need original capacity definitions and a uniform error mechanism; no finite certificate proposed.'),
335595:('parked','Exact maximum for every odd prime power, split by residue modulo4. A small counterexample is feasible but finite-field polarity implementation and primary Parsons/Mubayi-Williford comparisons not completed.'),
335597:('unresolved_attempt','Exact paired-row hook-length evaluation through n80 found no failed inequality; this range already checked in the 2015 original. Endpoint algebra and failed summation route in ATTEMPTS.md. No full-scope injection or uniform inequality.'),
335599:('parked','Requires local representation-theory wave-front and descent definitions, including expected uniqueness assumption; no finite full-scope mechanism identified.'),
335670:('parked','Cage claim quantifies over globally minimum-order k-geodetic digraphs; one irregular k-geodetic example is not a cage certificate.'),
335700:('parked','Sufficiently-large-n quantifier defeats a small exceptional graph. Requires actual minor exclusion plus spectral comparison on an unbounded family or full extremal theorem.'),
335701:('parked','Source Conjecture18 read. Would need a toroidal box society at n=4k+2 with a=k+1 to refute, with all pairwise intersections and exact maximum overlap; no such construction obtained.'),
335706:('parked','Uniform DNF-width big-O assertion; no finite Boolean function refutes an unspecified constant. Bias/measure and influence normalization must first be fixed from source.'),
335707:('parked','Uniform junta-size big-O assertion. Small finite sweeps cannot refute it; needs unbounded dimension and approximation lower bounds.'),
335725:('parked','Full convex spherical-domain covering inequality; no cap/domain counterexample with rigorous inradius bounds identified.'),
335752:('excluded_routine_or_source_known','Literal O(n^3) upper bound follows immediately from pair count times diameter. Source introduces same conjecture and asserts stronger results, but its displayed stronger error estimates were not audited and are unnecessary to this exclusion.'),
335764:('parked','Fixed-area torsional rigidity needs analytic PDE/variational endpoint, not a rational finite arithmetic witness. No full-scope rearrangement proof obtained.'),
335800:('parked','dP3-fibration class and maximization across dimensions need precise toric definitions; no independently computable exact volume competitor established.'),
335849:('excluded_known','Same cited source Theorem2.6 and complete proof already establish literal bipartite conclusion. Source record open label is stale.'),
335865:('parked','Minor-critical tree-depth requires proving every proper minor lower depth; no violating graph and tree-depth certificate constructed.'),
335940:('parked','Must define vertex set and edge relation for relative noncommuting graph from original. Proper noncommutative-subring restriction is material; no finite ring and class2 certificate obtained.'),
335942:('source_scope_hold','Fetched arXivv1 has Proposition2: SO(n) Haar trace average, not the record general positive-functional conjecture/generic subgroup. No authenticated passage matching the literal record located. Scalar trace-normalization/trivial-group objections would be wording/domain corrections, not credit.'),
336032:('parked','Full acyclic edge-coloring Delta+2 conjecture. No bounded graph with exact obstruction found; do not treat planar special results as the universal endpoint.'),
336036:('parked_prior_scope','Known pseudounitary extension literature surfaced, but full literal general ribbon/categorical-dimension scope not reconciled with theorem bodies. No novelty clearance or new endpoint.'),
336049:('parked','All 2-connected distinguishing-index bound; automorphism-group and edge-color-orbit certification needed for finite refutation, no witness identified.'),
336063:('excluded_record_reports_known','Literal record explicitly states existing counterexamples. Retrieved original body but no counterexample successor proof inspected; no new credit, no claim of full primary review.'),
336111:('excluded_known','Li-Wu1709.01225 Theorem2.2 and whole centroid-induction proof read. It proves the same endpoint; independent centroid route is rediscovery.'),
336116:('excluded_known','Jones2009.09616 Theorem4.3 and Proposition4.4 complete selected proof read: rank n-1 implies star. Star definition gives bijective deletion, exactly MathDB. Counterexample solver abandoned after predecessor found.'),
336130:('unresolved_attempt','Published2020 Conjecture1 persists. Reduced exact two-cover conditions to bipartitions; 146 self-centered diameter3 examples passed. Direct source greedy initialization fails on explicit 10-vertex diagnostic; global extension lemma remains unproved.'),
336213:('parked','Needs actual circular LLT definition and normalized power-sum expansion; no negative/unimodal-failure coefficient identified. Ordinary vertical-strip positivity cannot be assumed to cover circular data.'),
336228:('parked','Odd square q excluding9. Full projective-plane arc completeness is required, not a large incomplete arc; no exact counterexample certificate.'),
336259:('parked','Sourcev2 Definition2.1/2.3 and Conjecture2.4 read. A tricky vanishing sum alone is not a square Hadamard completion. No full orthogonal matrix containing such a row quotient constructed.'),
336283:('parked','Johnson adjacency indexed q must be decoded before search; known smallq and EKR-type comparison do not settle allq. No new coclique certificate.'),
336301:('excluded_known','Same source Acan-Kahn Theorem1.2 already gives high-probability packing O(n^2/k^3) for k=k0-C, contradicting proposed Omega(n^2/k^2) after expectation tail control. Only theorem passage read, not entire technical proof.'),
336323:('excluded_wording_correction','Actual e_q is MAXIMUM, record says minimum and lower bound. Monomial X0^d immediately separates literal minimum interpretation from conjectured maximum. This is a source-direction error, zero significance credit; intended maximum theorem remains unresolved here.'),
336369:('parked','Prescribed Reorder/admissible partial-coloring algorithm must be read literally. Goldberg-Seymour existence theorem alone does not prove this algorithm succeeds.'),
336401:('excluded_record_reports_known','Literal statement explicitly says proved in the source; no new result. Original Borg proof not fetched/read, primary depth remains literal.'),
336413:('excluded_degeneracy_route_only','As written no general-position hypothesis; collinear sets in dimension2 supply only degenerate simplices. Such domain/wording objections are explicitly uncreditable; intended nondegenerate depth conjecture not solved.'),
336414:('excluded_degeneracy_route_only','Unrestricted lower-dimensional configurations allow rays avoiding spanned faces. Missing general-position/domain hypotheses are not a significant new result; genuine higher-dimensional depth endpoint unproved.'),
336479:('parked','Approximation complexity requires exact input-size and CFT representation model; no finite counterexample can settle generic BQP completeness as stated.'),
336506:('excluded_known_report_scope','Original Section8.3 Conjecture8.1 explicitly reports Duyan-Halasi-Maroti proof announcement. Full proof not read, so excluded from nomination without claiming predecessor technical audit.'),
336519:('parked','Asymptotic linear bound needs uniform dimension estimate or superlinear family. No full Gram-matrix construction violating O(d), and finite instances cannot refute hidden constant.'),
336525:('excluded_known','Kwan-Sah-Sawhney-Simkin2201.04554 Theorem1.1 explicitly proves high-girth STS existence for all sufficiently large admissible orders. Theorem and definition passages read, entire100-page proof not reviewed.'),
336575:('excluded_known_passage','Same source Theorem5 covers t>=5 with order >=(2t-1)k and reports predecessor t4 already proved. Main theorem passage read; predecessor t4 and full long proof not audited. No new nomination.'),
336691:('parked','Bollobas-Eldridge-Catlin universal graph packing inequality. No violating pair with certified nonpacking found; parameter instances/known partial theorems earn zero.')}
primary={335597:['1703.06382','1511.08653'],335701:['1703.09870'],335752:['1704.00964'],335849:['1704.06093'],335942:['1705.02212'],336111:['1705.07270','1709.01225'],336116:['1705.07437','powerful-published','2009.09616'],336130:['1705.07982','appendage-published'],336259:['1706.00986'],336301:['1706.01866'],336323:['1706.03050'],336506:['1706.10028'],336525:['2201.04554'],336575:['1707.02390']}
proofs={335849:['1704.06093 Theorem2.6 pp4-5'],336111:['1709.01225 Lemma2.1/Theorem2.2 pp2-3'],336116:['2009.09616 Theorem4.3 pp6-9; Proposition4.4 p9'],336130:['1705.07982 Proposition3.2/Theorem3.3 and Proposition5.2; published Proposition3.1/Theorem3.1 and Proposition5.2'],335597:['1511.08653 Theorem4.4 double-hook proof (special family only)']}
res={}
for sid,r in recs.items():
 i=int(sid);status,note=notes[i];sources=[]
 for n in primary.get(i,[]):
  f=p/'sources'/(n+'.pdf');sources.append({'file':str(f.relative_to(p)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'receipt':next((z for z in receipts if z.get('file')==str(f.relative_to(p))),None)})
 res[sid]={'mathdb_id':i,'title':r['title'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'literal_statement':r['statement'],'corpus_provenance':prov[sid],'review_depth':{'literal_record':True,'primary_passage':bool(sources),'selected_proof_body':proofs.get(i,[])},'sources':sources,'status':status,'reason_or_obstruction':note,'ordinary_full_scope_proof':False,'literal_Lean_endpoint':None,'strict_extracted_replay':'not applicable: no new full-scope certificate','axiom_audit':'not applicable: no Lean declarations','accepted_credit':0,'independent_review':'not performed; root-controlled later','novelty_limit':'No worldwide-priority claim. Metadata/search misses are not clearance.'}
assert len(res)==40
(p/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
print('wrote',len(res),'records; primary passages',sum(x['review_depth']['primary_passage'] for x in res.values()))
