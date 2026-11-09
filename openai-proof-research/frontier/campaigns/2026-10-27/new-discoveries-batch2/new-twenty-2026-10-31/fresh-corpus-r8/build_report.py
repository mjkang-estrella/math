from pathlib import Path
import json,hashlib,datetime,subprocess,zipfile
p=Path(__file__).resolve().parent
notes={
328526:'Energy minimization over connected graphs for an edge interval. Bipartite cases do not settle the nonbipartite minimizer; no exact lower-energy witness established. Literal only.',
328559:'Non-divergence for arbitrary discrete subgroups needs quantitative recurrence on homogeneous spaces; epsilon quantifier absent from normalized wording. No exploit of missing quantifier.',
328602:'Equality of percolation and limiting homological thresholds requires both infinite-volume constructions and rank-difference semantics. No finite-test reduction.',
328626:'Exact unit-circle root count for prime-indicator polynomials strengthens Goldbach. Divisibility supplies only lower bound, not absence of further boundary roots. No full route.',
328630:'Distinct cycle-length count is asymptotic with an O(1) allowance. A small graph cannot refute it. Need an infinite family defeating the leading constant.',
328638:'Public 2021 Matchings and squarefree powers of edge ideals explicitly gives connected and disconnected nu0-counterexamples (Figures1,2); publisher primary search body excerpt inspected, full proof not audited. Do not formalize as new.',
328705:'SURVIVING COMPLETE FORMAL CANDIDATE: 153 rational nonzero real critical points for n17,d3,u all2; full critical set finite. Source pp4,6-7 and proof Theorem2.13 inspected; p7 rendered. Lean Fermat.claim_false, source quantifier distinction documented.',
328709:'Defect-by-defect unlikely intersections assertion. Ordinary Zilber-Pink implication is not an unconditional proof. No full special-subvariety semantics available.',
328710:'Record explicitly lacks definition of defect condition. No conclusion from the label or elementary dimension inequalities; requires source reconstruction.',
328743:'Dense two-color cycle partition threshold: asymptotic slack cannot settle exact bound; cycle conventions must include degenerate cycles. No small-case loophole used.',
328755:'Open Virasoro constraints likely have substantial subsequent open-intersection literature, not screened in primary bodies here. No novelty clearance; infinite operator identities not formalized.',
328760:'Record explicitly flags subsequent work on Oblak recursion. Maximum-U-chain implementation alone would not establish equality with generic Jordan type. No prior-art clearance.',
328869:'K-Knuth connectivity needs a path through words bounded by maximum tableau size, not merely endpoint insertion equivalence. No constructive path theorem.',
328876:'Read Conjecture5.2 and Proposition5.3 tree-decomposition proof. Trees satisfy it publicly; singleton/edgeless negative RHS is a prohibited endpoint correction. General half-factor decomposition remains unproved.',
328878:'Finite-field moment invariant and low-degree curve assertion have missing epsilon/t hypotheses. No use of unrestricted t or moment-index typography to manufacture refutation.',
328899:'Asymptotic acyclic coloring logarithmic improvement: no finite-oriented-graph test settles O-bound. Need uniform coloring method.',
328900:'m-degenerate extension includes uniformity of constant and asymptotic ratio. Cases m1 and bounded degree cannot resolve full assertion.',
328910:'P_j indexing and generalized-star paths not specified by record. Requires primary definitions before numerical interpretation; no claimed witness.',
328945:'Rectilinear tripartite crossing expression A is source-defined; no implementation of A or certified drawing enumeration. Parameter cases do not count.',
328946:'All tripartite sizes require optimum among arbitrary topological drawings versus straight drawings, not a finite diagram comparison. No full route.',
328947:'Normalized literal record already says primary paper proves polynomial algorithm via Clar number. Excluded on reported public resolution, body not independently audited.',
328951:'Equitable vertex-arboricity bound needs simultaneous balance and forest structure at every k. Standard greedy degeneracy does not provide equitability.',
328977:'Normalized literal record explicitly says its own paper completes proof of both assertions. Excluded on reported public resolution; no body audit claimed.',
328993:'Infinite transitive local-convergence connective constants require global self-avoiding-walk lower semicontinuity. Local finite path counts give only one semicontinuity direction.',
329057:'Exceptional paired Jacobian realization is sensitive to pairing rather than group alone. Cyclic wording may be corrupt; no group-order-only counterexample.',
329059:'Chow-to-cohomology injection for all small p-groups. A single cohomology computation without cycle-class semantic bridge would be insufficient.',
329061:'Read game definition, trunk simulation Lemmas1-3 and Theorem4 proof, Lemma27/Theorem28 proof, Conjecture29. Pruning high-degree leaves does not transfer Bob strategies: outside moves consume turns and neighbor colors. Need local strategy-preserving reduction, not existence elsewhere of a subcubic chi4 tree.',
329107:'Torsion transition endpoint involves entropy and normalization, not Alexander polynomial alone. No finite spectral substitute or exact source torsion construction.',
329174:'Primary concluding Conjecture inspected; full coloring-bound proof not reviewed. General cyclic interval-color count has substantial later literature; no certified graph/coloring witness.',
329259:'Read Conjecture2.7, inversion definitions and reciprocity induction proof Proposition2.6. Exact recurrence diagnostic finds no distinct-value violation through b300. Ranking multiplicities creates spurious violations because inverse a gives repeated values; not counted. Rank-transfer induction remains missing.',
329260:'Normalized statement explicitly says source abstract resolves displayed Alon-Frankl conjecture. Excluded as reported known, without inflating body coverage.',
329332:'Universal equality for any polygon differs from generic-polygon experimental motivation. Regular low-extension-complexity examples only expose wording/genericity and known extension constructions; prohibited as discovery.',
329344:'Weight bounds for arbitrary loop amplitudes need definitions of periods/weight and scheme; no mathematical endpoint reconstructed.',
329418:'Twin-free locating domination n/2 bound: arbitrary twin-free graph search would require exhaustive locating-set certificate, but no structural obstruction identified. No claim of current open status.',
329425:'PRIMARY RESOLVES: arXiv1412.2796v2 pp25-27 explicitly proves Conjecture5.1. Read Lemma5.4 integration-by-parts, Lemma5.5 inductive degree/denominator control, final proof using c_k integral. Exact bound 2^(k+1)+1 follows without new deduction.',
329433:'Source defines P1 as LARGEST prime divisor (p8), normalized record says smallest. Read Definition1.1, Lemma3.5 and Corollary3.2 proof/Conjecture3.2 pp11-12. Do not turn smallest/largest corruption into claimed new solution. True largest-prime cubic bound remains unproved here.',
329462:'Primary Lemma4.8 already supplies unsplittable triangle. Splittable overlap example B1={1,2},B2={2,3},B3={1,3,4} has16 splitters on[7], versus24 for disjoint sizes2,2,3. Later Coskey et al.2022 section4/AppendixA already computes near-unsplittable minimum configurations through k60, including small structure. Excluded; no formalization spent on public/subsumed result.',
329469:'Random EKR assertion uses source-specific Lambda and uniform asymptotics. No finite small hypergraph refutation can bypass almost-sure hypotheses.',
329484:'Automorphic sup-norm bound is epsilon-uniform over newforms with conductor restriction. No exact finite-dimensional substitution; local obstruction alone not full conjecture.',
329486:'Title and literal statement already report Solution to a conjecture. Excluded as reported source resolution; no primary proof audit claimed.'}
body={328705,328876,329061,329259,329425,329433,329462}
statement={329174}; excerpts={328638}
res={}
for r in json.loads((p/'records.json').read_text()):
 i=r['mathdb_id'];res[str(i)]={'mathdb_id':i,'title':r['title'],'literal_statement_reviewed':True,'primary_body_depth':('definitions_and_selected_theorem_proofs' if i in body else 'primary_statement_only' if i in statement else 'primary_publisher_search_excerpt_only' if i in excerpts else 'not_read'), 'status':'complete_lean_candidate_pending_independent_review' if i==328705 else 'excluded_or_parked_no_credit','accepted_credit':0,'assessment':notes[i],'source_url':r['source_url']}
(p/'results.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n')
receipts=[]
urls={'fermat':'https://arxiv.org/pdf/1409.0684','forest':'https://arxiv.org/pdf/1410.5223','rank':'https://arxiv.org/pdf/1412.2796','aluffi-harris':'https://msp.org/ant/2018/12-8/ant-v12-n8-p06-p.pdf','draisma':'https://arxiv.org/pdf/1309.0049'}
for n,u in urls.items():
 f=p/'sources'/f'{n}.pdf';receipts.append({'file':str(f.relative_to(p)),'url':u,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'retrieval_session_date':'2026-11-01 UTC / 2026-10-31 Pacific','status':200})
(p/'sources/additional-receipts.json').write_text(json.dumps(receipts,indent=2))
print(len(res),'records; body-depth',len(body))
