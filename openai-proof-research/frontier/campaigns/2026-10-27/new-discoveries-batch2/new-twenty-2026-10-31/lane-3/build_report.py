from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent;B=P.parent.parent;L=B/'lanes';O=L/'sol-mathdb-primary-qualified-breadth-r730'
records=json.loads((O/'literal-records.json').read_text())
gaps={
321054:'Restore exact Banach-space decomposition convention and largest-ideal hypotheses; arbitrary-space commutator classification needs operator-theoretic construction.',
321058:'Restore the explicit solvable group, bounding class and relative K-theory chain-complex equivalence before defining an endpoint.',
321063:'Check later surface-diffeomorphism maximal-measure finiteness theorems; no primary successor body reviewed.',
321164:'Check finite-group class-size multiplicity literature and the quantification of the bounding function; no full primary body reviewed.',
321278:'Retrieve parity crossing matrices, determinant normalization and Reidemeister invariance; then attempt an exponent-support argument.',
321318:'Restore cross-intersection and empty-family conventions; check whether source assertion implies Chvatal-type cases before investment.',
321403:'Full arbitrary-order minimum-degree tree packing is not supplied by a bounded-order theorem; embedding dependencies unresolved.',
321404:'Full average-degree tree packing requires simultaneous edge-disjoint embeddings; a single-tree extremal theorem is insufficient.',
321412:'Restore transitive-process definition and radius convention; intensity alone does not specify the comparison class.',
321413:'Restore the evaluation map, trace-reduction choices and all monomial quantifiers; current statement is definition-dependent.',
321431:'Check current Watanabe-Yoshida results in all dimensions and equality cases; no primary successor body reviewed.',
321476:'Need exact indecomposable class, small-order extrema and live extremal-permanent literature before a certified construction search.',
321500:'Restore pyramid levels, allowed query information and adaptive-round semantics; minimax strategy formalization could be substantial.',
321503:'Restore coefficient modules, cusp class and spectral sequence conventions; the record says as above and is not standalone.',
321506:'Restore stable category, finite-polyhedron conventions and exact torsion quotient; topology infrastructure is substantial.',
321530:'Check published bounded nonrepetitive planar coloring results before any proof investment; no successor theorem body reviewed here.',
321549:'Restore excess normalization and p-extremal definition, then compare later enumerations; no finite counterexample certificate obtained.',
321555:'Restore d range and distinction between triangle-free and no triangular faces; no full source passage reviewed.',
321583:'Restore concentration-at-zero versus maximum-atom convention and uniqueness modulo scaling; no partition search performed.',
321630:'Check squarefree-game rational-strategy corrections and later lattice-game counterexamples against the exact rule-set definition.',
321661:'Restore uniformity range of epsilon(n); a fixed-epsilon bound does not solve a near-critical uniform statement.',
321672:'Check complete-intersection-for-permutations literature; fixed t and all t,n quantifiers must not be confused.',
321782:'Restore intrinsic boundary length metrics, gluing and dimensional hypotheses before selecting a counterexample.',
321800:'Restore generic-channel quantifiers, antenna counts and precise degrees-of-freedom equivalence; no full source body reviewed.',
321841:'Restore maximal analytic and geometric radii and continuation convention; substantial analytic geometry formalization.',
321864:'Restore noncommutative ideal and M-essential equality exactly; no arbitrary-knot mechanism or Lean infrastructure established.',
321903:'Restore reversal-ratio and WRR definitions from primary body; the record is not a usable standalone endpoint.',
322009:'Restore reduced finite-point complete-intersection and minimum-distance definition; check later coding-theory resolution bodies.',
322109:'Restore meaning of C_n, common upper bound and path quantifier (some versus every geodesic); record wording insufficient.',
322141:'Restore nondegeneracy restrictions on point sets; degenerate affine stabilizers could make the displayed count infinite but are not a legitimate domain-repair discovery.',
322147:'Check later oriented-diameter bounds and exact bridgeless connected convention; no primary successor read.',
322163:'No tractable route for arbitrary zeta zero ordinates; RH or finite numerical checks would not prove rational independence.',
322178:'Restore parameter strata, standard modules and all specialization maps; no finite algebraic certificate selected.',
322185:'Check prior Kontsevich noncommutative birational-map order-three proofs before investment; exact universal skew-field endpoint needed.',
322187:'Check unrestricted versus bounded-curvature splitting results; geometric/PDE infrastructure would be extensive.',
322215:'Check all-transitive-group diameter literature; symmetric/alternating results alone do not settle the exact statement.',
322223:'Check directed immersion successor results; minimum outdegree and antiparallel-edge conventions need source restoration.',
322227:'Restore the language, schemes and conservativity class; the displayed Ramsey definition itself needs primary comparison.',
322270:'Check published full-range random-graph Hamilton-packing theorems; sparse-range proof alone is not new full-scope evidence.',
322300:'Restore extremal rotation-number function and admissible lift parameters; no all-word rationality proof found.',
322322:'Restore toric g-vector and Gorenstein-star meet-semilattice conventions; no general M-sequence mechanism established.',
322336:'This is an efficiency proposal without a quantified performance or existence endpoint; cannot supply an exact Lean target from metadata.',
322420:'The supplied record explicitly says resolved; restore actual cited result and direction before any formalization investment.',
322421:'Restore embedding-sequence approximate dimension definitions and lower-dimension conventions; no analytic estimate established.',
322437:'Restore probability mode, dimension and boundary conditions; check later Cheeger-limit papers before investment.'}
r={}
for item in records:
 x=item['record'];i=x['mathdb_id']
 r[str(i)]={'mathdb_id':i,'title':x['title'],'mathdb_url':x['canonical_url'],'record_statement':x['statement'],'source_url':x['source_url'],'review_depth':'literal_cached_record_only','disposition':'HOLD_NOT_FULLY_REVIEWED','remaining':gaps.get(i,''),'selected':i in [321110,322148,322229],'new_result_claim':False,'credit':0,'lean':{'complete':False,'endpoint':None,'axiom_audit':None,'clean_rebuild':None},'novelty_cleared':False}
r['321110'].update(review_depth='original and 2017 successor selected theorem/proof bodies',disposition='EXCLUDE_PUBLICLY_PROVED',remaining='No discovery investment justified; full registry clearance unnecessary to exclude known proof.',source_statement='For every finite simple graph G, at least dc(G) independent sets S have d(S)>0 and no proper subset with positive difference; d(S)=|S|-|N(S)|.',primary_evidence=['https://arxiv.org/html/1102.1859v1 Conjecture 3.1','https://arxiv.org/html/1701.03040v1 Theorem 2.11, Corollary 2.12'],prior_art='2017 primary manuscript explicitly proves the target; no new proof claimed.')
r['322148'].update(review_depth='original definitions, Conjecture 2.3, Theorem 1.2 and live public counterexample body',disposition='EXCLUDE_PUBLIC_COUNTEREXAMPLE_AND_RECORD_DEFINITION_MISMATCH',remaining='Exact MathDB min/max mismatch requires fidelity adjudication, not a credited domain correction. Public counterexample already covers intended maximum.',source_statement='M(n,r) is the MAXIMUM of Delta(F)/delta(F) over covering maximal intersecting r-uniform families on [n]; for r=o(n), conjectured M(n,r)=Theta(n).',primary_evidence=['https://arxiv.org/html/1109.1079v1 definitions and Conjecture 2.3','https://probxiv.com/problems/on-the-ratio-of-maximum-and-minimum-degree-in-maximal-intersecting'],prior_art='Live public proof constructs a maximal family with minimum degree 1 and maximum degree binom(2r-2,r-1)+n-2r+1. At n=2^r ratio/n diverges. Independently checked its maximality cases. Posting date of proof comment not recovered; page added Aug 17, 2026. No priority claim.')
r['322229'].update(review_depth='primary Sections 2 and 5 definitions and general-bound proof passages; sustained structural and exhaustive finite attempts',disposition='PARK_NO_FULL_PROOF',remaining='Need separator-sensitive Roman bondage construction for graphs where lambda>kappa and existing local path bounds exceed target; no full proof or refutation, no Lean theorem.',source_statement='For every finite simple connected graph G of order at least 3, b_R(G)<=2*Delta(G)+kappa(G)-3, with b_R the least number of edges whose deletion strictly increases the minimum weight of f:V->{0,1,2} such that each zero has a neighbor labelled 2.',primary_evidence=['https://arxiv.org/html/1109.3930v1 Conjecture 5.1; Theorems 5.1, 5.2, 5.6, 5.9'],attempts_file='ROMAN-ATTEMPT.md',diagnostics_file='roman-diagnostics.json',formalization_feasibility='Finite graph endpoint is practical in Lean once a proof exists. Must build RDF, finite minimum gamma_R, deletion, finite minimum b_R, degree maxima and vertex connectivity and all specification bridges. No theorem file or installed dependency pin asserted.')
r['321633'].update(review_depth='old pinned primary selected theorem and conjecture passages',disposition='EXCLUDE_RESOLUTION_ALREADY_IN_SOURCE',remaining='No new discovery; source Theorem 1.4 explicitly refutes Conjecture 1.8. Not an independent reproof of the whole construction.',primary_evidence=['https://arxiv.org/html/1105.5490v1 Theorem 1.4 and Conjecture 1.8'])
r['322237'].update(review_depth='old pinned primary definition and conjecture context',disposition='HOLD_SOURCE_FIDELITY_AND_ANALYTIC_DEPENDENCIES',remaining='Source xi is diameter^2*(lambda2-lambda1); record drops diameter factor. Scaling an unnormalized domain would be an uncredited record repair. Intended strict normalized gap remains unproved here; no PDE Lean endpoint.',primary_evidence=['https://arxiv.org/html/1109.4117v1 abstract and Section 1'])
(P/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
inputs=[B/'ledger.json',B/'prior-campaign-context.json',P.parent/'AGENTS.md',P.parent/'ledger.json',P/'reservation.json',O/'literal-records.json',O/'source-provenance.json',O/'pre-reading-checks.json',L/'root-mathdb-breadth-intake-r729/DECISION.md',L/'root-mathdb-breadth-intake-r729/adjudications.json',L/'root-mathdb-breadth-intake-r729/hypothesis-queue.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']+[O/f for f in ['1109.3930v1.html','1109.4117v1.html','1105.5490v1.html']]
bind=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size) for f in inputs]
(P/'immutable-inputs.json').write_text(json.dumps(bind,indent=2)+'\n')
print('Wrote',len(r),'records; primary/context review',sum(x['review_depth']!='literal_cached_record_only' for x in r.values()))
