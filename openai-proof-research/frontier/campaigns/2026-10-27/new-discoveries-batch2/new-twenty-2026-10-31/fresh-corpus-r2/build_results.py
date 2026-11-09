from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
reasons={
322439:'Uniform Pachner simplification-height assertion over all one-vertex sphere triangulations. No concrete local replacement mechanism or bounded obstruction certificate; finite low-level enumeration cannot settle the universal bound.',
322472:'Needs a quasipolynomial chromatic/biclique-partition separation uniformly in k; no new graph-product or communication lower-bound construction. Do not exploit ambiguity in the constant quantifier.',
322573:'Uniform equivariant obstruction over all binary weights m and e; no tractable cohomological nonexistence certificate or new generalized cohomology calculation.',
322713:'Existence of a planar graph forcing four bends needs a universal obstruction to all three-bend EPG representations; no finite graph plus sound representation obstruction located.',
322756:'Cycle-space spanning by all long circuits in every dense 3-connected graph. Known extra-assumption cases do not give the entire Hamiltonian range; no exchange mechanism closing that range.',
322768:'Exact simplification is not a defined mathematical class; a division identity would address wording rather than a substantive impossibility theorem. Excluded as an ill-specified target, no discovery claim.',
322778:'Would require a billiard reflection construction outside the hull of closest-point pairs for admissible obstacles, or a general reflection/convexity argument. No exact trajectory and obstacle certificate; index typo is not a result.',
322833:'Identifies two highly structured filtrations for every coprime pair; no geometric representation-theoretic bridge. Restricted torus-knot parameters would not meet full scope.',
322907:'Uniform square-root agreement subtree lower bound for arbitrarily tall balanced binary trees. A small recursive leaf permutation would need a proved agreement-number recurrence. No such new construction.',
322928:'Rank bound for arbitrary tree-automatic well-founded partial orders, not only forests/wulpos; finite automata examples alone cannot certify the transfinite bound. No rank decomposition or exact counterexample.',
322981:'Full Atiyah-bundle mass identity requires automorphism and section-count semantics; printed rightmost expression also appears offset at n=0. Endpoint correction would not be discovery. No substantive uniform new mass formula proved.',
323025:'Requires realizing every knot of each bridge index in two precise triangulated Morse configurations. No uniform triangulation/Morse construction; fixed knots are insufficient.',
323062:'Deep fallback investigated: original recurrence and 2019 single-heap proof bodies reviewed. Two-heap greedy rearrangement lemma remains unproved; finite recurrence probe does not settle it. Bare all-n failures are excluded wording corrections.',
323084:'Asymptotic sharp weighted cover time depends on the original random-graph/locally-tree-like hypotheses suppressed in the record. No new hitting-time estimate; unrestricted-graph counterexamples would not establish intended source scope.',
323097:'Literal record itself states that the cited paper proves exactly the log-supermodular Bethe lower bound. Exclude known theorem; this is cached-statement evidence, not fresh proof-body review.',
323176:'Uniform prime GAP existence at the claimed least starting prime is a simultaneous-prime-values problem. Domain/ratio degeneracies are not eligible counterexamples; no unconditional all-k construction.',
323177:'Same source GAP family as323176, with simultaneous least ratio as well. No uniform simultaneous primality theorem or admissible obstruction. No separate credit for a nearby parameter variant.',
323235:'Normal order of iterated Carmichael depth requires a density-one distribution theorem, not finitely many factorizations or a Pratt-tree heuristic. No tractable full mechanism.',
323277:'Sharp norm determination in all dimensions n>1 and allowed weights; existing two-sided bounds do not identify the maximizer. No new integral reduction with globally sharp estimate.',
323289:'Primary source v1 already reports capacity12 for n=14, while tau(14)=4 and a(14)=16. Record conjecture not located in that source. Known-source refutation/fidelity issue, zero credit.',
323293:'Exact same determinant inequality and sharpness proved in Minghua Lin arXiv1212.1934v1 (Dec2012). Original statement and solution proof read. Excluded known result.',
323318:'Uniform complexity criterion for all Specht modules needs the missing non-pxp direction; no support-variety mechanism. One partition or characteristic would be only a parameter case.',
323322:'Uniform extremal mean-distance minus proximity problem. Need a graph transformation preserving/improving the objective and reducing to three balanced arms; no new transformation proof or exact counterexample.',
323323:'Parity-dependent sharp remoteness-radius lower bound over all connected graphs. No all-n layer inequality or exact family breaking it; checking cycles only repeats the stated equality examples.',
323341:'Equality of Chern slant-product homomorphisms requires constructing the analytic and comparison bundles and identifying integral classes; no finite certificate or new homotopy mechanism.',
323348:'Bosonic binding threshold monotonicity over all particle numbers; asymptotic convergence and N=1,2 data do not imply monotonicity. No variational comparison between consecutive N.',
323363:'Representation constituent occurrence for all discriminants of a prescribed type. Low Fourier-coefficient checks do not prove positivity in every discriminant. No uniform modular/representation bound.',
323367:'Finite-degree difference preservation criterion could admit a discrete convolution proof or finite polynomial counterexample, but no primary-body review performed here. Park full criterion; do not claim current resolution status.',
323371:'Uniform independent-set level bound for all delta,n,t≥3. No new compression or degree-reduction induction; known/public status not cleared. Small t or delta alone would not meet scope.',
323431:'Full rational Halperin–Carlsson rank conjecture; no new Sullivan-model dimension bound. Formalizing classical special cases cannot be counted.',
323476:'Literal record explicitly says the cited source proves every admissible metric/upper-dimension pair. Excluded known theorem; original construction body not reviewed here.',
323482:'Local linear-forest cover bound for all maximum degrees. Needs a cover construction with vertex congestion ceil((Delta+1)/2); no new orientation/path split mechanism.',
323483:'Every planar graph needs an injective track cover with local multiplicity3. Existing bipartite/treewidth3 cases do not resolve full scope; no general embedding/cover construction.',
323489:'Full crossing-vector extremum includes arbitrary dimension and thresholds; equivalent to the main all-equal-threshold conjecture. No novel compression argument or finite excess family.',
323492:'Non-separated interval-censoring MLE limit law requires a process approximation and localization argument; malformed diagonal distribution assumptions would yield wording corrections. No full asymptotic proof.',
323512:'All three conjectures admit an ordinary proof by augmentation plus a characteristic-family Burnside idempotent; two full constructions in DEVIATION-PROOF.md. Routine source-machinery corollary concern; no literal Lean packet or novelty clearance. Zero credit.',
323552:'Polylog approximate-rank/randomized communication bound needs an all-size separation or protocol. No new such family. Possible public refutation requires primary comparison before claiming known status; literal review only.',
323636:'Uniform spectral index scaling for cubic Julia-set Laplacians requires a spectral renormalization/multiplicity theorem. No certified full spectral model; endpoint lambda0 behavior not counted.',
323665:'Total independent-set bound at every n≥2delta needs a uniform extremal graph argument, not a count for fixed n. No new compression proof; public resolution status not certified.',
323753:'Polynomial algebra structure for all actual multiple zeta values requires algebraic independence beyond formal/motivic substitutes. No new independence mechanism; changing to motivic MZVs would change the endpoint.'}
assert len(reasons)==40
rows=json.loads((p/'literal-records.json').read_text());out={}
deep={323289:('torus.txt','Sections2–3; constructions and Hilbert-series calculation discussion'),323293:('determinant.txt','Conjecture8.3; Lin theorem2 and full proof in determinant-solution.txt'),323512:('deviation.txt','Equations5.15–5.22, proofs5.24/5.28, Conjectures5.31 and examples'),323062:('scoring.txt','Definitions3.1–3.2, Theorem3.1 proof, Lemma3.1 proof, Conjectures3.1–3.3; cumulative.txt Sections2–3 proofs')}
for x in rows:
 i=x['id'];r=x['record'];out[str(i)]={'mathdb_id':i,'title':r['title'],'literal_statement_reviewed':True,'primary_statement_reviewed':i in deep,'primary_proof_body_reviewed':i in deep,'review_depth':'primary_and_relevant_proof_bodies' if i in deep else 'immutable_literal_statement_only','chunk':x['chunk'],'line':x['line'],'chunk_sha256':x['chunk_sha256'],'line_sha256':x['line_sha256'],'canonical_url':r['canonical_url'],'original_source_url':r['source_url'],'status':('excluded_known_or_fidelity' if i in [323289,323293,323097,323476] else 'ordinary_full_proof_routine_credit_hold' if i==323512 else 'parked_precise_proof_obstruction' if i==323062 else 'parked_literal_screen'),'disposition':reasons[i],'accepted_credit':0,'lean_complete':False,'novelty_cleared':False}
 if i in deep:out[str(i)]['primary_review']={'file':deep[i][0],'scope':deep[i][1]}
(p/'results.json').write_text(json.dumps(out,indent=2))
print('40 keyed records; primary/body review4; literal-only36; accepted0; complete Lean0')
