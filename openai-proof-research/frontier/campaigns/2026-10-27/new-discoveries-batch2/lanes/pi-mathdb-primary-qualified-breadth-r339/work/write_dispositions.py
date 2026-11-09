import json, datetime
from pathlib import Path

R = Path(__file__).resolve().parent.parent
now = datetime.datetime.now(datetime.timezone.utc).isoformat()

recs = [json.loads(s) for s in (R / "sources/reserved-records.jsonl").read_text().splitlines()]
ids = [r["mathdb_id"] for r in recs]
assert len(ids) == 50

# evidence levels:
#  L0 = record statement read literally in bound corpus copy (all 50)
#  L1 = record-level public prior-art check (search snippets / abstracts; NOT proof-body inspection)
#  L2 = body-level source retained in this lane (PDF/HTML bytes hashed)
#  in_lane_control = decisive bounded computation run and retained in this lane (control, not proof, not prior clearance)

FH = "reject_famous_hard_program"
PR = "reject_programmatic_no_mechanism"
RG = "reject_source_gap_statement_incomplete"
RV = "reject_publicly_resolved"
RT = "reject_routine_or_known"
PS = "park_needs_source_review"

D = [
 (389583, FH, "L0", "Sharp vacant-set transition for SRW on uniformly transient transitive graphs (Benjamini). Central deep probability program; transition-window statement involves asymptotic orders over all such graph sequences; no small exact witness or certificate mechanism identified."),
 (389591, FH, "L0", "Explicit limit shape of first-passage percolation / Richardson's model on Z^d. Determining the limit shape explicitly is a classical major open problem even for d=2; no exact certificate."),
 (389660, FH, "L0", "Find a non-trivial knot with trivial Jones polynomial (Ohtsuki Problem 1.1, [188, Problem 1]). Famous open; extensive known obstructions (non-alternating, large crossing number); no low-hanging mechanism."),
 (389718, PR, "L0", "(M. Polyak) Construct a universal finite-type invariant (Kontsevich invariant) of virtual knots. Deep construction program; no concrete full-scope mechanism identified."),
 (389759, PR, "L0", "Compute HQ_2(X) for every connected quandle X. Scope quantifies over an unclassified infinite class (classification of connected quandles itself open); no finite certificate."),
 (389864, PR, "L0", "Surgery formula for the Kuperberg-Thurston invariant / comparison with LMO. Deep 3-manifold invariant program."),
 (390075, FH, "L0", "Distortion of the Schottky locus in A_g (Farb). Deep geometric-group-theoretic problem; no mechanism."),
 (390082, FH, "L0", "Cohomological dimension of the Torelli group I_g, the Johnson kernel K_g, and I_g(k). Famous hard; even lower bounds are hard."),
 (390141, RG, "L0", "Compute phi(g,n) (Korkmaz chapter). phi(g,n) is not defined in the record statement; statement is not self-contained without the Farb volume context. Source gap recorded; no exact scope to verify."),
 (390224, PR, "L0", "Find a substitute for convex cocompactness in higher rank admitting proper Mod_Sigma-actions. Open-ended research program (Anosov/higher-rank Teichmueller territory)."),
 (390254, PR, "L0", "Find a geometric invariant distinguishing components of the four exceptional strata Q(-1,9), Q(-1,3,6), Q(-1,3,3,3), Q(1^2)... (quadratic-differential strata). Research program; no concrete certificate."),
 (390331, FH, "L0", "Is the Torelli group I_g (g>=3) finitely presentable? Famous open (finite generation by Johnson known)."),
 (390339, PR, "L0", "Determine the homomorphisms on H^8(-;Q) among M_3,*, Out F_6, GL(6,Z). Hard specific cohomology computation; no low-hanging certificate."),
 (390342, PR, "L0", "Compute cohomology of Aut(F_n), Out(F_n) with coefficients in various GL(n,Q)-modules. Open-ended program."),
 (390343, PR, "L0", "Triviality of H_*(Aut F_{2g};Q) -> H_*(M_{g,1};Q) and Out F_{2g} -> M_{g,*} maps. Hard homotopy-theoretic question (Wahl's work context)."),
 (392617, PS, "L1+L2", "Askey-Szego problem: classify triples (a,b,c)>0 with 1F2(a;b,c;-x)>0 for all x>0. Substantial public literature touches exactly this: Cho-Chung-Yun, 'Newton diagram of positivity for 1F2' (arXiv:1801.02312, Integral Transforms Spec. Funct. 2018, claims necessary and sufficient conditions/positivity region) and 'Rational extension of the Newton diagram ... and Askey-Szego problem' (arXiv:1805.11855, Constr. Approx. 2019); a formal Correction to the latter was published 2026-08-29 (doi:10.1007/s00365-026-09773-4) and is the MathDB source. Whether the full 3-parameter classification stands after the correction is a body-level question. PARKED for separate source-qualification (abstracts retained; proof bodies not inspected); not low-hanging now. Sources: sources/392617/."),
 (392620, FH, "L0", "Exact value of Grothendieck's constant K_G. Famous hard."),
 (392629, FH, "L0", "Turan's conjecture: H_n is the largest K_5^{(3)}-free 3-uniform hypergraph for even n. Famous hard extremal hypergraph problem (open even asymptotically)."),
 (392840, RV, "L1+L2", "APX-hardness of MIS for axis-parallel d-boxes for every fixed d>=3: publicly resolved by Chlebik & Chlebikova, 'Approximation hardness of optimization problems in intersection graphs of d-dimensional boxes' (SODA 2005): they prove APX-hardness of MIS in d-box graphs for every fixed d>=3, with explicit factor 443/442. Exactly the record's statement (record predates, OWR 2004/28). Post-print extract retained: sources/392840/ (2-page extract)."),
 (392847, RV, "L1", "Hardness of approximating maximum connected hereditary subgraphs: statement is phrased as an established theorem and matches the hereditary-property hardness line (Lund-Yannakakis; Feige, 'The hardness of approximating hereditary properties', ~2006, proving n/(log n)-type and n^{1-eps}-type bounds under 3-SAT subexponential / NP=ZPP assumptions). Record-level match only; body not inspected; no visible residual open scope."),
 (392848, RV, "L1", "Directed hereditary max-subgraph hardness n^{1-eps} unless NP=ZPP: same line; the statement reads as an established theorem (cf. Feige, hereditary properties hardness). Record-level only."),
 (392868, PR, "L0", "Approximation complexity of the Group Connector Problem. Open-ended complexity program; no concrete yes/no with certificate."),
 (392910, PR, "L0", "Extend Khovanskii's upper bound theorem to simplicial spheres / full face-number description / general polytopes. Open research program (parts a,b,c)."),
 (392979, FH, "L0", "Lifting problem for singular integral affine structures on S^2 (24 singular points, K3 fibration). Deep; no small mechanism."),
 (393038, PR, "L0", "Coefficient ring of unstabilized bivariant algebraic K-theory kk^alg. Hard open computation."),
 (393144, FH, "L0", "How far the 0.33p threshold for structural classification of sum-free subsets of GF(p) can be reduced. Active hard additive combinatorics (recent breakthrough-level area)."),
 (393321, FH, "L0", "Minimum area convex universal cover (convex Lebesgue covering problem). Famous hard; best known bounds by incremental constructions."),
 (393327, FH, "L0", "Erdos few-distance sets bound f(E^2;k)=O(k sqrt(log k)): the stated O-bound is a theorem of Guth-Katz (distinct distances), while the exact lattice-optimality reading is famous-hard. Either way not low-hanging; no exact certificate."),
 (393384, RV, "L1", "Explicit two-source extractors at arbitrary constant min-entropy rate: qualitatively resolved by Chattopadhyay-Zuckerman (STOC 2016) and follow-ups (Li; Cohen-Shi), which are explicit poly-time seedless two-source extractors for min-entropy delta*n for every constant delta>0. The record itself notes output/error parameters are unspecified; no exact scope survives for a new theorem."),
 (393509, FH, "L0", "Local structure near multiplicity-two branch points of stable minimal hypersurfaces. Deep geometric measure theory."),
 (393670, RG, "L1", "Polynomial-time separation for the crossing-minimization ILP: the record references 'the report's ILP formulation' without stating the inequalities; OWR 2005/50 full text was not retrievable in this session (extraction returned only the organizers' preface). Statement not self-contained; scope unverifiable from the record. Source gap recorded honestly."),
 (393706, FH, "L0", "Range of L^p-boundedness of the Riesz transform d*Delta^{-1/2} on complete manifolds of infinite measure. Famous hard harmonic analysis; partial results only."),
 (393741, PR, "L0", "Exact Turan numbers ex(n,T_i) for every i>=5 (3-edge i-uniform hypergraphs). Open-ended family; exact determination for all i is a program, no single decisive certificate."),
 (393754, RV, "L1+L2", "T(G)=B(G) a.a.s. for G(n,m), m >= n^{3/2+eps}: resolved by DeMarco-Kahn, 'Mantel's theorem for random graphs' (arXiv:1206.1016; Random Structures Algorithms 2015): t(G)=b(G) w.h.p. for G(n,p) with p > C sqrt(log n)/sqrt(n); m >= n^{3/2+eps} gives p ~ n^{-1/2+eps} which dominates. Abstract retained: sources/393754/."),
 (393755, RV, "L1", "Extremal triangle-free vs bipartite subgraphs range in G(n,m): same DeMarco-Kahn line determines the threshold up to constants (equality for p > C sqrt(log n)/n^{1/2}, tight up to C). Record-level; remaining constant-level refinements are not low-hanging."),
 (393824, RG, "L0", "Precoloring extension for planar bipartite graphs with d(W)>=5: the record asks 'what happens for the problem ... when d(W) >= 5' - no exact yes/no claim to prove or refute; scope too vague for an exact hypothesis."),
 (393825, RV, "L1", "NC (1-eps)-approximation for maximum-weight matching: publicly resolved by Hougardy & Vinkemeier, 'Approximating weighted matchings in parallel' (Inform. Process. Lett. 2006, doi:10.1016/j.ipl.2006.09.003): an NC approximation algorithm for weighted matching with ratio (1-eps), improving the previous (1/2-eps). Exactly the record's statement."),
 (393882, PR, "L0", "Unified integrable discretization of CMC surfaces in all space forms with Baechlund/Lawson analogues. Research program in discrete differential geometry."),
 (393907, "brief", "L0+in_lane_control", "PROMOTED: every (p,q)-core contained in the maximal (p,q)-core kappa_pq. Decisive bounded computation run in this lane (work/verify_core_containment.py, sources/core-containment-calculation.json): for all coprime p<q<=13 with kappa_pq<=45, all (p,q)-cores (partitions of size<=45) enumerated; counts match Anderson's formula exactly (validates the core criterion), max-size matches (p^2-1)(q^2-1)/24 (validates against Olsson-Stanton), and every core is contained in the max core. No counterexample. See proposals.json."),
 (394040, PR, "L1", "Explicit isomorphism problem for Big Ree groups 2F4(q) in GL(26,q). Constructive recognition exists for small Ree 2G2(q) (arXiv:1206.0411); none found publicly for 2F4. A correct algorithm + proof + implementation is a substantial CGT project (involution centralizers, generalized octagon); not low-hanging. Flagged for a future dedicated lane."),
 (394209, "brief", "L0+L2", "PROMOTED: exact P_l(n) = C(2l,l) 2^{n-2l} for the remaining small l. Alon-Lubetzky (arXiv math/0608173, Combinatorica 2009) prove it for all l >= l0 (unspecified) and characterize extremal pairs; l=1 follows from the Frankl-Rodl bound 2^{n-1}; l=2 by Keevash-Sudakov; the finite remaining range (l=3,4,...) is explicitly left open in the paper. Full PDF retained: sources/394209/. See proposals.json."),
 (394345, RV, "L0", "Classical Littlewood-Offord maximum: the record's own statement says the question is solved - the maximum of |N_r| over a_i >= 1 equals the sum of the floor(r)+1 largest binomial coefficients of order n (classical Erdos 1945). Nothing to do."),
 (394349, PR, "L0", "Monochromatic components xi_k(T_n^d) = Theta(n^{d-k+1}) for triangulated grids, all fixed d and k=3..d-1. Program-level conjecture; no small certificate."),
 (394378, RV, "L0", "Shared values of f and f': the record's own statement says the report answers it - least cardinality is 3, best possible. Nothing to do."),
 (394417, RT, "L0", "Adaptive fixed-degree Bernstein positivity certificates: existence follows from a standard continuity argument (Bernstein coefficients of P of degree p on [a,a+h] converge uniformly to values near P(a)>0 as h->0), and subdivision-based positivity certification is classical in computer-aided polynomial verification. High risk of routine-adaptation credit; no novel mechanism identified."),
 (394473, FH, "L0", "Game chromatic index chi'_g(G) <= (2-eps) Delta(G) for all non-empty graphs. Open graph-coloring-game problem; hard."),
 (394494, RV, "L0+L1", "Four-integer sets D with xy+x+y a perfect square for all distinct pairs: substitute u=x+1; u_i u_j - 1 must be a square for all pairs (a D(-1)-quadruple in Z). Mixed signs impossible (u_i u_j - 1 < 0), u=0 impossible, so all u_i>0 or all u_i<0; the all-negative case is the negation mirror of the positive case, which is the classical D(-1)-quadruple conjecture - resolved: Bonciocat-Cipu-Mignotte, 'There is no Diophantine D(-1)-quadruple' (arXiv:2010.09200, 2020; J. London Math. Soc., doi:10.1112/jlms.12507), which itself covers integer entries. Abstract retained: sources/394494/."),
 (394646, RG, "L0", "Lipschitz stability of the median interpolating subdivision scheme: the scheme is not defined in the record statement; stability of nonlinear median-type schemes is scheme-specific. Source gap recorded; no exact scope."),
 (394717, FH, "L0", "Mass-dependence of the limiting variance of the tagged particle in the 1-d Rayleigh gas. Hard kinetic-theory scaling-limit problem."),
 (394837, RG, "L0", "Minimal-degree families of rational curves on rational surfaces: 'as small as possible' is not an exact claim; open-ended birational-geometry program."),
]

assert len(D) == 50
assert [x[0] for x in D] == ids

out = {
 "lane": "pi-mathdb-primary-qualified-breadth-r339",
 "generated_at": now,
 "screened_ids": ids,
 "screening_scope": "literal full statement of all 50 records read from bound immutable corpus copy sources/reserved-records.jsonl; compact honest dispositions; metadata tags not treated as technical review",
 "dedup": "zero overlap with the 283 prior reported reviews (r338 coverage-delta) and with root-mathdb-accepted-exclusions-r304 accepted-exclusions/historical-dispositions, verified after binding",
 "dispositions": [
   {"mathdb_id": i, "title": next(r["title"] for r in recs if r["mathdb_id"] == i),
    "disposition": d, "evidence_level": lv, "note": n}
   for (i, d, lv, n) in D
 ],
 "counts": {
   "total": 50,
   "brief": 2,
   "reject_famous_hard_program": sum(1 for x in D if x[1] == FH),
   "reject_programmatic_no_mechanism": sum(1 for x in D if x[1] == PR),
   "reject_source_gap_statement_incomplete": sum(1 for x in D if x[1] == RG),
   "reject_publicly_resolved": sum(1 for x in D if x[1] == RV),
   "reject_routine_or_known": sum(1 for x in D if x[1] == RT),
   "park_needs_source_review": sum(1 for x in D if x[1] == PS),
 },
}
(R / "dispositions.json").write_text(json.dumps(out, indent=1) + "\n")
print("dispositions written:", out["counts"])
