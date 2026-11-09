#!/usr/bin/env python3
"""Write dispositions.json: one honest compact disposition per reserved ID (50)."""
import json

BASE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'
LANE = BASE + '/lanes/pi-mathdb-primary-qualified-breadth-r335'

rows = [json.loads(l) for l in open(LANE + '/sources/reserved-records.jsonl')]
by_id = {r['mathdb_id']: r['record'] for r in rows}

D = {}
def d(i, cat, reason, evidence=None):
    D[i] = {'mathdb_id': i, 'disposition': cat, 'reason': reason}
    if evidence: D[i]['evidence'] = evidence

# --- 384514 Representative class (Tolsa) ---
d(384514, 'rejected_deep',
  'Asks for a representative subclass of Calderon-Zygmund operators implying L^p(w) bounds for all CZOs via Tolsa\'s theorem; resolving requires new sparse-domination structure theory. No tractable full-scope mechanism at screening.')
# --- 384713 ---
d(384713, 'rejected_deep',
  'Exact extremal numbers ex(n,B_{5,2}), ex(n,B_{6,2}) for all large n is a famous open hypergraph Turan problem; exact determination for fixed books is far beyond screening-level methods.')
# --- 384757 --- proposed with objection
d(384757, 'proposed_with_novelty_objection',
  'Literal statement fully answered negatively by exact counterexample f=(z+5)^3 -> sum b_i A_i = x^2+19x+216 (disc -503; zero real roots by exact Sturm). BUT prior art: Branden-Jochemko disproved Brenti\'s conjecture that the shifted Eulerian transformation A^o (x^n -> x A_n(x)) preserves real-rootedness on real-nonpositive-root polynomials (same hypothesis class), and Athanasiadis (arXiv:2302.00754, JLMS 2025) proved the positive family P_n[x]; the residual delta is a one-line shift. Ranked #3 with recommendation: allocate only if root judges the unshifted-statement counterexample + maximal-positive-cone classification non-derivative.',
  evidence='sources/384757/aimpl-polypartition-p2.html; sources/384757/arxiv-2302.00754-abstract.html; work/verify_384757.py output')
# --- 384786 ---
d(384786, 'rejected_ill_posed_or_fragmentary',
  '"A good way to compute Z(G) for planar/outerplanar G" is not a crisp mathematical target; the natural crisp version (complexity of zero forcing on planar graphs) is a hardness question with no low-hanging mechanism noted.')
# --- 384973 ---
d(384973, 'rejected_deep',
  'Quantum query-complexity question (beating Grover for range-search/threshold). Open-ended; any full-scope answer needs new quantum algorithm or oracle lower bound machinery.')
# --- 384989 ---
d(384989, 'rejected_expensive',
  '"How short can units in Q[x]/(x^312-x^156-1) be" reduces to shortest-vector-type questions in a rank-156 unit lattice; true minimum is SVP-hard territory and any honest computation exceeds fixed caps. Observation retained: alpha (root of x^312-x^156-1) is a unit with house phi^(1/156) ~ 1.00309, and alpha-1 is also a unit (Norm=1).')
# --- 385256 ---
d(385256, 'rejected_deep', 'Centralizers in Artin groups / Euclidean Artin group commutation criterion is an active hard area; no screening-level mechanism.')
# --- 385430 ---
d(385430, 'rejected_deep', 'Donaldson question: smooth solutions of a degenerate PDE on M x [0,1] (Hamilton/Perelman-type equation with lambda>0); deep geometric analysis.')
# --- 385757 ---
d(385757, 'rejected_deep', 'Weil-etale topos cohomology for arithmetic schemes; deep arithmetic geometry, far from low-hanging.')
# --- 385905 ---
d(385905, 'rejected_likely_publicly_subsumed',
  'Literally, pairing-friendly curves of embedding degree k=13 exist by the Cocks-Pinch construction (works for every k, ~2002), so the literal question predates-resolved; the intended question (low rho / efficient families for k=13) requires a large computational search. Neither variant is a low-hanging novel full-scope target.', evidence='Cocks-Pinch, ANTS-VI (2004); standard construction')
# --- 386136 ---
d(386136, 'rejected_deep', 'Nonvanishing proportion of L(1/2, chi_d) weighted twisted sums: deep analytic number theory (moment methods, family laws).')
# --- 386916 ---
d(386916, 'rejected_deep', 'Set-theoretic forcing: model of TP_kappa for all regular kappa in [aleph_2, aleph_{omega^2+2}]; deep consistency machinery.')
# --- 386938 ---
d(386938, 'rejected_ill_posed_or_fragmentary', '"Exhibit a model with 3 phase transitions" for basis-pursuit-type problems is open-ended and not crisply quantified; no decidable exact target.')
# --- 386951 ---
d(386951, 'rejected_deep', 'Short algebraic definition of a tetracategory: a large coherence-data problem; even tricategory definitions run tens of pages.')
# --- 387089 ---
d(387089, 'rejected_deep', 'Kourovka 21.9 (free pro-p F: finite family of open subgroups so that only trivial subgroup is characteristic in each). Screening found no concrete tractable mechanism; characteristic-subgroup structure of free pro-p groups is delicate. Bounded screen only, not exhaustive.')
# --- 387118 ---
d(387118, 'resolved_publicly_reported',
  'Kourovka 21.38 (spread exactly 1): public result record answers affirmatively - an infinite subgroup of Thompson\'s group F (maps with equal endpoint slopes) has spread exactly one; cf. Donoven-Harper "Infinite 3/2-generated groups" Question 2. AI-result registry with unclear confirmation status, so recorded as resolved_publicly_reported rather than cleared; not eligible for credit either way.',
  evidence='sources/387118/nilradical-kourovka-21-38-result.html')
# --- 387184 ---
d(387184, 'rejected_deep', 'Engel-type iterated identities and branch groups torsion conjecture: deep combinatorial group theory.')
# --- 387260 ---
d(387260, 'rejected_deep', 'Algorithm to compute check H^i(boundary G) for word-hyperbolic G (Epstein question): deep computability/topology of boundaries.')
# --- 387818 ---
d(387818, 'rejected_deep', 'gamma = inf M_f/m_f over non-univalent disk functions, known in [e^{pi/2}, e^pi]: classical extremal problem; interval narrowing needs new extremal-function technology.')
# --- 388017 ---
d(388017, 'rejected_deep', 'MaxBis+MinBis = d/2+o(1) for d-regular graphs: deep probabilistic combinatorics (bisection structure of random/regular graphs).')
# --- 388048 ---
d(388048, 'rejected_deep', 'Minimum edge number covering a crossing supermodular function: central EGRES open problem; no screening-level mechanism.')
# --- 388049 ---
d(388049, 'rejected_deep', 'Same as 388048 with non-parallel arcs; deep combinatorial optimization.')
# --- 388058 ---
d(388058, 'rejected_deep', 'beta(f) <= beta*(f)+1 for matroid-representable 2-polymatroid functions: technical submodular conjecture; no concrete tractable mechanism at screening.')
# --- 388076 ---
d(388076, 'rejected_deep', 'Polynomial-time min-edge local connectivity augmentation of fixed-rank hypergraphs: open algorithmic problem of substantial difficulty.')
# --- 388089 ---
d(388089, 'rejected_deep', 'Orientation-compatible w-vertex cover in polynomial time: open combinatorial-optimization question.')
# --- 388096 ---
d(388096, 'rejected_deep', 'Rank-respecting hypergraph augmentation with crossing negamodular R: deep EGRES-type open problem.')
# --- 388108 ---
d(388108, 'rejected_likely_publicly_subsumed',
  'Asks for combinatorial polynomial-time cut-sparsifier-type subgraphs; existence is classical (Benczur-Karger) and deterministic/modern sparsification literature likely subsumes the ask; the residual "combinatorial" requirement is not crisply creditable.')
# --- 388174 ---
d(388174, 'rejected_deep', 'Partition regularity of x^2+y^2=z^2: famous open problem; 2 colors impossible (7825, Heule-Kullmann-Marek); k>=3 open and hard.')
# --- 388256 ---
d(388256, 'rejected_deep', 'Eremenko conjugate-one-point problem (minimum |a|, covering constant ~0.0505): deep complex analysis, long-standing.')
# --- 388257 ---
d(388257, 'rejected_deep', 'Eremenko symmetric-one-point problem: same family, deep.')
# --- 388271 --- proposed
d(388271, 'proposed', 'See proposals.json #2.', evidence='sources/388271/*; work/verify_388271.py')
# --- 388276 ---
d(388276, 'rejected_deep', 'Uniform sampling / counting of simple polygonizations: counting variant is #P-type and open; sampler question open since 1997.')
# --- 388358 ---
d(388358, 'rejected_deep', 'Determine all invariant measures/subsystems of a specific symbolic system from Boyle Section 14: requires deep analysis of an intricate construction; bounded screen did not identify a shortcut.')
# --- 388448 ---
d(388448, 'rejected_deep', 'Good multiple-recurrence sequence a(n) growing faster than polynomials: deep ergodic theory.')
# --- 388622 ---
d(388622, 'rejected_deep', 'Lift-family criterion guaranteeing real Thurston algorithm convergence for periodic/preperiodic kneading data: deep dynamical systems.')
# --- 388623 ---
d(388623, 'rejected_deep', 'Same for arbitrary kneading data: deep.')
# --- 388885 ---
d(388885, 'rejected_ill_posed_or_fragmentary', 'Gromov scalar-curvature question recorded in fragmentary form ("assumptions on pi_1(X) ... for all flat manifolds"); statement incomplete as captured; underlying problem deep.')
# --- 388970 ---
d(388970, 'rejected_ill_posed_or_fragmentary', 'Lens-space Hodge spectra problem list recorded with broken cross-references ("see )"); items deep (isospectral constructions).')
# --- 388984 ---
d(388984, 'rejected_ill_posed_or_fragmentary', 'Statement garbled by figure text ("Compute the number of different types of strata for n points with arbitrary n" + embedded figure labels); not a crisply quantified target as recorded.')
# --- 389046 ---
d(389046, 'rejected_deep', 'General expression for minimum ropelength of arbitrary knots: famous hard problem.')
# --- 389047 ---
d(389047, 'rejected_deep', 'Optimal constant a in L(K) >= a Cr(K)^{3/4}: deep; current bounds far apart.')
# --- 389145 ---
d(389145, 'rejected_deep', 'O10: randomized poly-time factorization reducible to solving x^e = a mod n: open complexity reduction since 1994.')
# --- 389362 ---
d(389362, 'rejected_infeasible_by_design', 'Factor RSA-1024: computationally infeasible by construction; not a mathematical research target under any caps.')
# --- 389505 --- proposed
d(389505, 'proposed', 'See proposals.json #1.', evidence='sources/389505/*; work/verify_389505.py')
# --- 389513 ---
d(389513, 'rejected_deep', 'Uniform expansion bound for k-net graphs in bounded-degree graphs: deep coarse geometry/probability.')
# --- 389527 ---
d(389527, 'rejected_deep', 'Linear finite models / cr-sofic question for vertex-transitive graphs: deep.')
# --- 389560 ---
d(389560, 'rejected_deep', 'Universal resistance bound for finite vertex-transitive graphs (Benjamini-Kozma type): deep; related conjectures open.')
# --- 389569 ---
d(389569, 'rejected_deep', 'Scaling exponent and GH scaling limit of random hierarchical graph: deep fractal-probability problem.')
# --- 389578 ---
d(389578, 'rejected_deep', 'Critical percolation on distributional planar limits: deep; even the statement spans several conjectures.')
# --- 389581 ---
d(389581, 'rejected_deep', 'Joint law of pairwise distances of p sampled Brownian-map points: deep; requires Brownian map machinery beyond caps.')

out = LANE + '/dispositions.json'
ids = [r['mathdb_id'] for r in rows]
res = {'lane': 'pi-mathdb-primary-qualified-breadth-r335',
       'coverage_note': 'all 50 reserved IDs received a literal full-statement screen; dispositions below; metadata tags were not treated as technical review',
       'dispositions': [D[i] for i in ids]}
open(out, 'w').write(json.dumps(res, indent=2) + '\n')
from collections import Counter
print(Counter(v['disposition'] for v in res['dispositions']))
print('total', len(res['dispositions']))
