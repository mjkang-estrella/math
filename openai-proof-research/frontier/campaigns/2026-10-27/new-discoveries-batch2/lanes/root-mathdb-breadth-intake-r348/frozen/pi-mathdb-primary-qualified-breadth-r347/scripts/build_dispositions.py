#!/usr/bin/env python3
"""Build dispositions.json for pi-mathdb-primary-qualified-breadth-r347.
Exactly the 50 reserved ids of root-mathdb-c5-intake-r346/reserved-ids.json."""
import json

RESERVED = json.load(open("frozen/root-mathdb-c5-intake-r346/reserved-ids.json"))["ids"]
assert len(RESERVED) == 50

R = "reject_publicly_resolved"
F = "reject_famous_hard"
D = "reject_deep"
P = "reject_programmatic_algorithmic"
V = "reject_vague_or_open_ended"
S = "reject_statement_degenerate"

EV_CACHE = "cached_full_statement_read"
EV_PUB = "cached_full_statement_read + public_abstract_or_search"
EV_PDF = "cached_full_statement_read + retained_primary_pdf_body_checked"

D_ = {}

def add(i, disp, ev, note):
    assert i not in D_, i
    D_[i] = {"disposition": disp, "evidence_level": ev, "note": note}

# ---------------- publicly resolved (5) ----------------
add(398792, R, EV_PDF,
    "Record is the Engbers-Galvin conjecture verbatim. Resolved by Gan-Loh-Sudakov, "
    "'Maximizing the number of independent sets of a fixed size' (arXiv:1311.4147; Combin. "
    "Probab. Comput. 24 (2015) 521-527), Theorem 1.2, retained and body-checked here: 'Let "
    "delta <= n/2. For every t >= 3, every n-vertex graph G with minimum degree at least delta "
    "satisfies i_t(G) <= i_t(K_{delta,n-delta}), and when t <= delta, K_{delta,n-delta} is the "
    "unique extremal graph.' Sources: arxiv.org/abs/1311.4147; doi 10.1017/S0963548314000546.")
add(399772, R, EV_PUB,
    "Linear stability of the elliptic Lagrangian equilateral-triangle (homographic) solutions "
    "as a function of mass parameter and eccentricity was determined by Danby (Astron. J. 69 "
    "(1964) 165-172 and 294-296) and completely by G. E. Roberts, 'Linear Stability of the "
    "Elliptic Lagrangian Triangle Solutions in the Three-Body Problem' (J. Dynam. Differential "
    "Equations, DOI 10.1006/jdeq.2001.4089; identified via public search 2026-10-31). "
    "ScienceDirect body excluded by access policy; abstract-level identification only, but "
    "this 2-parameter determination is a settled classical problem, not an open record.")
add(400244, R, EV_PDF,
    "Alon's problem resolved. Decisive: 'Quadratic-size Random Permutations are Universal' "
    "(arXiv:2610.13530, 2026-10), retained and body-checked: 'We prove that a uniformly random "
    "permutation of length 32n^2 is n-universal with probability at least 1-exp(-cn/log n) ... "
    "resolves an open problem of Alon' (the paper itself credits the proof to GPT-6 Pro). "
    "32k^2 <= 1000k^2, so f(k) <= 1000k^2 holds. Prior progress: He, 'Universality of random "
    "permutations' (arXiv:1911.12878, n = 2000k^2 log log k) and He-Kwan. The record's model "
    "(n distinct reals i.i.d. uniform) is a uniformly random n-permutation, matching.")
add(400776, R, EV_PDF,
    "Record is the finite (gamma>0, n>=n_0) form of the theorem of "
    "Reiher-Roedl-Rucinski-Schacht-Szemeredi, 'Minimum vertex degree condition for tight "
    "Hamiltonian cycles in 3-uniform hypergraphs' (arXiv:1611.03118; Proc. London Math. Soc. "
    "2019), retained and body-checked: 'every 3-uniform hypergraph with n vertices and minimum "
    "vertex degree at least (5/9+o(1))C(n,2) contains a tight Hamiltonian cycle', with "
    "asymptotically optimal lower-bound constructions. For any fixed gamma>0 the record's "
    "(5/9+gamma)n^2/2 >= (5/9+o(1))C(n,2) for all large n, so the record follows.")
add(400867, R, EV_PDF,
    "The record's concrete question is settled: A(4, arccos(1/3)) = 14, proved by T. S. Tomar, "
    "'Spherical codes with minimal angle arccos(1/3) in dimensions four, five and six' (Zenodo "
    "DOI 10.5281/zenodo.23603434, dated 2026-10-23), retained and body-checked: 'We prove "
    "A(4, arccos 1/3) = 14, A(5, arccos 1/3) <= 22 and A(6, arccos 1/3) <= 34. The previous "
    "upper bounds were 15, 23 and 35.' Certificates are exact rational solutions of the second "
    "Lasserre level (de Laat-Leijenhorst formulation), superseding the 16/15 two-/three-point "
    "bounds quoted in the record; the 14-point construction was already known.")

# ---------------- famous-hard (11) ----------------
add(398321, F, EV_CACHE,
    "Optimality of the ~43.52% independent-set density of local algorithms on large-girth "
    "d-regular graphs. Proving optimality of a specific local-algorithm value needs new "
    "lower-bound machinery for local algorithms (cavity/entropy scale); no small exact "
    "mechanism. No public resolution found in current bounded search; no exhaustive clearance "
    "claimed.")
add(398322, F, EV_CACHE,
    "Infinite family of nonbipartite d-regular Ramanujan graphs for every d: famous open "
    "construction problem (the all-d bipartite case is the Marcus-Spielman-Srivastava "
    "theorem; nonbipartite every-d remains open). No small mechanism.")
add(398403, F, EV_CACHE,
    "Global minimum ropelength R_g of non-trivial knots vs 24: known rigorous lower bounds are "
    "near 15.7 and smallest known explicit ropelengths (trefoil ~32.8 numerically) sit above "
    "24; deciding R_g <= 24 requires hard certified computational geometry on both sides.")
add(398482, F, EV_CACHE,
    "Minkowski's conjecture M(K) <= 2^{-n} sqrt(d_K) for totally real K of degree n: famous "
    "open in general (known only up to small n). No small mechanism.")
add(399925, F, EV_CACHE,
    "Ramos' conjecture Delta(j,k) = ceil((2^k-1)j/k): famous open mass-partition problem; even "
    "small cases are delicate. Deep topological/combinatorial machinery required.")
add(399926, F, EV_CACHE,
    "Exact values Delta(2^t+1, 2) = 3*2^{t-1}+2: special case of the same famous-hard family; "
    "exact determination needs new lower- and upper-bound technology.")
add(399983, F, EV_CACHE,
    "Explicit family of 2 log n-Ramsey graphs on n vertices matching Erdos 1947: famous open "
    "explicit-construction problem.")
add(400257, F, EV_CACHE,
    "Turan density pi(K_4^{(3)}): famous open hypergraph Turan problem (bounds 5/9 <= pi <= "
    "0.5616 are in the statement itself).")
add(400321, F, EV_CACHE,
    "Rationality of a generic cubic fourfold: famous open algebraic-geometry problem.")
add(400795, F, EV_CACHE,
    "Slicing (hyperplane) problem: dimension-independent max hyperplane-section bound; famous "
    "open convex geometry.")
add(401011, F, EV_CACHE,
    "Finiteness of optimal points in subvarieties of mixed Shimura varieties: "
    "Zilber-Pink-scale diophantine problem; famous-hard.")

# ---------------- deep (16) ----------------
add(398348, D, EV_CACHE,
    "Existence, for every k>=4, of a k-graph H with H-free k-graphs whose largest clique or "
    "independent set is O(c_k r_k^{-1}(n)). Research-scale extremal hypergraph problem; major "
    "related progress exists (Mubayi-Suk, 'The Erdos-Hajnal hypergraph Ramsey problem', "
    "arXiv:1602.08716: correct tower growth for r_k(k+1,t;n) in almost all cases) but the "
    "record's specific statement was not cleared by current bounded search. No small "
    "mechanism; no exhaustive clearance claimed.")
add(398519, D, EV_CACHE,
    "Totaro's conjecture on d_0(CH^*G) as a module over the Steenrod algebra: deep algebraic "
    "topology; known cases require substantial computation. No small mechanism.")
add(398782, D, EV_CACHE,
    "Inducibility of the 4-vertex path P4: open since Exoo's 1986 construction; left open by "
    "the 4-vertex-graph papers ('The inducibility of graphs on four vertices', "
    "arXiv:1109.1592; 'still not completely determined' per JCTB 2018). Flag-algebra + "
    "stability scale; no small mechanism; no resolution found in current search.")
add(398788, D, EV_CACHE,
    "Bondy's conjecture (every cycle of a vertex-3-connected graph with |G|>=2d, delta>=d is "
    "a symmetric difference of circuits of length >= 2d-1): deep graph-structure problem with "
    "partial results only.")
add(398797, D, EV_CACHE,
    "Every cycle in an odd-order min-degree ceil(n/2) graph is a symmetric difference of "
    "Hamilton circuits: Dirac-threshold structure problem; known methods give partial cases.")
add(398799, D, EV_CACHE,
    "Spanning copy of 'C_n^2 with alternate periphery edges deleted until exactly three "
    "consecutive degree-4 vertices remain' in every odd n>=7 graph of min degree ceil(n/2): "
    "absorption/embedding scale; a hard spanning-subgraph theorem, no short mechanism.")
add(399274, D, EV_CACHE,
    "Existence of C with the Ck^9 distinct-circumradii selection property: Erdos-Szekeres-type "
    "selection with a specific exponent; deep.")
add(399275, D, EV_CACHE,
    "Existence of n_k forcing k points with all triple circumradii distinct: Ramsey-type "
    "selection; deep (companion of 399274).")
add(400177, D, EV_PUB,
    "Does min degree >= n force an immersion of K_n? Open. Best known: min degree >= 11t+7 "
    "forces a strong K_t immersion (Dvorak-Yepremyan, 'Complete graph immersions and minimum "
    "degree', arXiv:1512.00513, J. Graph Theory 88 (2018) 211-221, retained and body-checked "
    "via abstract page). Gap 11n+7 vs n; no small mechanism; complete bipartites K_{n,n} DO "
    "contain K_n immersions (round-robin lifts), so no easy counterexample either.")
add(400276, D, EV_CACHE,
    "Deciding IH^{10}(A_4^Sat,Q) = R_4^{10} or a proper inclusion: deep arithmetic geometry "
    "(tautological rings of A_4).")
add(400566, D, EV_PDF,
    "house-Northcott finiteness for O_{Q_tr^{(d)}}. d=1 trivial; d=2 YES via Bombieri-Zannier: "
    "Q_ab^{(2)} has property (N) (Widmer, arXiv:1205.2491, retained and body-checked: "
    "Bombieri-Zannier proved Q_ab^{(d)} has (N); subfields inherit (N); h(alpha) <= "
    "house(alpha) gives finiteness of {house<X}). For d >= 3 the underlying Bombieri-Zannier "
    "question for K^{(d)} is OPEN. CRITICAL registry fact: arXiv:2605.27232v1 (2026) claiming "
    "(N) for all degree-bounded composites was WITHDRAWN (v2, 2026-06-02: 'There is a mistake "
    "in page 4 line 5...'), so it is NOT a resolution. Full scope (all d) unknown -> deep.")
add(400774, D, EV_PDF,
    "Davies' strengthened conjectures: ratio >= 4/3 for all triangle-free G plus alpha/E >= "
    "2-o_d(1) at minimum degree d. Open; the 4/3 core is Davies' Conjecture 1 (see 400775) "
    "and the min-degree part is an open Shearer-type refinement. Ramsey-theoretically loaded: "
    "per Davies, any constant > 1 would improve the R(3,k) bound. No small mechanism.")
add(400775, D, EV_PDF,
    "Verbatim Davies' Conjecture 1 (arXiv:1606.01043, retained and body-checked): 'For every "
    "triangle-free graph G, alpha(G)/alpha_G(1) >= 4/3'; author's note: smallest ratio found "
    "is 197136/137585 = 1.43283... on the R(3,9)>=36 graph, and any constant > 1 would "
    "improve R(3,k). Open since 2016. RUN HERE (bounded, exact): exhaustive labeled "
    "triangle-free graphs on n<=7 vertices (2+7+41+388+5789+133501 = 139,728 graphs; "
    "scripts/triangle_free_ratio_small_n.py, work/triangle_free_ratio_small_n.out): min "
    "alpha/E = 1.466667 (=C5, n=5) and ALL ratios >= 4/3. Finite evidence only; does NOT "
    "clear the conjecture. A full-scope proof needs new hard-core/entropy machinery beyond "
    "short-proof scale; not briefed.")
add(400780, D, EV_CACHE,
    "Characterize F admitting Delta-regular G with d_x(G,F) < (1-eps) d_x(K_Delta,F): the "
    "record itself states this is open even for F=C_4. Deep generalized-Turan program.")
add(400929, D, EV_CACHE,
    "Computational complexity of finding a colorful Caratheodory choice: open per the primary "
    "literature (PPAD formulation: 'The Rainbow at the End of the Line', arXiv:1608.01921; "
    "'the computational complexity ... is unknown', SOCG 2015 / DCG 2018 line). "
    "Complexity-separation scale; no resolution found in current search.")
add(400976, D, EV_CACHE,
    "Characters of indecomposable tilting GL_m-modules / all symmetric-group decomposition "
    "numbers for <= m-row partitions: famous-deep modular representation theory.")

# ---------------- programmatic / algorithmic (6) ----------------
add(398566, P, EV_CACHE,
    "Average-polynomial-time zeta-function computation for curves: algorithm-design program; "
    "no crisp mathematical conjecture to prove.")
add(399745, P, EV_CACHE,
    "Deterministic poly(g, log p) zeta of hyperelliptic curves: algorithmic open problem; the "
    "deliverable is an algorithm and complexity analysis, not a proof.")
add(400230, P, EV_CACHE,
    "Effective Shafarevich for principally polarized abelian surfaces: effective-computation "
    "program; no crisp conjecture.")
add(400231, P, EV_CACHE,
    "Effective Shafarevich for genus-2 Jacobians: same programmatic nature as 400230.")
add(400616, P, EV_CACHE,
    "Construct a Sharbly-type resolution and codimension-one algorithm for Sp: "
    "research-program construction request.")
add(400621, P, EV_CACHE,
    "Compute Hecke operators for all arithmetic groups with computable cohomology: "
    "software/algorithm program.")

# ---------------- vague / open-ended (10) ----------------
add(398297, V, EV_CACHE,
    "'Find explicit closed formulas for the kernel K_a for arbitrary real a>0, beyond the "
    "cases where closed forms are already known': open-ended research request, no crisp "
    "conjecture or falsifiable exact statement.")
add(398547, V, EV_CACHE,
    "'Find conditions on f under which gamma(E) >= c log lambda for all E, lambda large': "
    "open-ended research program (quasiperiodic cocycles); conditions unspecified, any sound "
    "condition would qualify - not a precise conjecture.")
add(398678, V, EV_CACHE,
    "Polynomial tractability of integration on permutation-invariant subspaces 'described in "
    "the report': definitions live in an inaccessible report; open-ended IBC characterization "
    "program, no self-contained exact statement.")
add(399002, V, EV_CACHE,
    "Maximizer of the largest zero of the mixed characteristic polynomial 'in Problem 0.4' of "
    "an unspecified report: statement not self-contained (undefined Lambda^+ and context); "
    "also deep.")
add(399464, V, EV_CACHE,
    "'Find a universal method for obtaining general matrix-valued solutions K(u) of the "
    "reflection equations': open-ended integrable-systems program; no crisp conjecture.")
add(399956, V, EV_CACHE,
    "'How can one find a geometric description of the non-symplectic involution on S^[2]?': "
    "open-ended research question, no exact statement to prove or refute.")
add(399965, V, EV_CACHE,
    "Multi-part question about exceptional moduli-map images for nodal curves on K3 surfaces, "
    "referencing an inaccessible 'Theorem 17' and 'expectation (1)': not self-contained; "
    "open-ended.")
add(400374, V, EV_CACHE,
    "'Explicitly compute the differential and the relations R' in an exact sequence involving "
    "K_2(E) and St_3(k)/R for arbitrary fields: open-ended computation request with scope "
    "defined by an inaccessible report.")
add(400863, V, EV_CACHE,
    "Truncated moment problem for QFT functionals on the Borchers-Uhlmann algebra 'subject to "
    "the stated quantum-field-theoretic constraints' stated only in the report: not "
    "self-contained.")
add(400954, V, EV_CACHE,
    "'Study Sec_k(G_{n,d}) for all k,n,d: determine its dimension, degree, and defining "
    "equations': broad algebraic-geometry research program, not a single exact statement.")

# ---------------- statement-degenerate (2) ----------------
add(398914, S, EV_CACHE,
    "Literal reading: a line arrangement in general position has NO multiple points, so it is "
    "vacuously stable (mu(x) < 2n/3 for every multiple point) with total multiplicity 0. "
    "Hence the literal minimum is 0 and the record as stated is trivial; the intended "
    "nontrivial version (e.g. arrangements with no ordinary points, or quasi-simple "
    "arrangements) is missing from the record. Decisive small exact observation; no mechanism "
    "for the intended version is available from the record text, so no brief.")
add(400796, S, EV_CACHE,
    "Literal reading: c(d) = min_{K subset L} E V(P^K_{d+1}) / E V(P^L_{d+1}) over convex "
    "bodies with no volume normalization. Take K_eps = [0,1]^(d-1)x[0,eps] subset L = [0,1]^d: "
    "the slab 0<=x_d<=eps is convex, so the hull of d+1 points of K_eps lies in it and "
    "V_d(hull) <= eps * (bounded projection volume), giving E V(P^K_eps) = O(eps) -> 0 while "
    "E V(P^L_{d+1}) > 0 is fixed. Hence the literal infimum is 0 (not attained) and no "
    "positive lower bound exists: the comparison constant is degenerate without the intended "
    "normalization. RUN HERE: numeric illustration work/comparison_constant_thin_demo.out "
    "(ratio ~ eps, d=3). No mechanism for the intended version; no brief.")

assert set(D_.keys()) == set(RESERVED), set(RESERVED) ^ set(D_.keys())

counts = {}
for v in D_.values():
    counts[v["disposition"]] = counts.get(v["disposition"], 0) + 1

doc = {
    "lane": "pi-mathdb-primary-qualified-breadth-r347",
    "scope": ("All 50 MathDB records reserved in root-mathdb-c5-intake-r346/reserved-ids.json "
              "received a compact literal-statement disposition. Every full literal statement was "
              "read from work/reserved-records.json, extracted from the hash-verified corpus "
              "frozen/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0001..0020.jsonl. "
              "Evidence levels: cached_full_statement_read = literal statement read from the verified "
              "corpus extract; public_abstract_or_search = lawful public HTTP/search verification "
              "(abstract/answer-mode text, NOT proof-body reading); retained_primary_pdf_body_checked "
              "= actual primary PDF retained in sources/ with key statement extracted to "
              "work/extracts/ and read. Metadata tags were never used as review. No claim of "
              "exhaustive current-registry clearance is made anywhere; current-registry gaps are "
              "stated in notes and SUMMARY."),
    "dispositions": {str(k): D_[k] for k in sorted(D_.keys())},
    "counts": {
        "total": 50,
        "qualified_briefs": 0,
        "reject_publicly_resolved": counts.get(R, 0),
        "reject_famous_hard": counts.get(F, 0),
        "reject_deep": counts.get(D, 0),
        "reject_programmatic_algorithmic": counts.get(P, 0),
        "reject_vague_or_open_ended": counts.get(V, 0),
        "reject_statement_degenerate": counts.get(S, 0),
    },
}
assert sum(counts.values()) == 50
json.dump(doc, open("dispositions.json", "w"), indent=1)
print("dispositions.json written:", doc["counts"])
