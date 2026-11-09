# Build results.json: exactly 20 ID-keyed entries with provenance, receipts, review depth and outcome.
import json, hashlib, pathlib
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text()); res=json.loads((D/'reservation.json').read_text())
def rec(name):
    p=D/'sources'/(name+'.receipt.json')
    return json.loads(p.read_text()) if p.exists() else None
def txt_hash(a):
    p=D/'sources'/(a+'.txt'); return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
H="history-matches.txt (bounded grep of prose/review/results/ledger files across new-discoveries-batch2) plus a whole-word ID grep across frontier/: every hit was a reservation list, sitemap index or digit substring of a hash or byte count. No earlier exact-ID technical review or exclusion found. Inherited protected families retained."
E={}
def add(i,outcome,depth,attempts,coverage,remaining,extra_receipts=()):
    E[str(i)]=dict(outcome=outcome,review_depth=depth,mathematical_attempts=attempts,coverage_artifact=coverage,remaining_lemmas_or_reason=remaining,extra_receipts=list(extra_receipts))
add(338214,'full proof found; routine classical bridge (Edmonds covering theorem plus Wei duality); expected zero credit; no Lean',
 'Source Definitions 1, 3, 6, 9, Theorem 2 and Conjecture 1 read (1801.04923v2). Companion 1712.03898v4 conjecture text read. Bounded web prior-art search.',
 'Proved sufficiency (PIR-PROOF.md). Condition (5) is equivalent to r(Z) >= k|Z|/n for every coordinate set Z, by the subcode {c : c_Z = 0} of dimension k - r(Z). Edmonds\' covering theorem applied to kappa0 parallel copies gives nu0 disjoint bases, i.e. a Lambda_{kappa0,nu0} with kappa0/nu0 = k/n. A random-code LP cross-check (275 codes, 65 satisfying (5)) agrees in every case.',
 'PIR-PROOF.md; outputs/pir-check.json',
 'No mathematical gap. Excluded as routine by the campaign rule against one-step bridges from classical theorems. Not formalized: Lean would need matroid covering and base theory, which is absent from mathlib. Journal versions (IEEE) not read.',
 ['1712.03898.html','1712.03898.abs.html','1801.04923.abs.html'])
add(338260,'parked; no counterexample beyond the source range',
 'Source Section 8 (Lemma 8.8, Theorem 8.9, Remark 8.10, Conjecture 8.11) and the Catalan-graph adjacency formula (40) read.',
 'Exact adjacency rule CM_n(i,j) = [z^{i-1-j}] C(z)^j mod 2. Modular Gaussian elimination reproduces the zero set {1, 6, 8, 10, ..., 11, 13, 15, 23, 33, 51, 61, 63} through n = 70. For every odd n from 65 to 1999, det(CG_n) mod 2147483647 is nonzero, which rigorously certifies det != 0 given correct code. Exact Bareiss values for odd n <= 81 all have the form +-2c^2 (e.g. 7597202 = 2*1949^2), consistent with det = +-w^T X w for the block form [[CM, B],[B^T, 0]]. Literal note: n = 1 gives det = 0 although 1 is not in the stated set (a trivial endpoint defect, zero credit).',
 'logs/catalan-odd-65-2001.log; logs/catalan-odd-1681-1999.log; scripts/catalan_det.c; scripts/catalan_exact.py',
 'A uniform nonvanishing proof of the square root c for odd n not in Gamma is missing; c is irregular. Coverage: all odd n <= 1999.')
add(338569,'parked (asymptotic); random-model diagnostics point AGAINST the conjecture',
 'Source main theorem (magic over some group iff no p - q in the Z-row space of the incidence matrix), forbidden substructures (Figure 6) and the n <= 13 table read.',
 'The six-line forbidden substructures have Levi-graph cyclomatic number at least 3, so their expected count in random n_3-configurations is O(n^-2). Random linear 3-regular configurations (union of three matchings, rejection sampled; labelled model) were tested with the source criterion. Magic fraction: n=10..40 about 10%, n=60 9/30, n=80 20/30, n=100 28/30, n=150 12/12. This suggests the proportion tends to 1, not 0. Mechanism: point images in coker(A^T) collide rarely once |det A| >> n^2.',
 'outputs/magic-random*.json; scripts/magic_random.py',
 'A rigorous refutation needs asymptotic cokernel/injectivity results for random sparse 0/1 matrices and a uniform model over isomorphism classes. This is far beyond the pass, with no Lean route. Worth flagging to root as evidence that the conjecture is false.')
add(339411,'parked; no counterexample beyond the source range',
 'Bencs (1806.00689v2) Section 5, Proposition 6.2 and Conjecture 6.3 read. Jiradilok-McConville 1910.14631 abstract and introduction read: it proves only the weaker Diaz-Lopez et al. Conjecture 4.3, not the disk.',
 'Exact integer value vectors via d(I,n) = C(n,m) d(I^-,m) - d(I^-,n); exact deflation of the boundary roots z = m (always) and z = -1. numpy roots, with mpmath refinement near the boundary. All 1,048,575 sets I with max I <= 20: no violation. Tightest cases are I = {m} (proved by the source) and {1,m}. All |I| <= 2 for m <= 30 (high-precision mpmath): no violation (log; run stopped at the CPU cap after m = 30).',
 'outputs/descent-disk-20.json; logs/descent-disk-sparse.log',
 'A uniform root-location proof is missing. Floating-point root finding is diagnostic only.')
add(339492,'parked (asymptotic extremal constant)',
 'Source conjecture and context read (1806.03899). Bounded web search: no resolution found. Forcade-Lamoreaux local maximum 0.084 noted.',
 'No finite mechanism. Delta_3 is a limsup density over all abelian Cayley digraphs of degree 3, which a search cannot certify.',
 'none', 'A global extremality proof is needed. Out of scope for this pass.')
add(341618,'source-reported resolution (zero credit)',
 'Source 1901.06771 Section 4 read around Conjecture 4.13: the converse is false for general words (source cites [7, Remark 2.19]), and the conjecture concerns involution words.',
 'The source itself states, after Conjecture 4.13: "Remark (Note added in proof). A proof of this result now appears in [25]." Stopped.',
 'sources/1901.06771.txt', 'Resolved in the source authors\' cited follow-up [25].')
add(341964,'parked; Lean-infeasible object',
 'Source 1902.10357 statement read via conjecture text. Web search: the survey 1901.05155 lists it as open. The cases m <= 3 are proved in the source.',
 'No search: crossing-number lower bounds for m >= 4 are not finitely certifiable at scale, and mathlib has no topological drawing or crossing-number theory for a literal endpoint.',
 'none', 'Needs a lower-bound proof for all n and m >= 4. Not pursued.')
add(342411,'parked; reduction recorded; finite CSP out of cap',
 'Albert-Li (1904.05500) Definitions 1-4, Observation 5, the experimental method and the open cases |F_4| in {22,23,24} read.',
 'Proved |F_4| = 23 impossible: S_4 is (3,4)-balanced with 10 extensions per pattern, and removing one rho drops only the at most 4 patterns of rho. Enumerated the balanced F_4 with |F_4| = 22: 5 labelled choices (outputs via scripts/uwilf_f4.py). HiGHS ILP for F_4 = S_4 with levels 5..6 and (k,n)-balance: level 5 is trivially feasible (all of S_5); level 6 hit the 100 s limit.',
 'scripts/uwilf_f4.py; scripts/uwilf_ilp.py; outputs/uwilf-N5-S4.json; outputs/uwilf-N6-S4.json',
 'Needs a structural growth argument or a much larger certified CSP. An ILP or SAT nonexistence certificate would not be kernel-checkable in Lean without native evaluation.')
add(343098,'parked; extended computation agrees',
 'Source 1906.12054 Sections 2 and 4 (Propositions 4.1-4.8, definition of N_p, U_1, L(p), Table 1, Conjecture 4.10) read.',
 'Union-find counter (scripts/equational.c) reproduces Table 1 (p = 31: U = 8, L = 7; p = 107: U = 27). New prime p = 3049, beyond the source\'s 3041: U_1 = 762 = L(3049); every unconnected graph has exactly two components, with a small component of size 2. Heuristic: components of size k >= 5 have expected count about p^{3-k}.',
 'logs/equational-3049-a.log; logs/equational-3049-b.log',
 'A proof excluding medium-size components (a Weil-type or dynamical argument) is missing. Each further prime costs about p^3 operations.')
add(343100,'parked; extended computation agrees',
 'Source Section 6 (Propositions 6.1-6.7, cubic computations, conjecture) read.',
 'New prime p = 3083 (p = 2 mod 3, beyond 3041): U_3 = 771 = L(3083), all with exactly two components (small components 2:770, 3:1).',
 'logs/equational-3083c-a.log; logs/equational-3083c-b.log',
 'Same missing argument as 343098.')
add(343101,'parked; extended computation agrees',
 'Source Section 6 read. The claim covers all lambda in N_p, a != 0, p >= 5 with 3 not dividing p - 1.',
 'At p = 3083, every unconnected G(lambda, X^3 + a) (771 graphs) has exactly two components. Same computation as 343100.',
 'logs/equational-3083c-a.log; logs/equational-3083c-b.log',
 'A structural proof is missing.')
add(344001,'parked; strong computational evidence; source Proposition 7.11 is wrong',
 'Source Definition 1.1, Remarks 3.1 (incl. the 8-day search to order 29), Conjectures 4.1-4.5, and Propositions 7.10 and 7.11 read.',
 'Reduction: E is extreme iff there are unimodular masses with mu*mu~ = 6 delta_0 (Cauchy-Schwarz forces equal moduli). So every nonzero ordered difference must occur at least twice. For generating sets whose coincidence relations have full rank 5, n divides the index of a lattice spanned by vectors of norm at most sqrt 8, so n <= 8^{5/2} < 182 (Hadamard). Complete enumeration of generating 6-sets with the difference condition for all n <= 181, canonical under affine maps (fast enumerator cross-checked against brute force for n <= 64): 1,487 canonical sets (311 for n <= 64, 1,176 for 65..181), all solved. Numerical unimodular least squares (25-60 random starts) finds only Z_6 and {0,1,2,3,4,7} in Z_10. The detector recovers both at 25 starts. Source error: Proposition 7.11 claims {0,1,2,3,4,7} is extreme in Z_14, but difference 5 occurs only once there; the printed certificate gives (mu*mu~)(5) = -i, not 0.',
 'outputs/extreme6b-6-64.txt; outputs/extreme6b-65-181.txt; outputs/extreme6-solve-*.json; scripts/extreme6*.c; scripts/extreme6_solve.py',
 'Toward a proof: (i) exact (non-numerical) solvability of the unimodular systems for the 1,487 sets; (ii) the rank-deficient coincidence case. Those patterns lift to Z^s + T with s >= 1, and the extreme-direction argument only forces |A|, |B| >= 2 torsion fibres, so this needs a separate bound. A Lean classification over all cyclic groups is far beyond feasible kernel computation.')
add(344132,'parked (open for k = 4)',
 'Source 1910.06226 statement read. Web search: large alphabets are settled (Hong-Zhang k >= 17; 2608.10591 preprint k >= 5, unverified), k = 4 is open.',
 'No search: the source already searched to length 1000. A counterexample would have to be a long extremal word, and exhaustive search beyond length 1000 is infeasible within the caps.',
 'none', 'Open; no tractable mechanism.')
add(344430,'parked (descriptive table pattern, analytic/computational)',
 'Source 1911.03707 Conjectures 3.1-3.5 and the base-word construction read.',
 'The statement depends on table-defined perturbation vectors from MACH2 supercomputer data for n <= 75000. Not finitely checkable within the caps; no proof mechanism.',
 'none', 'Out of scope.')
add(344665,'source-proved (zero credit)',
 'Source 1911.12471 abstract, Introduction (Conjecture 4 and the Fraughnaugh-Locke conjecture) read.',
 'The source itself proves it: "every 2-connected n-vertex triangle-free graph with maximum degree at most 3 has an independent set of size at least 3n/8, with the exception of the six graphs in F. This confirms a conjecture made independently by Bajnok and Brinkmann". The MathDB remark that the source gives no resolution status is a paraphrase defect.',
 'sources/1911.12471.txt', 'Resolved by the source (Cames van Batenburg-Goedgebeur-Joret).')
add(344724,'published resolution (zero credit); independent short proof recorded',
 'Hibi-Tsuchiya (1912.01212v2) full text read. Miyazaki arXiv 2205.01409 Section 5 read: Conjecture 5.1 = Hibi-Tsuchiya Conjecture; Theorem 5.2 "Conjecture 5.1 is true" (via an Ulrich module / canonical-module trace argument).',
 'Independent proof found before the prior-art check. K[C_{2s+1}] is normal (source [4]), so h = h* of the stable set polytope Q. Interior lattice points of kQ, shifted by -1, are the points of (k-3)Q plus D(m) points with sm < sum y <= sm + s - 2 (m = k-3). The slack bijection z_i = m - y_i - y_{i+1} gives y_j = r + (alternating z-sum) >= 0, so D(m) = sum_{r=1}^{s-2} C(m - 2r + 2s, 2s). Ehrhart reciprocity then gives rev(h) - h = sum_{i=2}^{2s-3} (-t)^i, exactly the conjectured form. Excluded as known.',
 'sources/2205.01409.txt', 'Known (Miyazaki 2022).',
 ['2205.01409.html','1912.01212.abs.html'])
add(345005,'parked (analytic eventual-periodicity claim)',
 'Source 1912.11185 statement and numerical context read.',
 'An eventual sign-periodicity claim for q-series coefficients; no finite certificate. The source says q-series methods are unclear.',
 'none', 'Out of scope.')
add(348339,'parked (restricted Goormaghtigh equation)',
 'Source 2010.08023 (Jones-Zvonkin) read around the conjecture. Web search: Goormaghtigh conjecture is open; Grantham 2410.03677 finds no new Goormaghtigh primes below 10^700.',
 'The claim is the Goormaghtigh equation (q^n-1)/(q-1) = (r^k-1)/(r-1) restricted to prime-power bases. n = 2 is impossible because q = r(1 + ... + r^{k-2}) has a cofactor that is 1 mod p and greater than 1. The general case is a famous open exponential Diophantine problem.',
 'none', 'No tractable route.')
add(348918,'parked; verified far beyond the source range (diagnostic)',
 'Source 2012.01992 Section 3 (least eigenvalue -4 with multiplicity (n-3)^2, n-4 multiplicity bounds, Conjecture 3, verified n <= 100) read. Web search: 2301.08106 and 2508.01088 give partial results; no proof found.',
 'Exact reduction: A(Q(n)) = N N^T - 4I with N the n^2 x (6n-2) square/line incidence matrix (rows, columns, diagonals, antidiagonals; two squares share at most one line). So every eigenvalue other than -4 is mu - 4 for a nonzero eigenvalue mu of the (6n-2)-dimensional Gram matrix N^T N. eigvalsh with an absolute integrality tolerance of 1e-8 (the minimum non-integer distance stays >= 1e-3) gives integer eigenvalues and multiplicities exactly as conjectured for every n from 4 to 400. An earlier loose-tolerance run showed spurious hits (e.g. n = 108, lambda = 109); exact modular nullity 0 confirmed they were artefacts (retained as superseded).',
 'outputs/queens-4-260.json; outputs/queens-261-400.json; scripts/queens.py; scripts/queens_check.py',
 'Needs exclusion of all other integer eigenvalues for every n (characteristic polynomial factorization of N^T N). Floating results are diagnostic.')
add(349132,'parked (numerical celestial mechanics)',
 'Source 2012.10759 conjecture section read: the source says the conjecture remains unproved in a rigorous sense.',
 'Continuation-class equality for all odd n is analytic/numerical; no finite route.',
 'none', 'Out of scope.')
assert set(E)==set(map(str,res['ids'])) and len(E)==20
out={}
for i in map(str,res['ids']):
    o=ex[i]; a=o['source_url'].rsplit('/',1)[-1]; e=E[i]
    rcpts=[r for r in [rec(a+'.html')]+[rec(x) for x in e.pop('extra_receipts')] if r]
    out[i]=dict(mathdb_id=int(i),title=o['title'],statement=o['statement'],source_url=o['source_url'],provenance=o['provenance'],
        credit=0,source_receipts=rcpts,source_text_sha256=txt_hash(a),historical_screen=H,**e)
(D/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(len(out)); 
for i,v in out.items(): print(i,v['outcome'][:90])
