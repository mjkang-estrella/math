# Build results.json (exactly 20 ID-keyed entries) from extracted.json, sources/receipts.jsonl and the dispositions below.
import json, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D / 'extracted.json').read_text())
rec = [json.loads(l) for l in (D / 'sources/receipts.jsonl').read_text().splitlines() if l.strip()]
NO_HIST = ("No substantive prior campaign note: exact-ID search of campaign *.md/*.json/*.txt (logs/history-grep-files.txt, "
           "logs/history_context.log) found only sitemap/corpus/routing/coverage lists, coincidental numeric strings and the r146 launch note.")
E = {}
def e(i, depth, outcome, source_statement, finding, credit, remaining='n/a', mechanism='n/a', coverage='n/a', files=(), keys=()):
    E[i] = dict(depth=depth, outcome=outcome, source_statement=source_statement, finding=finding, credit=credit,
                remaining=remaining, mechanism=mechanism, coverage=coverage, files=list(files), keys=list(keys))

e(337352, 'full conjecture sections of CJKM arXiv:1710.04604 v1 and v2; full body of Jung arXiv:1901.11156; published abstract (Graphs Combin. 38 (2022) 7)',
  'CANDIDATE: full proof of Conjecture 2 in the family reading, plus exact per-k characterization (holds for k=1 and all k>=4, fails exactly at k=2,3); Lean not run (draft UNCOMPILED)',
  'CJKM Riordan graphs I, Conjecture 2: diam(CG_{2^k}) = k and no io-decomposable Bell-type G_{2^k} not isomorphic to CG_{2^k} has diam(G_{2^k}) = k, for all k >= 1.',
  'Theorem: for every k >= 4, an io-decomposable Bell-type G_{2^k} with diameter k has an all-ones A-prefix, so it is CG_{2^k}. New Lemma A (Lagrange inversion mod 2): N=2^K ~ j iff j is odd and [w^{N-1-j}]A^{-1} = 1. Lemma B: the first zero at p in [2^{K-1}, 2^K - 2] gives the edge {N, N-1-p} with 1 <= N-1-p <= 2^{K-1}-1. Lemma C: diameter <= K-1. Induction from the k=4 base (128 sequences, exhaustive). Per-k reading fails at k=2 (A=110) and k=3 (A=1111110, printed with diameter 3 in Jung Table 1).',
  'Possible credit for the (R2) and k>=4 theorem only; the (R1) literal refutation is a zero-credit source-table correction. Distinct from credited 338258 (Riordan graphs II, kernel/odd-part spectral conjecture): same object family, different invariant and mechanism. Bridge risk moderate: uses published lemmas (P1)-(P5) plus new Lemmas A and B. Root to judge significance and family concentration.',
  remaining='Lean formalization (HIGH cost): generating-function bridge, Lagrange inversion mod 2, general-k fractal, universal-vertex and CG-distance lemmas; base case by decide.',
  mechanism='Lagrange inversion mod 2 for the last vertex + fractal decomposition + induction',
  coverage='Exhaustive: all io sequences for k=2..5 (2, 8, 128, 32768 graphs); k=6 all 65536 sequences with the forced 32-ones prefix; Lemma A on 800 random Bell-type A-sequences (N=8..64); Lemma B on all restricted sequences for K=4..6 and 3000 random K=7 samples; CG_{2^s} eccentricity structure for s<=8.',
  files=['outputs/337352-proof.md', 'lean/Riordan337352.lean', 'scripts/riordan.py', 'scripts/riordan_fast.py', 'scripts/riordan_crosscheck.py', 'scripts/riordan_nbr.py', 'scripts/riordan_tables.py', 'scripts/riordan_sanity.py'],
  keys=['1710.04604', '1901.11156', 's00373-021-02427-1'])
e(330508, 'Li-Wei survey Conj. 2.54 and the original Dehmer-Kraus MATCH 68 (2012) Sect. 4.1 (Lemma 4.1, Conj. 4.2) read',
  'REFUTED trivially (zero credit: follows from the source\'s own Lemma 4.1, rho=1 case)',
  'Dehmer-Kraus Conj. 4.2: for every nonincreasing c_0>=...>=c_r, the star has maximal and the path minimal I_{f3}, where f3(v) = c_{orbit(v)} * ecc(v).',
  'n=5: the only dendrimers are S_5 and P_5. With c=(1/2,1/3,1/4) (nonincreasing), f3 is constant on P_5, so I(P_5) = log2 5 = 2.3219 > I(S_5) = 2.3135. Both the max and min claims fail; the same holds for every odd n (logs/dendrimer.log). The source\'s own Lemma 4.1 (c(i)(r+i) constant gives entropy log n) contains the mechanism.',
  'Zero credit: one-line consequence of the source lemma / statement defect.', files=['scripts/dendrimer.py', 'logs/dendrimer.log'],
  keys=['1505.04658', 'Match68'])
e(330518, 'source abstract and Sect. 3 (Pai et al. Conj. 2 and its proof) read',
  'KNOWN: proved in the source itself (Gregor-Luzar-Sotak)',
  'Pai et al.: chi_i(Q_n) = n+2 for n != 2^p - 1.',
  'The source derives chi_i(Q_n) = n+2 for all n != 2^p - 1 from its Cartesian-product theorem (Q_n = Q_{2^m-1} x Q_k), with tightness via the absence of a partition into n+1 dominating sets.',
  'Zero credit (source-proved).', keys=['1505.04908'])
e(332393, 'Milicevic arXiv:1602.00725 Conj. 9.6 and Lemma 5.5 read; Pokrovskiy arXiv:2507.05842 v2 abstract (fetched)',
  'OPEN deep (complete-graph version); the literal MathDB wording ("countably infinite graph") is trivially false',
  'Milicevic Conj. 9.6: for a k-colouring of a countably infinite graph G, k-1 sets with bounded monochromatic diameter cover G.',
  'Literally false for non-complete G (an infinite path in one colour cannot be covered by finitely many bounded-diameter sets). The intended complete-graph version is proved for r<=4 (Milicevic) and r=5 (Pokrovskiy 2025, via Tuza), and is equivalent to a bounded-diameter Ryser conjecture (Pokrovskiy); open in general.',
  'Zero credit: wording defect / deep Ryser-type problem.', keys=['1602.00725', '2507.05842'])
e(332603, 'source Sect. 7 read',
  'OPEN infinite structural; parked',
  'Merker: for every tree T there is k_inf(T) such that every k_inf(T)-edge-connected infinite graph has a T-decomposition.',
  'Infinite-graph extension of the Barat-Thomassen tree decomposition conjecture; no finite certificate route (the statement quantifies over infinite graphs).',
  'Outside the finite lane.', keys=['1603.00198'])
e(332860, 'source abstract; Sedlar-Skrekovski arXiv:2207.03941 abstract (fetched)',
  'KNOWN REFUTATION (bow-tie graph B has chi\'_irr(B) = 4)',
  'Baudon-Bensmail-Przybylo-Wozniak: every decomposable graph has chi\'_irr <= 3.',
  'Sedlar and Skrekovski showed the bow-tie cactus needs 4 locally irregular subgraphs; the conjecture was restated excluding B.',
  'Zero credit (published refutation).', keys=['1604.00235', '2207.03941'])
e(333133, 'source Sect. 1 conjectures read; status search',
  'OPEN deep; parked',
  'Zhu Conj. 3: some m makes every planar graph (5m-1,m)-choosable.',
  'Open (a 2026 arXiv paper says the conjecture remains largely open). Lower bound 4m + floor((2m-1)/9) + 1 <= a(m) (source). No finite certificate: m is existential and the statement covers all planar graphs.',
  'Outside the finite lane.', keys=['1605.04690'])
e(333742, 'Dyatlov-Jin arXiv:1608.02238 Conj. 3.15 and Remark read',
  'OPEN famous (Fuglede conjecture in cyclic groups); parked',
  'Dyatlov-Jin Conj. 3.15: A subset Z_M is a discrete spectral set iff it tiles Z_M.',
  'The cyclic-group Fuglede conjecture; proved for M with few prime factors (Laba, Malikiosis-Kolountzakis, ...); open in general and tied to the 1-D Fuglede conjecture. A counterexample would need M far beyond capped exhaustive reach.',
  'Outside lane capacity.', keys=['1608.02238'])
e(333826, 'source Conj. 1.2 read; Mies-Moore arXiv:2208.06336 via search',
  'OPEN structural; parked',
  'Merker-Postle Conj. 1.2: the class of arboricity-<=k graphs has bounded diameter arboricity k+1.',
  'Proved for k in {2,3} in the source; related strong nine dragon tree results (Mies-Moore) do not settle it. The bounded diameter is existential and the class is infinite: no finite certificate.',
  'Outside the finite lane.', keys=['1608.05352'])
e(334118, 'cited arXiv:1609.06171 (only version v1) and journal version (Involve 11 (2018) 143-167) read in full',
  'SOURCE-FIDELITY DEFECT: the G-positivity greatest-element conjecture does not appear in the cited source (either version)',
  'Not present in the source. Its conjectures are 5.1/6.1 (ribbon G-equivalence iff equal or rotated) and 5.3/6.2 (staircase transpose).',
  'Neither text contains a poset of G-positivity, a_{A,nu} or a greatest-element claim. The MathDB status line quotes text ("this does not hold for all ribbons") also absent from both. Real provenance unknown (possibly 2016 UMN REU Day-7 notes, not fetched).',
  'Zero credit unless root identifies the true source; without source definitions the order (sign convention for G-expansion coefficients) is ambiguous.', keys=['1609.06171', 'involve'])
e(334119, 'same as 334118', 'SOURCE-FIDELITY DEFECT (statement absent from cited source)',
  'Not present in arXiv:1609.06171 or the Involve version.', 'Same as 334118.', 'Zero credit unless the true source is identified.', keys=['1609.06171', 'involve'])
e(334560, 'source Sect. 1.4-1.5 read (Conj. 1.9 and its special case Conj. 1.11); Pokrovskiy-Sudakov arXiv:1711.00429 abstract (fetched)',
  'KNOWN REFUTATION via the source\'s own special case',
  'Aharoni et al. Conj. 1.9: for any partition E_1..E_m of E(K_{n,n}) and any j, some perfect matching F has |F cap E_i| >= floor(|E_i|/n) for i != j and |F cap E_j| >= floor(|E_j|/n) - 1.',
  'The source notes that Conj. 1.9 with m=n and |E_i|=n is Stein\'s equi-n-square conjecture (Conj. 1.11): partial transversal of size n-1. Pokrovskiy-Sudakov (arXiv:1711.00429, Proc. AMS 147 (2019)) construct equi-n-squares with no partial transversal larger than n - (1/42) ln n, refuting Conj. 1.11 and hence Conj. 1.9.',
  'Zero credit (published refutation of the stated special case).', keys=['1611.03196', '1711.00429'])
e(334570, 'source Sect. 5 (Conj. 9-10) read; arXiv:1806.03774 abstract (fetched; Admasu-Sehgal answer questions of Toth)',
  'KNOWN: proved (arXiv:1806.03774 using the Chew-Chin-Lim rank-4 formula)',
  'Toth Conj. 10: N(p^m,p^m,p^m,p^m) has degree 4m and leading coefficient 1.',
  'Resolved in "Counting subgroups of fixed order in finite abelian groups" (arXiv:1806.03774), which also proves Conj. 9. It also follows routinely from the classical Birkhoff/Delsarte type-count formula: the dominant type mu\'=(2^m) has degree sum mu\'_i(4-mu\'_i) = 4m and a monic Gaussian factor.',
  'Zero credit (published; routine classical bridge).', keys=['1611.03302', '1806.03774'])
e(334722, 'source Sect. 1-3 read; Yang arXiv:2310.16382 intro read',
  'OPEN; parked (no finite route found)',
  'Brown-Erey: for 2-connected k-chromatic G of order n>k>=4 and all (integer) x>=k, pi(G,x) <= (x)_k pi(C_{n-k+2},x)/(x(x-1)).',
  'Equivalent to Brown-Erey Conj. 1.3 (extremal graph K_k plus an ear). Proved at x=k (Engbers-Erey-Fox-He), for omega=k or alpha=2 (Yang 2023), and for huge x (Brown-Erey). The source states x in N, so no real-x shortcut. A python-only canonical graph generation to order 9-10 is beyond lane caps (no compiled helpers allowed).',
  'Not attempted beyond the screen.', keys=['1611.09545', '2310.16382'])
e(334795, 'source abstract; Damasdi-Palvolgyi arXiv:2011.12187 abstract (fetched)',
  'KNOWN REFUTATION (disks)',
  'Keszegh-Palvolgyi: for every plane convex D there is m such that every finite point set has a 3-colouring with no monochromatic homothet of D containing >= m points.',
  'Damasdi-Palvolgyi ("Realizing an m-uniform four-chromatic hypergraph with disks") realize, for every m, a non-3-colourable m-uniform hypergraph by disks. They extend this to homothets of convex sets with two parallel supporting lines and strict convexity near the tangencies, so the "every convex D" statement fails.',
  'Zero credit (published refutation).', keys=['1612.02158', '2011.12187'])
e(334947, 'source Conj. 2 and open-problem list read',
  'OPEN algebraic-geometric; parked',
  'Nenashev-Shapiro-Shapiro Conj. 2: for every mu |- d there is a refinement mu\' of mu with l_{bar mu} = l_{mu\'}.',
  'Secant degeneracy indices are defined via complex projective dependence on strata; no finite discrete certificate route in the lane.',
  'Outside the finite lane.', keys=['1612.08651'])
e(334964, 'source Sect. 1 and 4 (Conj. 2, Prop. 1, Table 1) read; status search',
  'OPEN; parked after analysis',
  'Akbari-Alipour Conj. 2: for every c there is n with l(n) > n + c.',
  'Best known gap is 2 (l(6)=9; l(2^k-2) > 2^k via Z_2^k minus two rows/columns). Analysis: for Z_2^k subarrays the only invariant is one linear sum, which blocks transversals only when t=2 lines are deleted, so this family cannot exceed gap 2. Product with odd cyclic squares fails because m-fold transversals evade the sum invariant. The statement needs an infinite family; finite search cannot resolve it (l(n) for n>=8 is beyond the authors\' computations).',
  'No candidate.', keys=['1612.09443'])
e(337294, 'Golowich-Kim source and Kovacs arXiv:2310.17433 v2 intro read',
  'OPEN; parked (verified n<=5 by Balister-Gyori-Schelp)',
  'BGS: any 2^{n-1} nonzero vectors of F_2^n summing to 0 are the differences of a pairing partition of F_2^n.',
  'Verified for n<=5 (BGS); partial results by Golowich-Kim (<= n distinct values) and Kovacs (<= n - 2 log n - 1 distinct values; a large equal fraction). An exhaustive n=6 check (multisets of 32 from 63, up to GL(6,2)) exceeds capped pure-python reach; a counterexample is considered unlikely.',
  'No candidate.', keys=['1710.02906', '2310.17433'])
e(337528, 'source Sect. 6 read; Burger-Pitz arXiv:1711.08711 abstract (fetched)',
  'KNOWN: proved (Burger-Pitz)',
  'Guggiari Conj. 6.1: no red directed path of length r implies a cover of K_N by at most r disjoint blue directed paths.',
  'Burger and Pitz ("Decomposing edge-coloured complete symmetric digraphs into monochromatic paths", arXiv:1711.08711) prove it, with a multicolour extension.',
  'Zero credit (published).', keys=['1710.10900', '1711.08711'])
e(337577, 'source Sect. 4 (Conj. 14) read; Li-Su-Fallat arXiv:2306.16247 abstract (fetched)',
  'KNOWN: resolved (Li-Su-Fallat 2023)',
  'Clark-Cooper Conj. 14: for k-trees H in T (k>=3), the matching polynomial of H divides phi(T); in particular phi(H) | phi(T).',
  'Li-Su-Fallat express phi(T) as a product of matching polynomials of connected subtrees with explicit positive exponents and state that this resolves the Clark-Cooper conjecture. Their abstract (fetched): phi_H | phi_T holds if r>=4 or H is connected when r=3, and they give a counterexample for disconnected H in a 3-tree, so the printed "in particular" clause is false in that case. Both parts are settled in print.',
  'Zero credit (published).', keys=['1711.01466', '2306.16247'])
assert sorted(E) == sorted(int(i) for i in ex), (sorted(E), sorted(ex))
out = {}
for i in sorted(E):
    x = ex[str(i)]; v = E[i]
    rr = {}
    for r in rec:
        if any(k in r['url'] for k in v['keys']):
            rr[r['url']] = {k: r.get(k) for k in ('status', 'sha256', 'bytes', 'file', 'utc', 'error', 'final_url')}
    out[str(i)] = dict(mathdb_id=i, title=x['title'], source_url=x['source_url'], provenance=x['provenance'],
                       prior_campaign_history=NO_HIST, review_depth=v['depth'], outcome=v['outcome'],
                       source_statement=v['source_statement'], mechanism=v['mechanism'], finding=v['finding'],
                       credit_assessment=v['credit'], precise_remaining=v['remaining'], search_coverage=v['coverage'],
                       files=v['files'], source_receipts=rr, self_accepted=False)
assert len(out) == 20
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(out), 'entries')
