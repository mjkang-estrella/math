# Assemble results.json: exactly 20 ID-keyed dispositions with provenance and receipts.
import json, hashlib, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
prov = json.loads((D/'outputs/provenance.json').read_text())
res_ids = json.loads((D/'reservation.json').read_text())['ids']
rec = {r['path']: r for r in json.loads((D/'outputs/source-receipts.json').read_text())}
def absr(a): 
    r = rec.get(f'sources/abs/{a}.html'); return {'url': f'https://arxiv.org/abs/{a}', 'http_status': 200, **({'sha256': r['sha256'], 'fetched_utc_mtime': r['mtime_utc']} if r else {})}
def pdfr(a):
    r = rec.get(f'sources/pdf/{a}.pdf'); return {'url': f'https://arxiv.org/pdf/{a}', 'http_status': 200, 'sha256': r['sha256'], 'fetched_utc_mtime': r['mtime_utc']} if r else None
C = 'Bounded review only. No worldwide novelty clearance. No Lean was run in this lane (Claude lane restriction).'
E = {}
def add(i, arx, outcome, depth, finding, attempts, gap, formal='No Lean endpoint; none claimed.', extra=None):
    E[i] = dict(outcome=outcome, review_depth=depth, source_arxiv=arx, finding=finding,
                attempts_and_exact_coverage=attempts, remaining_gap=gap, formal_status=formal, **(extra or {}))
add(336121, '1705.07504', 'PARKED_AFTER_EXACT_COMPUTATION',
    'Current arXiv v3 (11 Oct 2017; published Proc. AMS 146 (2018)) Section 4, Table 1 and Conjecture 4.1 read; follow-up arXiv:1911.03707 located (abstract-level).',
    'Conjecture 4.1 (with the source data) amounts to: M(m) := max|coef of (q;q)_m| is strictly increasing from m = 25 on (for h > 16) and the cumulative sets form intervals for h > 5. Exact big-integer computation of M(m) for every m <= 1253 found M strictly increasing on 25 <= m <= 1253 (ratios M(m+1)/M(m) in [1.12, 1.25]); Table 1 values reproduced. No counterexample; a proof needs explicit-error Sudler/Wright asymptotics for all m plus a finite computation (analytic, Lean-heavy).',
    'scripts/qmax.py (checkpointed exact computation), outputs/qmax.json (M(m) and argmax for m <= 1253), logs/qmax1.log, logs/qmax2.log.',
    'Uniform analytic lower bound for M(m+1)/M(m) > 1 for all m beyond a computable threshold; not attempted.')
add(336509, '1706.10206', 'PARKED_AFTER_EXHAUSTIVE_COMPUTATION',
    'Current arXiv v3 (30 Aug 2017) Section 7.2 read; Rajasekaran 2018 Waterloo MMath thesis (UWSpace) read at the antipalindrome passage: still Conjecture 28, NWA did not run to completion.',
    'Conjecture 11 holds exhaustively for every odd n = 9, 11, ..., 25 (bitset DP over all even integers of length n and all sums of at most 10 antipalindromes of length n-3; per-n counts in logs). Every target needed between 5 and 10 summands. No counterexample in that range; the statement is universal in n, so only an automaton-style or hand digit-carry proof can settle it (Lean-heavy).',
    'scripts/antipal.py; logs/antipal1.log (n = 9..21), logs/antipal2.log (n = 23, 25).',
    'A full proof for all odd n (the authors\' nested-word-automaton computation never completed).')
add(325116, '1303.0568', 'PARKED_AFTER_EXACT_COMPUTATION',
    'arXiv v1 (only version) Section 7, eq. (7.11), Corollary 7.2 and Conjecture 7.3 read. Published as Acta Arith. 162 (2014) 51-64 (per [Ho4] in Hou, Acta Arith. 166.3 (2014)); the published text of the 162 paper was NOT read, so retention of Conjecture 7.3 there is unverified.',
    'S(a) computed exactly (rational arithmetic, generalized binomials) for 0 <= a <= 120: the predicted residue mod 3 holds for every a (covers the regimes [3,8], [9,26], [27,80], [81,120]). Conjecture 7.3 extends Corollary 7.2 (p = 3, q = 3^{2k}). A proof would need a Lucas-type 3-adic analysis of the double sum; not attempted. An a <= 250 run hit the wall cap (logs/houS250.*) and is not claimed.',
    'scripts/houS.py; logs/houS.log.',
    'Proof for all a; published-version check.')
add(323730, '1207.0357', 'PARKED_SOURCE_DEFINITIONS_HEAVY',
    'Abstract/current version (v2, J. Stat. Phys. 150 (2013) 609-657) checked; conjecture body not reproduced; follow-ups located by search only (Hagendorf 2014 arXiv:1405.4726 nineteen-vertex model; Hagendorf-Morin-Duchesne 2016 sum rules via Kuperberg determinants).',
    'Infinite family of sum-rule identities for zero-energy singlets of a spin-one supersymmetric chain; not a finite certificate. Follow-up papers compute related sum rules and may settle it (unread). r151 recorded a related Hagendorf-Lienardy item as announced/published elsewhere.',
    'None (no exact diagonalisation implemented).',
    'Read follow-ups for a published proof; otherwise Bethe-ansatz/ASM machinery.')
add(372524, '2601.08583', 'PARKED_ALGEBRAIC_GEOMETRY',
    'Current v3 (23 Jan 2026) Section 2 read (Conjecture 2.1, Question 2.2).',
    'Existence of reduced plane curves realising every ordered partition (composition) of every t; source verifies t <= 4. Needs explicit curve families and Jacobian syzygy computations (Singular/CoCoA) for each t; no finite certificate resolves all t; no defect found against the source\'s own necessary conditions.',
    'None.', 'A uniform construction of curves of class tT_pi.')
add(372789, '2601.19068', 'PARKED_ASYMPTOTIC_EXTREMAL',
    'Abstract (v1 only) read; conjecture as quoted.',
    'Linear Turan bound kn/3 + cn for linear paths of length k >= 5 with a universal constant: asymptotic in n, excluded by reserve7 cues; source proves only k = 5 exactly (15n/11). Web search finds no general resolution.',
    'None.', 'General k; deep extremal problem.')
add(373032, '2602.07920', 'KNOWN_SOURCE_THEOREM',
    'Abstract of current v1 read.',
    'The source abstract states that it determines the full spectrum and eigenspaces of the single-shelf position matrix, which "strengthens and resolves two conjectures" of arXiv:2507.10294 (Clay). The MathDB record is the source\'s own resolved conjecture.',
    'None (source resolution).', 'None for discovery.')
add(373513, '2603.08822', 'PARKED_COMPLEXITY',
    'Abstract read; conjecture as quoted.', 'DP-completeness of deciding chi\'_c(G) = r: complexity-theoretic, not a finite certificate.', 'None.', 'Reduction proof.')
add(373723, '2603.18754', 'PARKED_AFTER_EXHAUSTIVE_AND_LOCAL_SEARCH',
    'Current v2 (25 May 2026) Theorems 6-7, Remark 8, Conjecture 30, Lemma 31 and the special-case argument read.',
    'Since sum(k) = l for k on the segment and p_M <= k, ||p_M - k||_1 = l - |M|, so the conjecture asks for a matching with p_M <= k and |M| >= l - h + 2. Exhaustive (restricted-growth colourings, all integer k on the segment, all matchings): h = 4 for l = 2..6 (700,075 colourings at l = 6), h = 5 for l = 3..5; no violation; minimum slack 1 for l <= 5. Local search (exact DP slack) for h = 4 up to l = 16, h = 5 up to l = 12, h = 6 at l = 12: no violation. A tight h = 4 instance was found and brute-force verified at l = 10 (edge colours [0,1,0,2,0,2,1,2,1,3,0,3,3,3,0,3,1,1,0,1], p_M0 = (6,3,0,1), p_M1 = (0,3,3,4), k = (2,3,2,3) at t = 2/3; max |M| with p_M <= k is 8 = l - h + 2; logs/cl3-10-4-22.log), so the conjectured bound is attained for h = 4. Literal reading with h = 2 is false (alternating 2-colouring, k midpoint) but the source clearly intends h >= 3 and says h = 3 follows from Theorem 7: a wording issue, zero credit.',
    'scripts/cyclematch.py, scripts/cyclelocal.py, scripts/cycleminslack.py; logs/cm-*.log, logs/cl*-*.log, logs/cms-*.log.',
    'A proof for h >= 4 (the h = 3 case already needs the source\'s topological Crossing Lemma).')
add(373761, '2603.21181', 'KNOWN_SOURCE_THEOREM',
    'Abstract of current v1 read.',
    'Tang proves lambda_{n-1}(A) + lambda_n(A) >= -2n/3 for real symmetric A with off-diagonal entries in [0,1] and nonnegative diagonal, and states that this confirms the Leonida-Li conjecture. Since lambda_n <= lambda_{n-1}, this gives lambda_{n-1} >= -n/3 on the MathDB class S_n.',
    'None (source resolution).', 'None for discovery.')
add(373863, '2603.25428', 'PARKED_DEEP_STRUCTURAL',
    'Abstract read; conjecture as quoted.', 'Body-hinge global linkedness characterisation in dimension d >= 3 via superbricks: deep rigidity-theory structural conjecture; no finite certificate.', 'None.', 'Structural proof.')
add(374399, '2604.24502', 'PARKED_DEEP_STRUCTURAL',
    'Abstract of current v2 (9 May 2026) read.', 'Upper bound rk Eq(g,h) <= 2n-2 for monomorphisms F_n -> F: the source only gives the lower-bound construction; general upper bounds are a long-standing hard problem (Stallings, Logan n = 2). A counterexample would need explicit monomorphisms with large equalizers, computable via Stallings foldings but with no tractable search space identified. Web search: no follow-up.', 'None.', 'Search or proof strategy.')
add(374586, '2605.04859', 'PARKED_FAMOUS',
    'Abstract read.', 'Partition rank vs analytic rank linear equivalence (known up to log factors): famous open problem; the source resolves a different AKZ stability conjecture.', 'None.', 'Famous open problem.')
add(375230, '2606.11494', 'PARKED_AFTER_ADVERSARIAL_SEARCH',
    'Current v1 Sections 1-2 read (definitions, Conjectures 1-3, Theorems 1-2); Dror-Feldman-Segal-Halevi arXiv:2010.07280v4 abstract read.',
    'Two agents reduce to the identical-valuation Conjecture 1 by cut-and-choose (agent 1 cuts with an EF1 2-colouring for v1, agent 2 chooses), so counterexamples need n >= 3 or matroids where Conjecture 1 is open. Adversarial local search over integer valuations with exhaustive feasible-partition checks: M(K4) n = 2, 3; Fano F7 n = 3; M(K3,3) n = 2; wheel W4 n = 2. Best min-violation stayed <= 0 (=0 only for K4, n = 2, which is covered by the cut-and-choose argument); n = 3 runs stayed far from a counterexample (-12, -20 at vmax 100).',
    'scripts/ef1matroid.py; logs/ef-*.log, logs/ef2-*.log.',
    'General proof (open even for laminar matroids with >= 4 agents).')
add(375692, '2606.31702', 'PARKED_FAMOUS',
    'Abstract (survey) read.', 'List Edge Colouring Conjecture: flagship open problem; ranked last by reserve7.', 'None.', 'Famous open problem.')
add(376053, '2607.14694', 'KNOWN_SOURCE_THEOREM',
    'Abstract of current v2 (12 Oct 2026) read.',
    'The source abstract states that it characterises the subtournaments forced by large acyclic dichromatic number, "thereby confirming a conjecture of Bang-Jensen, Picasarri-Arrieta, and Yeo". The MathDB record is that conjecture.',
    'None (source resolution).', 'None for discovery.')
add(366608, '2501.05968', 'PARKED_AFTER_EXHAUSTIVE_AND_LOCAL_SEARCH',
    'Current v2 (11 Feb 2026, split from v1) Sections 1-2 read (Conjectures 1.2, 1.6, Constructions 1.3, 1.7, Theorems 1.4, 1.5, 1.8). Related Chang-Cheng-Wang-Wei-Yan arXiv:2603.18915 found by search (asymptotic version sigma_2/2 - o(n); abstract-level).',
    's* in {0,1} is trivial (any Hamilton cycle has sigma_max >= n/2) and Freschi-Lo (Theorem 1.1) settles every graph with delta >= n/2 and delta >= T. Exhaustive over all underlying graphs K_n - H with s* >= 2 up to isomorphism and all orientations (backtracking over Hamilton-cycle constraints; two independent implementations agree for n <= 8): n = 6 (3 graphs), 7 (7), 8 (53): no counterexample. n = 9: all 265 graphs; 258 decided exactly (no counterexample; Freschi-Lo skips included), 7 graphs (all s* = 4, T = 7, delta = 6, H containing a P3) undecided at 20,000 nodes and then checked by Held-Karp local search (about 18,000-53,000 orientation evaluations each): best max sigma = 7 = T, no counterexample. Random and construction-seeded joint searches at n = 9, 10: margins >= 0. Not exhaustive beyond n = 8 in full.',
    'scripts/oridisc.py, scripts/oridisc2.py, scripts/oriexact.py, scripts/orirandom.py, scripts/orijoint.py; logs/od-*.log, logs/od2-*.log, logs/oriex*.log, logs/orir10.log, logs/oj-*.log; outputs/oridisc-n9-*.json. Note: an early oridisc2.py version had a count-bookkeeping bug that produced false counterexamples; it was fixed and the fixed version agrees with oridisc.py (logs of the buggy run were overwritten; disclosed here).',
    'Exact decision for the 7 remaining n = 9 graphs; n >= 10; a proof.')
add(367590, '2503.15296', 'SETTLED_BY_CLASSICAL_BRIDGE',
    'arXiv v1 (only version) Section 4 read (equation (13), the n = 20 and n = 119 discussion, Conjecture 5). Chen-Fu-Wang-Zhou theorem read at abstract level (Optimization Online 2003 preprint page; Taiwanese J. Math. 9 (2005) 629-638); Project Euclid PDF returned an Incapsula challenge and was not retried.',
    'Full resolution by a short bridge. Take G a disjoint union of stars: partition {1,...,m} into blocks S_1..S_t (t = n - m) with block sums exactly m+1, ..., n; each block becomes a star whose leaves carry its elements as edge labels and whose centre has sum m+i. Leaf sums are {1..m}, centre sums {m+1..n}, so the vertex sums are exactly 1..n; there are m edges and n vertices. Blocks have >= 2 elements since every target exceeds m, so no K2 components; P3 components are the blocks of size 2 (c may be any count, including 0). The partition exists by the Chen-Fu-Wang-Zhou theorem (sum condition = Pell equation (13); all targets >= m). Explicit check for n = 20 (blocks {14,1},{13,3},{12,5},{11,7},{10,9},{2,4,6,8}). This is a classical-theorem bridge and is expected to earn zero credit.',
    'scripts/pellstar.py; outputs/367590-star-partitions.json (n = 3, 20 explicit; the naive DFS did not finish for n = 119, 696 and is not claimed).',
    'None mathematically (given the cited theorem); credit unlikely (routine bridge).')
add(367786, '2504.00760', 'PARKED_ALGORITHMIC',
    'Abstract of current v3 (11 Feb 2026; SODA 2026; split, part two arXiv:2602.09811) read.', 'Linear-time algorithm conjecture: algorithmic, not a finite certificate; part two unread.', 'None.', 'Algorithm design; check arXiv:2602.09811.')
add(367834, '2504.02425', 'CANDIDATE_FULL_PROOF_UNREVIEWED',
    'Full source read (v1, only arXiv version); published OJAC 20 (2025) DOI 10.61091/ojac20-01 open-access copy read: Conjecture 6.2 retained verbatim. Companion papers 2402.15774, 2502.04228, 2510.01667, 2607.14098 screened (statements/keywords, not every proof body).',
    'Conjecture 6.2 is TRUE. Complete ordinary proof in CASE-367834.md. (i)=>(ii): total boundedness forces ray labels -> 0, the completion adds one point p with d(p,x_n) = max_{k>=n} lambda_k; cutting the ray after each right-to-left record and hanging each finite segment from p (label 0) gives a starlike rayless tree generating X. (ii)=>(i): compactness forces label 0 at the centre and finiteness of {d(c,.) >= eps}; group each leg by strict prefix records and list groups by decreasing height, each written as (y_{s+1},...,y_e,y_s); this ray with the original labels generates X \\ {c}, which is dense and totally bounded.',
    'scripts/ultra62.py diagnostic (300 random exact-rational instances per direction, all distances agree; logs/ultra62.log). Lean statement draft lean-draft/Conj62.lean (UNCOMPILED, proofs sorry-outlined).',
    'Independent review; credit judgement (short elementary argument in the source family); full Lean formalization (medium-high cost).',
    formal='Draft Lean statement only (UNCOMPILED, not elaborated); no endpoint claimed.')
out = {}
for i in res_ids:
    p = prov[str(i)]; r = p['record']; e = E[i]; a = e.pop('source_arxiv')
    out[str(i)] = {'mathdb_id': i, 'title': r['title'], **{k: e[k] for k in ['outcome']},
        'discovery_count_credit': 0, 'root_acceptance': 'not requested or claimed; root decides',
        'review_depth': e['review_depth'], 'literal_statement': r['statement'],
        'statement_sha256': hashlib.sha256(r['statement'].encode()).hexdigest(),
        'source_name': r['source_name'], 'source_url': r['source_url'],
        'provenance': {'chunk': p['chunk'], 'line_1based': p['line_1based'], 'raw_sha256': p['raw_sha256'], 'chunk_sha256': p['chunk_sha256']},
        'raw_file': f'raw/{i}.jsonl', 'primary_receipts': [x for x in [absr(a), pdfr(a)] if x],
        'historical_screen': 'No exact-ID or source-keyword hits in campaign ledgers or the 516 lane SUMMARY/results files screened (outputs/history-screen.txt); index absence is not global novelty.',
        **{k: e[k] for k in ['finding', 'attempts_and_exact_coverage', 'remaining_gap', 'formal_status']}, 'limitations': C}
assert len(out) == 20
(D/'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('ok', len(out))
