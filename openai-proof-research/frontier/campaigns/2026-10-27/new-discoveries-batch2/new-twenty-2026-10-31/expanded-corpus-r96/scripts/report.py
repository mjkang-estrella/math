"""Assemble results.json (exactly the 20 reserved IDs) from extracted.json, receipts and dispositions."""
import json, hashlib, pathlib
L = pathlib.Path(__file__).resolve().parents[1]
ext = json.loads((L / 'extracted.json').read_text())
ids = json.loads((L / 'reservation.json').read_text())['ids']
h = lambda b: hashlib.sha256(b).hexdigest()
def receipt(name):
    p = L / 'sources' / f'{name}-receipt.json'
    return json.loads(p.read_text()) if p.exists() else None
D = {
 368807: dict(outcome='candidate_counterexample_with_full_lean_endpoint', review_depth='primary PDF read (definitions p.2, (2)-(4),(6), Definition 3, Lemma 7, Section 5.2, Conjecture 1 p.14); arXiv abstract page (v1 only); follow-up arXiv:2511.05045 PDF screened',
   result='Exact counterexample at n = 8: x* = X/4 (support 19, denominator 4) is a vertex of P_ASEP^8 (tight rank 56) adjacent to no tour (max common tight rank 54 < 55 over all 5040 tours). Lean: ASEP.arc_counterexample and ASEP.arc_neighborhood_tour_conjecture_false (literal arc space R^A), plus matrix-form ASEP.counterexample, ASEP.neighborhood_tour_conjecture_false, ASEP.segment_not_exposed; axioms propext, Classical.choice, Quot.sound only; fresh extracted strict -DwarningAsError rebuild of 21 modules + leanchecker on all 21 pass (lean-replay-3/result.json).',
   coverage='LP-sampled vertices n=4 (all 12), n=5 (191+212 distinct of 384), n=6 (378+348 distinct); annealing walks n=6 (2), n=7 (8 walks, min 1 adjacent tour), n=8 (4 walks, 101 zero-count vertices). Exact certification of two n=8 vertices (denominators 5 and 4) by integer rank; independent JS BigInt check of the chosen vertex.',
   remaining='Independent fidelity review (adjacency-as-extreme-segment, n >= 4 domain, tour definition), significance adjudication, paper, root replay. n = 7 status open (no counterexample found; not exhaustive).',
   files=['ASEP-COUNTEREXAMPLE.md', 'lean/', 'lean-replay-3/result.json', 'outputs/asep/', 'scripts/asep*.py', 'scripts/asep_independent.js'], credit=0),
 368627: dict(outcome='excluded_known_full_scope', review_depth='primary HTML read (Definition 2.1, Theorems 2.2, 3.3, Conjecture 3.8); resolving paper arXiv:2607.24426 read (Theorem 1.1 statement, nontriviality convention, final proof of Theorem 1.1 Section 4)',
   result='Conjecture 3.8 is settled by arXiv:2607.24426 (submitted 27 Jul 2026), Theorem 1.1: for 2 <= k <= |G|-1, (G,B_k^x) a 2-design with lambda > 0 forces G elementary abelian. k = 1 gives lambda = 0 (trivial). Known; no credit.',
   coverage='Exact pair-count checker (inclusion-exclusion over full-group subset-sum table): elementary controls Z3^2, Z2^3, Z2^4, Z5, Z5^2 reproduce known designs; all non-elementary abelian p-groups of orders 4..64, Z3 groups of order 81, Z121, Z125, Z128, Z2+Z4+...; no 2-design for 2 <= k <= n-2 (several order-128/243 groups hit the CPU cap, see outputs/designs/*.time).',
   remaining='none (known)', files=['scripts/designs.py', 'outputs/designs/', 'sources/prior/368627-2607.24426*'], credit=0),
 367165: dict(outcome='excluded_known_full_scope', review_depth='primary HTML read (definitions of FO/FD, Theorem 1.1, Conjecture 1.2, generating-function section); resolving paper arXiv:2609.17389 read (Conjecture 1.2 statement, Section 3 singularity analysis, Propositions 3.3, 3.5)',
   result='Proved by P. Cuthbertson, arXiv:2609.17389 (15 Sep 2026), Section 3 (singularity analysis; FD grows like the k-bonacci rate, FO strictly slower for k >= 3). Our independent rational-GF growth comparison (k-bonacci root vs root of x(x-1)^{k-1}=1) agrees. Known; no credit.',
   coverage='analytic derivation only (no search needed).', remaining='none (known)', files=['sources/prior/367165-2609.17389*'], credit=0),
 349717: dict(outcome='excluded_known_full_scope', review_depth='primary HTML statement section read; resolving paper arXiv:2205.13468 (O\'Sullivan) Theorem 1.3 and its derivation pointer read',
   result='O\'Sullivan, arXiv:2205.13468 Theorem 1.3: 2p_k(n) < (p_k(n+1)+p_k(n-1))(1 - n^{-2}) for n >= C_k. Since 1 - n^{-2} <= 1 - n^{-d} for d >= 2, the MathDB inequality follows for all large n. Known; no credit.',
   coverage='none needed', remaining='none (known)', files=['sources/prior/349717-2205.13468*'], credit=0),
 363770: dict(outcome='excluded_known_full_scope', review_depth='arXiv abstract of source 2407.02102 read (HTML 404); literal MathDB statement itself records the 2023 resolution',
   result='Every graph has a separating path system of size at most 19n (Bonamy, Botler, Dross, Naia, Skokan, Adv. Comb. 2023), as stated in the record and the source abstract. Known; no credit.',
   coverage='none needed', remaining='none (known)', files=['sources/363770-abs.html'], credit=0),
 341896: dict(outcome='parked_partial_known', review_depth='primary PDF read (Section 2 posets, Section 4.4 PL rowmotion definitions, Example 4.18, Theorems 4.21, 4.27, Conjecture 4.35 and its checked range); Dao-Wellman-Yost-Wolff-Zhang arXiv:2002.04810 (trapezoid definition, l=1 result) and Johnson-Liu arXiv:2311.07133 (intro, Corollary 4.12, Section 6.1) read',
   result='Johnson-Liu give a PL-rowmotion-equivariant bijection PP^l(rectangle) -> PP^l(trapezoid), settling condition (1) for the main pair at every l; condition (2) (orbit ddeg sums) remains open and is equivalent, given (1), to ddeg homomesy for PL rowmotion on PP^l(T_{k,n}) with the rectangle average (plus the two small pairs). No counterexample found.',
   coverage='rowmotion.js reproduces Example 4.18 exactly. Rectangle/trapezoid, both trapezoid orientations: 57+57 jobs beyond the source range (n = 9..12 with l up to 6/4/3/2, and n <= 8 with l = 5..8), largest 1,646,568 P-partitions, all orbit (size, ddeg-sum) multisets equal. Q^{2n}/I2(2n), both orientations, outside the source range n <= 8, l <= 4: 202 of 256 planned jobs (n <= 14, l <= 12) ran before the batch wall limit; 170 (85+85) completed with all multisets equal (largest 7,413,705 P-partitions) and 32 large jobs were killed by memory/CPU caps (recorded as FAILED).',
   remaining='Prove ddeg homomesy of PL rowmotion on PP^l(T_{k,n}) (trapezoid not tCDE); orbit-structure equality for (Q^{2n}, I2(2n)) and (OG(6,12), H3) at all l (H3 root poset not implemented).',
   files=['scripts/rowmotion.js', 'scripts/rowmotion_batch.sh', 'outputs/rowmotion/'], credit=0),
 366914: dict(outcome='parked_no_counterexample', review_depth='primary HTML read (Theorems 1.4, 1.5, 1.8, 1.9, Conjecture 1.11, construction sections)',
   result='Theorem 1.4 already covers a >= f(y-k,y) and both-even cases; the open window is y <= a < f. Every instance searched in the window has a verified linear realization.',
   coverage='All y = 7..11, 3 <= k < y/2 (x,y not both even), y <= a < f(x,y), 1 <= b,c <= 14 (y <= 9) or <= 18 (y = 10, 11): 9872 instances, all realized (exhaustive DFS with node caps plus deterministic randomized restarts; every path independently re-verified). y = 12, 13 runs were cut by the CPU cap (partial logs retained).',
   remaining='A uniform construction for k >= 3 (the authors\' proposed extension of their standard realizations); counterexample search would require exhaustive nonexistence at larger v.',
   files=['scripts/linreal.js', 'scripts/linreal.c (not compiled: no C compiler)', 'outputs/linreal-*.txt'], credit=0),
 382492: dict(outcome='parked_no_counterexample', review_depth='primary HTML read (Eq. (3) definition of rowDiv_k, Proposition 1 adjoint, Section 4 e-expansion, the conjecture and the equivalent T_k(m_mu) monomial-positivity proposition, two-row lemma)',
   result='No negative or non-integral e-coefficient found.',
   coverage='rowdiv.py (exact 0-1 matrix counts and dominance-order e-basis inversion; reproduces the source example rowDiv_2(e_22211) = 136e4 + 2e22 + 14e31): all mu |- kn for (k, n <= nmax) = (2,13), (3,9), (4,7), (5,6), (6,5), (7,4).',
   remaining='A positivity proof (e.g. a sign-reversing involution for the k-divisible 0-1 matrix model, or monomial positivity of T_k: e_r -> e_{kr} on m_mu).',
   files=['scripts/rowdiv.py', 'outputs/rowdiv/'], credit=0),
 368042: dict(outcome='parked_no_counterexample', review_depth='primary HTML read (Definitions 3.1, 3.12, Theorem 3.16, Question 6.1, Conjecture 6.2 and the checked range)',
   result='reg(I(G)^[k]) = aim(G,k) + k holds for every chordal graph on at most 9 vertices and all 1 <= k <= nu(G) (characteristic 32003).',
   coverage='chordal_gen.py: all unlabeled chordal graphs through n = 9 (counts 1,2,4,10,27,94,393,2119,14524 = OEIS A058862; connected = A048193). sqfree_reg.py: Hochster formula with the deletion recursion over induced subgraphs, ranks mod 32003; n <= 8 reproduces the authors\' check, n = 9 (14524 graphs) is new; 0 mismatches.',
   remaining='n = 10 (126758 graphs) not run; characteristic-2 check not run; Lean infeasible (Castelnuovo-Mumford regularity not in mathlib).',
   files=['scripts/chordal_gen.py', 'scripts/sqfree_reg.py', 'outputs/chordal/', 'logs/sqfree-reg-*.log'], credit=0),
 376197: dict(outcome='parked_no_counterexample', review_depth='primary HTML read (Theorem 3.9 flats formula, SP inequalities, duality lemma, Proposition 4.2 uniform formulas, Section 8 Conjecture 8.4 and its checked range: simple matroids up to 8 elements)',
   result='No violation of rho^(I_Delta(M)) <= omega / alpha^(I_Delta(M)); equality occurs (e.g. omega = 2 parallel-class matroids).',
   coverage='ghv.py (source Theorem 3.9 plus LPs); uniform matroids n <= 7 reproduce Proposition 4.2. Random GF(q)-represented matroids including loops and parallel classes (non-simple, outside the source\'s checked class): q = 2, 3 with n <= 8 (1308 + 1483 distinct labeled) and q = 2, 3, 5, 7 with n <= 10 (273 + 303 + 286 + 288). Floating-point LP screen (diagnostic).',
   remaining='Proof of Conjecture 8.4; exhaustive non-simple and 9-element catalogues; Lean infeasible (resurgence not in mathlib).',
   files=['scripts/ghv.py', 'outputs/ghv/'], credit=0),
 350489: dict(outcome='parked', review_depth='primary HTML conjecture section read; abstracts of Damnjanovic arXiv:2210.08334 and arXiv:2212.03026 read',
   result='The follow-ups resolve the circulant nut order-degree existence problem with n-dependent generator sets, not the universal sets {1..2t+1}\\{p_t} (odd t = 1 mod 10 or 15 mod 18) or {1..2t+2}\\{q_t,r_t} (even t). Open as stated; no mechanism within this pass.',
   coverage='none (source already computational to t = 1300).', remaining='Cyclotomic analysis of the residual families; Lean would need circulant spectra for all even n.', files=['sources/prior/350489-*'], credit=0),
 347539: dict(outcome='parked', review_depth='primary HTML conjecture statement and verified range read (8x8 Hankel minors)',
   result='No computation: the 9x9 Hankel minors in seven indeterminates exceed this lane\'s caps. Sokal-school coefficientwise conjecture; no shortcut found.',
   coverage='none', remaining='Production-matrix / continued-fraction proof of coefficientwise Hankel-TP for the GKP recurrence.', files=[], credit=0),
 349406: dict(outcome='parked', review_depth='primary HTML conjecture statement and context read (verified for odd v <= 53)',
   result='Existence conjecture over all normalized non-exceptional PPS; searching larger v could only confirm instances, and a refutation needs exhaustive nonexistence beyond reach.',
   coverage='none', remaining='A general construction of PDFs with the (s**) and (**s) symbols.', files=[], credit=0),
 349136: dict(outcome='parked_asymptotic', review_depth='primary HTML conjecture statement read',
   result='Asymptotic statement about the fraction of regular bipartite graphs; not finitely refutable; source studies a weaker conjecture.',
   coverage='none', remaining='Probabilistic analysis of matching-count differences for random regular bipartite graphs.', files=[], credit=0),
 350950: dict(outcome='parked_asymptotic', review_depth='primary HTML statement read (Theorems 1, 2 bounds; experiments n = 21, e = 3, 4)',
   result='Eventual sharpness for all e >= 3 and all prime powers q; not finitely refutable in this pass.',
   coverage='none', remaining='Constructions realizing every congruence class for large n.', files=[], credit=0),
 342630: dict(outcome='parked', review_depth='primary HTML statement read (computations to 216 vertices)',
   result='A counterexample needs fullerene generation beyond 216 vertices (buckygen-scale), outside caps; structured nanotube-family comparisons would not refute the claim.',
   coverage='none', remaining='Extremal Wiener index proof for fullerenes.', files=[], credit=0),
 375325: dict(outcome='parked', review_depth='primary HTML scanned (main theorem area <= 1, refined conjecture 8.2, computational checks)',
   result='Refined valley-Delta scaffold exchange; heavy source-specific definitions; authors verified area two over extensive ranges. No mechanism this pass.',
   coverage='none', remaining='Extend the authors\' exchange involution to area >= 2 with per-gap data.', files=[], credit=0),
 375831: dict(outcome='parked', review_depth='primary HTML read (abstract, Lemma 7.3 decomposition, Conjecture 8.3 degree bound, Conjecture 11.2, Corollary 11.3)',
   result='Sub-top coefficient law for remainders R_(a,b); requires the envelope-encoding enumeration machinery and is downstream of the open degree-bound Conjecture 8.3. No mechanism this pass.',
   coverage='none', remaining='Explicit remainder polynomials for d >= 11 or a structural proof via the separable/non-separable split.', files=[], credit=0),
 366840: dict(outcome='parked_analytic', review_depth='primary HTML conjecture statement and abstract read',
   result='Analytic number theory (perturbed shifted powers, k >= 2); the source proves a more general version for k >= 3 and k = 2 remains open. Source-backed disposition only.',
   coverage='none', remaining='The k = 2 multiplicative irreducibility under o(X^{1/2}) perturbations.', files=[], credit=0),
 370189: dict(outcome='parked_famous', review_depth='primary HTML statement read (bounded-degree result)',
   result='Graham-Sloane harmonious labelling conjecture (famous); the source proves the bounded-degree case. Source-backed disposition only.',
   coverage='none', remaining='Unbounded-degree trees.', files=[], credit=0),
}
assert sorted(D) == sorted(ids), set(ids) ^ set(D)
srcmap = {341896: '341896-pdf', 363770: '363770-abs', 368807: '368807-pdf'}
out = {}
for i in ids:
    e = ext[str(i)]; row = e['row']; raw = (L / 'raw' / f'{i}.jsonl').read_bytes()
    assert h(raw) == e['raw_sha256']
    rec = receipt(srcmap.get(i, str(i)))
    out[str(i)] = {
        'mathdb_id': i, 'title': row['title'], 'canonical_url': row['canonical_url'], 'source_url': row['source_url'],
        'first_stated_year': row['first_stated_year'],
        'provenance': {'chunk': e['chunk'], 'line_one_based': e['line'], 'chunk_sha256': e['chunk_sha256'], 'raw_line_sha256': e['raw_sha256'],
                       'raw_file': f'raw/{i}.jsonl', 'statement_sha256': h(row['statement'].encode())},
        'source_receipt': {k: rec[k] for k in rec if k in ('url', 'utc', 'status', 'sha256', 'error')} if rec else None,
        'historical_check': 'only inventory/coverage entries (root-mathdb-coverage-queue-r309 statement_screen, pi-mathdb-full-corpus-inventory-r301 tags); no prior lane notes',
        **D[i]}
(L / 'results.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
print(len(out), 'entries')
