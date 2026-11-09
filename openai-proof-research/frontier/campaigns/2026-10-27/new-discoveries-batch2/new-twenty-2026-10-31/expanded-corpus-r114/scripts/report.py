# Builds results.json (exactly 20 ID-keyed dispositions) from extracted.json, source receipts and lane outputs.
import json, pathlib, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
X = json.loads((D / 'extracted.json').read_text())
R = json.loads((D / 'reservation.json').read_text())
meta = {r['mathdb_id']: r for r in R['rows']}

def rec(name):
    p = D / 'sources' / f'{name}.receipt.json'
    return json.loads(p.read_text()) if p.exists() else None

def out(name):
    p = D / 'outputs' / name
    return dict(path=str(p.relative_to(D)), sha256=hashlib.sha256(p.read_bytes()).hexdigest()) if p.exists() else dict(path=name, missing=True)

OLD = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign/outcomes'
E = {}
E[368078] = dict(outcome='parked_hard_infinite', review_depth='source conjecture text read (Conjectures 2.4/2.5 context, numerical normality evidence to k = 2^20)',
    disposition='Normality of an infinite word tied to Collatz-type iteration; famous-hard analytic/number-theoretic item. No finite certificate can settle normality; no tractable mechanism.',
    attempts=[], remaining='A proof of normality of <sat(infinity)> (at least as hard as Collatz-adjacent equidistribution); no counterexample route since normality is a limit property.')
E[368244] = dict(outcome='parked_hard_analytic', review_depth='source abstract, Section 4 numerical methods and Conjectures 5.2-5.5 located',
    disposition='Axisymmetry of magnetic Dirichlet ground-state minimizers in R^3: analytic shape optimization, numerical evidence only. Out of scope for finite search and Lean.',
    attempts=[], remaining='Existence/regularity of minimizers and a symmetrization argument compatible with the magnetic field; no known rearrangement inequality applies.')
E[368305] = dict(outcome='parked_finite_search_infeasible', review_depth='source rules (Section 1), Conjecture 4, Proposition 5 and computer-verification statement read',
    disposition='The source (arXiv:2505.03497) already extends the original n <= 6 check to n <= 8 by computer and to n <= 9 via its Proposition 5 (n = 3 mod 4 implies n = 1 mod 4). The next open case n = 10 is a 45-edge positional game on K_10; even with S_10 symmetry the position space (about 3^45/10!) is far beyond the lane caps in Python. No structural reduction found beyond the source.',
    attempts=['Read exact rules: Alice and Bob alternately colour edges of K_n; score = #vertices majority red minus #majority blue; s_VC(n) optimal score.'],
    remaining='Optimal play for VC(10) or a general pairing/strategy argument for n = 0, 2 mod 4 and n = 3 mod 4.')
E[368317] = dict(outcome='excluded_published_resolution', review_depth='source statement read; live prior art abstract read (arXiv:2512.12251 v2)',
    disposition='Resolved: S. Babu, G. Di Stefano and A. Lakshmanan S., "Mutual-visibility Coloring of Graphs", arXiv:2512.12251 (v1 13 Dec 2025, v2 12 Feb 2026), prove that determining the mutual-visibility chromatic number is NP-complete even for graphs of diameter four with mutual-visibility chromatic number two (reduction from NAE3-SAT). Zero credit.',
    attempts=[], receipts_extra=[rec('prior-2512.12251-abs.html')], remaining='None (resolved in the literature).')
E[368352] = dict(outcome='parked_bounded_search_no_counterexample', review_depth='source Conjecture 8.1 and verification list (v3, July 2026) read; exact CSF computation implemented and cross-checked',
    disposition='No counterexample found in the source coverage gap that was searched. The source (v3) verifies distinctness for 3-cycle graphs at odd n <= 15, 5-cycle graphs n <= 15, 4-cycle n = 14..17 and c >= 6 n <= 16. This lane computed exact chromatic symmetric functions (Stanley power-sum subset expansion via rooted-tree DP plus cycle-edge subsets, cross-checked against brute force on all 143 unicyclic graphs with n <= 8; reproduces the source even-n 3-cycle collisions at n = 6, 8, 10) for every 5-cycle unicyclic graph on n = 16 and n = 17 vertices (beyond the source range n <= 15 for c = 5). n = 16: 50,871 graphs, 50,870 distinct CSFs, exactly one collision pair ((1,0),(2,0),(2,0),(4,2),(7,9)) and ((1,0),(3,0),(2,0),(2,0),(8,57)) in cycle-plus-rooted-tree code, confirmed by independent brute-force subset expansion; both have degree sequence 1^7 2^3 3^5 4, 4 non-trivial rooted trees and 9 internal edges, so the conjecture holds (this shows CSF no longer distinguishes 5-cycle unicyclic graphs at n = 16, a fact beyond the source list). n = 17: 145,146 graphs, all CSFs distinct.',
    attempts=['scripts/csf.py, scripts/csf_chunk.py, scripts/csf_merge.py, scripts/csf_selftest.py, scripts/csf_pair_check.py'], outputs=['csf-c5-n16-merge.json', 'csf-c5-n17-merge.json', 'csf-c5-n13-merge.json', 'csf-c3-n10-merge.json'], remaining='c = 3 at n = 17 (about 300k graphs) not run; a general proof would need star-basis recovery of degree sequences, rooted-tree counts and internal edges for unicyclic graphs.')
E[368397] = dict(outcome='excluded_source_refuted', review_depth='source abstract, Section 1 (lines on Zheng-Sun revised conjecture, computer search) and Section 3 construction read',
    disposition='The source arXiv:2505.08131 itself disproves the revised conjecture: among connected graphs of order 11 its computer search finds three counterexamples to the generalized Kriesell conjecture, one non-regular, and Theorem 3.x constructs infinite non-regular families (e.g. K_n box P_3, minimally (n+1)/3-tough). The MathDB text itself records this. Zero credit.',
    attempts=[], remaining='None.')
E[368742] = dict(outcome='parked_bounded_search_no_counterexample', review_depth='source Conjecture 1.2, Theorem 3.1 (super-additivity over disjoint induced subgraphs) and verification statement (all connected graphs n <= 9, Mathematica database n <= 100) read',
    disposition='No counterexample. Exhaustive (with repetition) over all connected graphs with cyclomatic number 2 for n <= 13 (909,935 graphs at n = 13) and cyclomatic number 3 for n <= 10; minimum of s+ - n is 0.569 (c = 2, n = 13) and 1.498 (c = 3, n = 10). Edge-swap annealing at n = 16..40 (c = 2, 3, 4, 6) found the c = 2 minimum plateauing near 0.54 and margins growing with c. Since s+ - n = (c - 1) + (s+ - s-)/2, a counterexample needs (s- - s+)/2 > c - 1; observed sparse extremals stay far from that.',
    attempts=['scripts/strong_positive.py, scripts/strong_local.py'], outputs=['strong-c2-n4-12.json', 'strong-c2-n13.json', 'strong-c3-n5-10.json'],
    remaining='A proof for sparse graphs (c = 2, 3) is the bottleneck; the source gluing lemma handles claw-free unicyclic only.')
E[368743] = dict(outcome='parked_bounded_search_no_counterexample', review_depth='source Proposition 9.1 (cycles), Conjecture 9.1 and the "checked up to 9 vertices" statement read',
    disposition='No counterexample. Since s+ + s- = 2m = 2n for unicyclic G, the conjecture is a sign condition on D = sum lambda|lambda| / 2. Exhaustive isomorphism-class enumeration of all odd-cycle unicyclic graphs for n <= 15 (counts match OEIS A001429 splits; 40,708 + 17,844 + 5,433 + 1,029 + 114 + 8 + 1 graphs at n = 15) found no violation; signed margins shrink (k = 9: 0.0018 at n = 15). Local search at n = 20..40 for k = 5..13 reached margins down to 1e-5 (k = 13, n = 30) but always on the conjectured side; extremals are near-uniform leaf coronas. For the uniform t-leaf corona of C_k, sum lambda|lambda| = sum_j mu_j sqrt(mu_j^2 + 4t), and expanding sqrt(4t + mu^2) in powers of mu^2/(4t) kills every term with an odd power of mu below k (tr A^r = 0 for odd r < k), so the leading term is 2 sqrt(t) binom(1/2, j) tr(A_{C_k}^k) / (4t)^j with j = (k-1)/2 and tr(A_{C_k}^k) = 2k; its sign (-1)^(j+1) is positive for k = 3 mod 4 and negative for k = 1 mod 4, exactly as conjectured. So the conjecture is consistent with asymptotics and likely true.',
    attempts=['scripts/unicyclic.py, scripts/unicyclic_local.py'], outputs=['unicyclic12.json', 'unicyclic13-15.json'],
    remaining='A proof (e.g. moment/sign expansion of tr(A|A|) controlled by odd closed walks); Lean would need spectral sign counting for an infinite family.')
E[368745] = dict(outcome='parked_bounded_search_no_counterexample', review_depth='source Conjecture 9.5, the sharpness examples and Theorem 3.1 read',
    disposition='No counterexample. Maximal outerplanar: all labelled polygon triangulations n = 4..14 (208,012 at n = 14); s+ - 2n is negative exactly for n <= 7 and its minimum increases about 0.3 per vertex (0.225 at n = 8, 2.103 at n = 14; fan-type extremals). Maximal planar: exact flip-graph BFS enumeration with embedding canonical codes (counts 1, 2, 5, 14, 50, 233, 1249, 7595 match OEIS A000109); s+ - 3n fails exactly for n <= 9 and is 0.246, 0.654, 1.165 at n = 10, 11, 12, attained by the source bipyramid C_{n-2} v 2K_1. Thresholds are exact and margins increase.',
    attempts=['scripts/outerplanar.py, scripts/planar_flip.py'], outputs=['outerplanar-4-14.json', 'planar-n10.json', 'planar-n11.json', 'planar-n12.json'],
    remaining='Proof needs new ideas: Theorem 3.1 only lower-bounds by disjoint induced pieces and loses inter-piece edges; Lean planarity infrastructure absent.')
for i, lab, extra in [(368967, '3-sum formula (Conjecture 1.15)', 'N_2 of 3-sums'), (368970, '4-edge-twist congruence (Conjecture 1.21)', 'g mod t^3 under 4-edge twists'),
                      (368973, 'K_{3,n} and K_{1,1,1,n} formulas (Conjecture 4.7)', 'closed forms, verified by the source for all n <= 60')]:
    E[i] = dict(outcome='parked_beyond_source_computation', review_depth=f'source {lab}, data-set description (all simple biconnected min-degree-3 graphs with < 10 vertices or < 22 edges, 3,293,662 graphs) and algorithm section located',
        disposition=f'Speyer g-polynomial ({extra}). The source computed g for its full data set with a dedicated covaluative algorithm; this lane has no implementation of Speyer polynomials and cannot exceed that coverage within caps. Speyer g-polynomials are not in Mathlib (definition via K-theory of the Grassmannian or the Ferroni-Schroter covaluative recursion), so a Lean endpoint is not feasible.',
        attempts=[], remaining='A structural proof (e.g. symbolic evaluation of Algorithm 2 over the explicit cyclic-flat lattice of K_{3,n}, which the source describes) plus a formal g-polynomial theory.')
E[369280] = dict(outcome='excluded_historical_known_and_formalized', review_depth='historical campaign outcome and review read (2026-10-25 twenty-proof-campaign/outcomes/shuffle-quadratic)',
    disposition='Already handled by this project: the quadratic eigenvector is a known result resolved by Tripathi, formalized as shuffle-quadratic (MathDB 369280) in the 2026-10-25 twenty-proof campaign; the independent review recorded zero new mathematical resolution. Unindexed old exclusion retained; route stopped.',
    attempts=[], receipts_extra=[dict(path=f'{OLD}/shuffle-quadratic/outcome.json', sha256='243bce35fb6c0d458a5eeff52074ed5ec8ebd11627294c0e06dc3cded0311192')], remaining='None.')
E[369281] = dict(outcome='excluded_historical_endpoint_correction', review_depth='historical campaign outcome read (2026-10-25 twenty-proof-campaign/outcomes/shuffle-spectrum)',
    disposition='Already handled by this project: shuffle-spectrum (MathDB 369281) proved the displayed ceiling endpoint false at n = 4 (1/16 absent), recorded as an index-range correction with no priority claim. Endpoint corrections are zero credit; route stopped.',
    attempts=[], receipts_extra=[dict(path=f'{OLD}/shuffle-spectrum/outcome.json', sha256='547801de6f4d3b1002b81850ecc59f47f4d805d0b4824fa6542e7ec5c356db37')], remaining='None.')
E[369568] = dict(outcome='excluded_live_registry_proof', review_depth='Omega registry problem file read (cached copy) and current Problems tree path confirmed at Omega HEAD ddeafbc85f06ddade64bc7aab47c37698ecd7fe6',
    disposition='The Omega registry (the-omega-institute/trureturing) has Problems/caldwell-2024-super-catalan-action-graph-ntable.md (current blob 98ba7ce4a491b09cd9b15177b4908c7b57c197b0), whose frozen Lean declaration D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.result proves the identity for every n (preregistration issue #14721). Zero credit.',
    attempts=[], receipts_extra=[dict(path='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/Problems/caldwell-2024-super-catalan-action-graph-ntable.md', sha256='23c8c83c7d944699ecb0202d61dc11b34524d19882c20b87c245595346eebc3a', note='cached older tree copy; path present in current tree')], remaining='None.')
E[369616] = dict(outcome='excluded_public_refutation_independently_rediscovered', review_depth='source Conjecture 4.12, Theorem 4.13 use, dense-case remark read; exact counterexample computed; prior art abstract read',
    disposition='Refuted, but already public. This lane independently found (by annealing, then exact verification) the connected 14-vertex, 16-edge cactus C5 - bridge - C4 (entered/left at adjacent vertices) - bridge - C5 with In(L(G)) = (9, 0, 7) by the integer characteristic polynomial and Descartes rule of signs (exact since all roots are real), and an infinite family C_{4a+1} - C_{4b} - C_{4c+1}. The identical 14-vertex cactus with inertia (9,0,7), a 48-vertex example and unbounded signature appear in arXiv:2607.22874 (v1 24 Jul 2026, v2 29 Jul 2026), "The signature of connected line graphs is unbounded" (also SSRN preprints by A. Paone). Zero credit. Side note: the source line "for any tree T, s(L(T)) <= -1" is false (L(P5) = P4 has signature 0); Guo theorem gives s <= 1, which still suffices for trees.',
    attempts=['scripts/line_inertia.py (exhaustive c=1 n<=15, c=2 n<=13, c=3 n<=13, c=4 n<=9: no violation)', 'scripts/line_local.py, scripts/verify_line.py, scripts/line_chain.py'],
    outputs=['line-local-20-24.json', 'line-min/n14-m16.json', 'line-inertia-c3-n12.json'], receipts_extra=[rec('prior-2607.22874-abs.html'), rec('prior-2607.22874.html')], remaining='None (publicly refuted).')
E[369640] = dict(outcome='parked_hard', review_depth='source Conjecture (Section 6, after Proposition 6.5) read; "based on computations for m <= 8"',
    disposition='Equivalence criterion for m-intersection number zero of plabic graph positroid varieties; requires positroid/cluster computations not available in the lane and no finite counterexample mechanism with feasible certificate; Lean infrastructure absent.',
    attempts=[], remaining='Necessity direction of Proposition 6.5 for all m.')
E[369642] = dict(outcome='parked_beyond_source_computation', review_depth='source Conjecture 6.35 and its verification note read',
    disposition='The source records computational verification (G. Edwards) for all 7 <= n <= 26; extending requires tropical prevariety computations (gfan-type) unavailable here. Lean: no tropical/Dressian library.',
    attempts=[], remaining='A structural description of the reduced Dressian of T_n.')
E[369839] = dict(outcome='parked_bounded_search_no_counterexample', review_depth='source Appendix A (Proposition A.1 classes, Conjecture A.2, verification of first 30 / 37 S-fraction coefficients) read',
    disposition='No counterexample. Exact O(n^3) DP for P_n(x) (state = rank of last entry; Class 1 via 1-23, Class 2 via 1-32; cross-checked by brute force n <= 7, Bell numbers at x = 0, n! at x = 1) and quotient-difference S-fraction coefficients (checked against exact rational inversion) gave 90 positive coefficients for both classes at x = 1/100, 1/2, 3, 100 (authors: 30 and 37 as rational functions). Pointwise checks only, not a proof for all x >= 0.',
    attempts=['scripts/vincular.py'], outputs=['vincular-dec-N90-x1_100.json', 'vincular-dec-N90-x1_2.json', 'vincular-dec-N90-x3.json', 'vincular-dec-N90-x100.json'],
    remaining='Positivity of all S-fraction coefficients as rational functions on x >= 0 (no closed-form continued fraction known for Classes 1, 2).')
E[370017] = dict(outcome='parked_hard_complexity', review_depth='source Conjecture 1.1/1.6 location and statement read',
    disposition='Average-case computational hardness for online balanced independent sets in dense random bipartite graphs; unconditional hardness against all polynomial-time algorithms would imply a P != NP-strength separation; the source supplies only restricted-model (online / overlap-gap style) evidence. No finite route.',
    attempts=[], remaining='An unconditional low-degree/OGP-type lower bound for all polynomial-time algorithms (not known in this generality).')

src_key = lambda o: o['source_url'].rsplit('/', 1)[-1] + '.html'
res = {}
for k in sorted(R['ids']):
    o = X[str(k)]; e = E[k]
    res[str(k)] = dict(mathdb_id=k, title=o['title'], source_url=o['source_url'], first_stated_year=meta[k]['first_stated_year'],
        literal_statement=o['statement'], provenance=o['provenance'], source_receipt=rec(src_key(o)),
        outcome=e['outcome'], review_depth=e['review_depth'], disposition=e['disposition'], attempts=e.get('attempts', []),
        outputs=[out(p) for p in e.get('outputs', [])], extra_receipts=e.get('receipts_extra', []), remaining=e['remaining'],
        credit='zero unless root accepts; no self-acceptance', lean_packet=None)
assert len(res) == 20
(D / 'results.json').write_text(json.dumps(res, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(res), {v['outcome'] for v in res.values()})
