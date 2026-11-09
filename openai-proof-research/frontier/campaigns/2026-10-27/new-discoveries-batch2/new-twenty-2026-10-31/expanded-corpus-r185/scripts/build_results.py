import json, pathlib
L = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((L / 'extracted.json').read_text()); rec = json.loads((L / 'outputs/fetch-receipts.json').read_text())
def receipts(prefixes):
    out = {}
    for r in rec:
        if any(r['id'].startswith(p) for p in prefixes) and 'status' in r:
            out[r['id']] = {k: r[k] for k in ('url', 'status', 'sha256', 'utc')}
    return out
D = {}
def put(i, outcome, depth, summary, computation=None, credit='none', extra=(), src=None):
    i = str(i); e = ex[i]; s = src or i
    D[i] = dict(mathdb_id=int(i), title=e['title'], source_url=e['source_url'], provenance=e['provenance'],
                source_receipts=receipts([s + '-abs', 'eprint-' + s] + list(extra)), outcome=outcome, review_depth=depth,
                summary=summary, computation=computation, credit_claim=credit)

put(342653, 'PARKED_BOUNDED_VERIFICATION',
 'arXiv v2 (current) TeX read: homogeneous braids, Conjecture HBGR (Artin-Tits presentation of HBM(e)), Proposition (Murasugi), Lemma Inequalities, Theorem HomogeneousAreGeodesic, Remark (minimal diagrams keep the sign vector), Conjecture Wreathlike (line 389); web searches (no resolution; Alekseev 2024 Algebra i Analiz extends minimality to closed braids)',
 'Weak form of the source\'s HBGR conjecture. Two remarks. (1) With at most two homogeneous blocks the claim already follows from the source: homogeneous words are geodesic, so the length P+N is invariant, and the exponent sum P-N is invariant. The first open case therefore has three blocks, e.g. e = (+,+,-,+). (2) The paraphrase is ambiguous when an index is absent from a word: the block numbering then depends on an arbitrary sign choice. That is a wording defect worth zero credit, not a counterexample. Exhaustive computation over all e-homogeneous words, with braids identified by the faithful Artin action on F_n: no braid has two words with different block counts, up to length 12 for ++-+ (543,100 braids at length 12) and +--+ (444,276), and up to length 11 for ++-++ (554,077). Moreover the number of distinct braids at each length equals the Saito growth series of the conjectured Artin-Tits monoid, so HBGR itself holds up to those lengths. A Burau-minor invariant route was tested and fails: on sigma2 sigma3^-1 sigma4^10 sigma3^-1 sigma2 sigma1 the 2x2 principal minor has max t-degree 11, while c_0 = 3. No proof, no counterexample.',
 'scripts/braid_blocks.py, artin_growth.py, burau_blocks.py, burau_word.py; logs/braid-*.log')
put(342833, 'PARKED_DEEP',
 'arXiv v2 (ALCO 2020) TeX read: Conjecture conj:positivity (lines 204, 332), Theorems for n <= 4; BHMPS arXiv:2102.07931 v4 TeX read (Section positivity: convex-curve Schur-positivity conjecture, which would imply Negut\'s); web search',
 'Negut positivity for nonincreasing sequences is still open. BHMPS proves Schur positivity only for paths under a line and conjectures the convex-curve generalisation. A statement over all n; Schur positivity of shuffle-algebra elements is not a finite target in capped Python. Disposed.', extra=('bhmps2102.07931',))
put(343087, 'PARKED_DEEP',
 'arXiv v1 abstract read (Shi: Fuglede holds on Z_{p^2} x Z_p); family warning',
 'Tile => spectral in Z_{p^n}^d for all p, n, d: a deep open Fuglede-type statement. Known cases: cyclic p-groups, Z_p^2, Z_{p^2} x Z_p, and later Z_p x Z_{p^n}. No finite certificate route at feasible sizes (tiles of Z_4^3 or Z_8^2 cannot be enumerated in capped Python). Disposed per the brief.')
put(343127, 'PARKED_DEEP',
 'arXiv v3 (SODA 2020) abstract and latest TeX read (Conjecture conj:main, Brakensiek-Guruswami, lines 355-362)',
 'The Brakensiek-Guruswami PCSP hardness conjecture for all non-bipartite loopless pairs is a flagship open complexity conjecture. Not finite; disposed.')
put(343222, 'PARKED_DEEP',
 'arXiv v4 (Discrete Math 2022) TeX read: definitions of cover, strictly f-degenerate transversal; Problem 4 conjecture (line 817) after Thomassen\'s theorems; web search (no resolution; Nakprasit partial for f in {0,1,2}; Li-Wang minor-free extensions)',
 'Planar positive-valued cover conjecture (sum f >= 5, s >= 2). For list or partition versions this specialises to Thomassen (forest + 2-degenerate; independent set + 3-degenerate) and Dvorak-Postle (DP-5). A minimal counterexample needs min degree >= 5 (>= 12 vertices) together with a cover and an f-assignment, a search space far beyond capped Python without SAT (which this lane forbids). Disposed.')
put(343238, 'RESOLVED_BY_LITERATURE_ROUTINE_BRIDGE',
 'arXiv v1 (only version) TeX read: Conjecture red / Conjecture 3 (lines 86-91, 389-392), Laplacian L = d_{k-1} d_{k-1}^T (line 306), proofs for t = 1, 2 and the last partial sums; Abebe-Pfeffer 2012 REU report (Reiner REU site) read (three variants; SAGE found no counterexamples); Lew arXiv:2508.04209 TeX read (Theorem 1.3 thm:degree_bound, Corollary 1.4, Conjecture conj:higher_brouwer, Section conclusion); Kothari-Tudose arXiv:2606.12197 abstract (Brouwer\'s conjecture proved); Huang arXiv:2607.20051 and Zhang-Song-Fan arXiv:2607.20910 TeX read (Duval-Reiner counterexamples; Huang\'s seeds F16 and F15 have s_5 about 33+ while Abebe\'s bound is 67)',
 'TRUE in full scope. k = 2 is Brouwer\'s conjecture, proved by Kothari-Tudose (2026). For k >= 3 (r = k-1 >= 2) it follows in about ten lines. Lew\'s Theorem 1.3 bounds s_t by the sum of the (r+1)t largest ridge degrees, which is at most r f_r + |F\'|, where F\' is the set of facets whose whole boundary lies in the chosen (r+1)t ridges. Lovasz\'s Kruskal-Katona theorem together with C(t+r, r) >= (r+1)t (valid for r >= 2) gives |F\'| <= C(t+r, r+1). For (r+1)t > f_{r-1}, the trace bound plus the same Kruskal-Katona estimate applies. Lew does not state this consequence, and no source found does. It is a routine bridge from published and classical results, so zero credit is expected (outputs/343238-bridge-proof.md). Numerical diagnostic: random pure 2- and 3-complexes, maximum excess 0.',
 'scripts/abebe_check.py; logs/abebe-check-r2.log, logs/abebe-check-r3.log',
 credit='none (routine bridge: Lew 2025 Thm 1.3 + Lovasz-Kruskal-Katona; k=2 is Kothari-Tudose 2026)',
 extra=('reu2012', 'lew2508.04209', 'eprint-lew2508.04209', '2606.12197', 'eprint-huang', 'eprint-zsf', '2607.20051', '2607.20910'))
put(343390, 'PARKED_DEEP',
 'arXiv v1 (APAL 2022) abstract read; closing conjectures on the Sigma_1 and Sigma_2 theories',
 'Undecidability of the Sigma_1 theory of Young\'s lattice with all constants is a logic or decidability statement with no finite certificate. Disposed. The Omega Library card gomezaiza2026younglattice was checked and is unrelated.')
put(343391, 'PARKED_DEEP',
 'arXiv v1 abstract read; same source as 343390 (pair warning)',
 'Undecidability and non-finite-axiomatizability for all nontrivial differential posets: model-theoretic, infinite, and a pair variant of 343390. Disposed.', src='343390')
put(343468, 'PARKED_CHECKED_WITHIN_AUTHOR_RANGE_NO_PROOF',
 'arXiv v1 (Gao-Gu) TeX read: Section 4.4 Conjecture (Postnikov) and its generalisation to weights (2x+1)^{2k}; Postnikov "Counting Morse curves and links" (math.mit.edu brief) read: Conjecture 3.4 (alpha bits, records, d2(R_n) = s(n) + t_alpha(n-2) + 1) verified there for n <= 100,000 with the 2-adic integer pinned mod 2^20 (549719); RSI 2025 report (Pramatarova) and arXiv:2510.14956 abstract (periodicity only); web searches',
 'Independent exact computation of L_n (weights (2h+1)^2) and v2(L_n - C_n) for 2 <= n <= 3500: consistent with v2(L_n - C_n) = s2(n) + v2(n - alpha) + 2, with alpha = 9047 mod 2^14 (binary 10001101010111; low six bits 010111 as stated) and record values matching Postnikov\'s (343, 855, 9047). Postnikov\'s own check reaches n <= 100,000, so no counterexample is reachable here. A proof needs new 2-adic theory beyond Postnikov-Sagan and Gao-Gu. Parked.',
 'scripts/morse2adic.py; logs/morse-200.log, morse-1200.log, morse-3500.log', extra=('rsi/', 'multicat'))
put(343505, 'RESOLVED_PUBLISHED',
 'arXiv v1 abstract read; Xia-Zhang-Zhang-Zhu, A complete classification of shuffle groups, arXiv:2304.01037 v4 = Forum Math. Sigma 12 (2024) e104: abstract and TeX read (Conjecture conk, line 234; Remark, line 238 on the parity determination; Theorem confirming all cases)',
 'Known result. Xia-Zhang-Zhang-Zhu prove that G_{k,kn} contains A_{kn} for k >= 3, n not a power of k, and (k,n) != (4,2^f). Their Remark (after Medvedoff-Morrison Theorem 1) shows that G_{k,kn} <= A_{kn} exactly when n = 0 mod 4, or n = 2 mod 4 with k = 0,1 mod 4. This is precisely the Alt/Sym split in the MathDB statement, which is therefore fully proved (published 2024). Zero credit.', extra=('343505-xzzz', 'eprint-343505-xzzz'))
put(343851, 'PARKED_DEEP',
 'arXiv v3 (JGT) latest TeX read: finite character definition (line 1405), problems at lines 1440 and 1453',
 'Infinite-hypergraph Konig property (finite character): an infinite combinatorics statement with no finite certificate. Disposed.')
put(343852, 'PARKED_DEEP',
 'Same source as 343851 (pair warning); latest TeX line 1453',
 'Finite-extension Konig variant (stronger form of 343851): infinite, and a pair variant. Disposed.', src='343851')
put(344346, 'RESOLVED_PUBLISHED',
 'arXiv v1 (EJC 2020) TeX read: Conjecture 1 (Coll-Mayers-Mayers), Theorem 1, concluding conjectures (lines 465-490); Craig arXiv:2112.09269 v5 abstract + TeX read (proof of non-negativity of 1/(q,-q^3;q^4)_inf; Chern arXiv:1912.10341 for n > 2.4e14 plus computation)',
 'The sign conjecture is equivalent to non-negativity of 1/(q,-q^3;q^4)_infinity (Seo-Yee Theorem 1), which was proved by Craig (circle method + Euler-Maclaurin + finite check to 350,000). Known result, zero credit.', extra=('craig', 'eprint-craig'))
put(344347, 'PARKED_ANALYTIC',
 'Same source as 344346: concluding conjecture for O^d (non-negativity of 1/(q,-q^{4d-1};q^{4d})_inf); Craig\'s footnote: only m = 4 proved, general m >= 4 still conjectured',
 'For every d >= 1 the claim is coefficient positivity of an infinite product, i.e. circle-method analysis plus a finite check for each d (d = 1 done by Craig). Uniform in d and analytic, so no finite certificate; also a parameter variant of 344346. Parked.', src='344346', extra=('craig', 'eprint-craig'))
put(344370, 'PARKED_DEEP',
 'arXiv v3 (Discrete Analysis 2022) latest TeX read (free elevation discussion, lines 236-302; Conjecture conj:rank)',
 'Free-elevation rank formula for K_{d+2}-matroids for all d (known d <= 3). Computing free elevations of rank-C(d+2,2) truncations is not feasible in capped Python. Deep; disposed.')
put(344494, 'PARKED_STRUCTURED_SEARCH',
 'arXiv v1 (JGT 2021) TeX read (Conjecture AddConjecture; computer search to order 8); Cambie-Chen-Hao-Tokar arXiv:2308.12808 abstract; Cambie-Jooken-Wagner arXiv:2508.20593 v2 (Sept 2026) TeX read: Conjecture conj:main2(b) still open, Theorem thr:strong_counterexamples (barbell D_{n,w}: only one edge class increases mu), commented exhaustive check n <= 10; GitHub JorikJooken/averageSubtreeOrderOfGraphs noted',
 'The weaker Cameron-Mol conjecture is still open as of Sept 2026 (CJW v2 proves K_n is the maximum but leaves the edge-addition conjecture open). Exact tools: mu(G+uv) is obtained from ordered pairs of disjoint subtrees containing u and v respectively. They reproduce Cameron-Mol\'s K_{2,n-2} decrease from n = 8. Structured searches all found some increasing non-edge: barbells (w <= 5, n <= 12), closed-form K_{a,b} for a <= 14 and b <= 30 (the large-side edge always increases, delta about c/a), and complete multipartite graphs such as 2,3,9 / 2,4,8 / 3,4,12 / 2,6,6 / 1,1,6,6 (the largest part always increases). Asymptotic reasoning (CJW Case 4) shows that a P3 through a clique vertex in clique-dominated graphs always increases, so a counterexample must avoid dominant cliques. No counterexample, no proof.',
 'scripts/msto.py, msto_families.py, msto_kab.py, msto_multi.py; logs/msto-*.log', extra=('cjw2508.20593', 'eprint-cjw2508.20593', '2308.12808'))
put(344509, 'PARKED_DEEP',
 'arXiv v2 (DCG 2023) latest TeX read (Morales conjecture line 149; Lee-Liu prove the 3rd and 4th coefficients positive); web search (no resolution)',
 'Ehrhart positivity of Tes_n(1,...,1) and of the CRY polytope for all n: the polytopes have dimension about n^2/2, and computing Ehrhart polynomials beyond tiny n is outside capped Python. Disposed per the brief.')
put(344759, 'PARKED_DEEP',
 'arXiv v3 (current) TeX read: the conjecture is renamed "bold bouquet" (Conjecture introbouquet, line 80), still open; lattice-like bouquets proved (Theorem latticeboq)',
 'Colourings of the whole plane: an infinite geometric Ramsey statement with no finite certificate. Disposed.')
put(344776, 'PARKED_SOURCE_FIDELITY_NOTE',
 'arXiv v1 (SIAM DM 2021) TeX read (Theorem thm:2-conn at x = k; Conjecture conj:tomescu-2conn); Yang arXiv:2310.16382 TeX read (Brown-Erey conjecture with bound (x-1)_{k-1}((x-1)^{n-k+1}+(-1)^{n-k}); proved when omega = k or alpha = 2; "wide open")',
 'The MathDB paraphrase writes (x)_k instead of (x-1)_{k-1}. That bound is x/(x-1) times weaker, and its equality clause is then literally false (G_{n,k} attains the smaller value). This is a paraphrase defect worth zero credit; we work from the source. Source conjecture: proved at x = k (EEFH), for omega = k or alpha = 2 (Yang), and for very large x (Brown-Erey). Analysis: attaching long ears to a core H reduces the comparison to Tomescu\'s general-x bound, proved for k = 4, 5 by Knox-Mohar, and cores with omega < k are denser. No promising finite counterexample route. Parked.', extra=('2310.16382', 'eprint-yang'))
put(344926, 'PARKED_EXTENDED_VERIFICATION',
 'arXiv v2 (current) TeX read: Meszka / Pasotti-Pellegrini conjecture (lines 160-176; prime case solved by Preissmann-Mischler); Pasotti-Pellegrini 2016 (arXiv:1404.3890) verified v <= 23 (per search abstract); web searches (no later extension)',
 'Exact search with an exhaustive DFS (memoised, parity-pruned, MRV), with every found realisation re-verified. All boundary lists were realisable: v = 25, lists within 2 of the multiples-of-5 bound (9,240 lists); v = 27, within 1 of the bounds for 3 and 9 (24,957); v = 33, exactly at the bounds for 3 or 11 (54,264); v = 35, exactly at the bounds for 5 or 7 (24,480). An early timeout on v = 27 was an artefact of DFS ordering and was resolved by the improved solver. A refutation would in any case be a nonexistence certificate, expensive in Lean. This is near the parked 329760 Alspach sequencing family. Parked.',
 'scripts/nearfactor.py, nearfactor_tight.py, nf_solver.py, nf_tight2.py; logs/nf*-*.log')
assert len(D) == 20, len(D)
r = json.loads((L / 'reservation.json').read_text())
assert sorted(map(int, D)) == sorted(r['ids'])
(L / 'results.json').write_text(json.dumps(D, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(D))
