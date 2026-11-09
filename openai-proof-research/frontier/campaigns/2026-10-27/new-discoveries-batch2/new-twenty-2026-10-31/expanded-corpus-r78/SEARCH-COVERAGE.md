# Search coverage records (expanded-corpus-r78, 2026-11-01)

Every run used `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB. Full logs and receipts are in `logs/`. All numerical results are diagnostics, not proofs, except where a Lean endpoint is stated (334207).

## 329078: Burns–Jonoska–Saito Conjecture 3.2 (two-value genus ranges)

* Definition (source Def. 2.1, Lemma 3.1): each chord end is attached inside or outside the annulus (4^n thickenings). Genus is g = (n − b + 2)/2, where b is the number of boundary components. The computation counts faces of the equivalent rotation systems on the cubic graph (backbone 2n-cycle plus n chords): `scripts/genus/gr.js`.
* Validation: reproduces the paper's GR_n sets for n = 1..6 exactly. Also reproduces gr(123123) = [1,2], gr(12341342) = [1,2], gr(12312345674675) = [2,4] and gr(123132) = [0,2] (`logs/genus-validate-n7.log`; the n = 7 brute force was killed by the CPU cap as expected).
* Search space: all linear perfect matchings on 2n points, which cover every chord diagram, for n = 3..12. Pruning by source Lemma 4.4: a sub-diagram 123321 forces ≥ 3 genera. Pruning was validated: pruned and unpruned runs give identical width-1 counts for n = 3..6 (`logs/genus-noprune-n*.log`).
* Per diagram: random samples, then hill climbing, then an exhaustive Gray-code enumeration of all 2^{2n−1} rotation systems, with early exit once face counts differ by ≥ 4.
* Pruned leaves: n=8: 21,633; n=9: 95,112; n=10: 414,482; n=11: 1,792,296; n=12: 7,698,258.
* Result: no diagram with genus range [g, g+1], g ≥ 2. The width-1 linear matchings number 2n + 2 for each n (2 of type {0,1}, 2n of type {1,2}).
* n = 13: 30 partitions exceeded the CPU cap, so the search is incomplete; the background loop was stopped.

## 341374: χ''(L(K_n)) = 2n − 3 (Vignesh–Geetha–Somasundaram)

* Direct SAT (CaDiCaL bundled with Lean; the model is independently re-verified in Python): Type 1 for n = 4..11 (`logs/total-lk4..11.log`). n = 12, 13, 14 were inconclusive at the 100 s solver limit.
* Z_n-equivariant ansatz: V = Z_n for n odd, or Z_{n−1} ∪ {∞} for n even; φ({i,j}) = (i+j)/2; orbit and fixed colours (`scripts/total/zn.py`). It found verified Type-1 colourings for n = 5, 8, 9, 12, 13 (`logs/total-zn12.log`, `logs/total-zn13.log`). It is UNSAT for n = 6, 7.
* 1-factorization opposite-edge framework (`scripts/total/reduced.py`): SAT for n = 5, 9; UNSAT for n = 6, 7.
* Combined coverage: Type 1 for every 2 ≤ n ≤ 13.

## 322842: k-coloured kernels in l-quasi-transitive digraphs

* Positive control: the source Theorem 5 cycle C_{2k+2} with paired colours has no k-coloured kernel for k = 2, 3, 4 (`logs/kernel-control.log`). Since every digraph is 1-quasi-transitive, this also shows the literal statement fails at l = 1.
* Circulant 4-QT digraphs on Z_N, N = 7..16, with ≤ 3 offsets: none reaches diameter ≥ 6 (`logs/kernel-circ-l4.log`).
* Structured random strong l-QT digraphs of diameter exactly l+2 (P-skeleton plus up to 5 extra vertices), l = 2..7, 300,000 samples each: the far-pair digraph is always acyclic, Lemma A never fails, and in-radius is 1 or 2 (`logs/kernel-far-l*.log`). Caveat: these samples are biased by the diameter filter. Lemma A is false in general (strong backward tournaments).
* Random small l-QT digraphs, not necessarily strong (l = 2..5, N = 8, 10, 20,000 samples each with 20 random colourings): no kernel-less closure C_{l+1}(D) (`logs/kernel-rand-l*-N*.log`).

## 324248: flashcard bound T_i(n+1) − T_i(n) ≤ 2n

* Exact simulation of the Slow Flashcard Game, p_k = k + 1, validated against the source viewing sequence 1,2,1,2,3,1,3,…
* Through t = 10^8: max over all observed (i, n) of T_i(n+1) − T_i(n) − 2n is 0. Equality occurs 10,842 times. For n ≥ 2 the maximum slack is also 0 (`logs/flash-1e8.log`).

## 322409: Fang–Chen distinct-prime sums

* Exact bitset DP. For every 3 ≤ s ≤ 200 and every l with T_s < l ≤ T_s + 20,000, where T_s = p_2 + … + p_{s+2}, l is a sum of exactly s distinct primes (`logs/primes-s200-m20000.log`). A run up to s ≤ 400 hit the CPU cap.

## 345108: Chapoton–Han Conjecture 5.3

* Exact computation of ρ(x^i(1+x)^j) for 0 ≤ i, j ≤ 40, using N_0^{⌊d/2⌋} on V_d. Reproduces the paper's matrix M_6 rows; no violation (`logs/rho-i40.log`). The conjecture is proved by Han, arXiv:2607.08279, Lemma 26.2 / Remark 26.4.

## 334207: Ding–Zhang–Ge Conjecture 2 (candidate; full Lean endpoint)

* Binary existence of cyclic window sequences by independent DFS: b = 2..7, all 2b ≤ n ≤ 3b−1 checked; all exist (`logs/bsym-b2-6.log`, `logs/bsym-b7.log`).
* Recursive construction: 228 pairs (b ≤ 12, b ≤ n ≤ 3b+5), 4,106 cyclic windows, every determinant ±1 over ℤ (`logs/bsym-recursive-B12.log`).
* Code enumeration over F_2, F_3, F_5 for b = 2..5, n = 2b..3b+2 (code size ≤ 300,000), 68 cases: |C| = q^{n−b} and minimum b-weight exactly 2b (`logs/bsym-codecheck.log`).

## IDs with no finite search run (reason recorded in results.json)

316834, 319591, 322353, 330337, 338400 and 345633 need engines not available here: a planar-graph generator, an FPL enumerator, reduced-Latin-square parity counts beyond the published range, Gröbner bases over ℤ, a matroid database, and oriented-matroid enumeration respectively. 320953 needs k ≥ 7 graphs. 343946 is the famous Barát–Gyárfás–Sárközy problem. The remaining IDs are known/resolved, analytic or asymptotic.
