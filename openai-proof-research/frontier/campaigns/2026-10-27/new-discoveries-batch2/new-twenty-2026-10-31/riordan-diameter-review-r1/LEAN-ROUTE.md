# 337352: Lean route plan (reviewer's design; Lean NOT run in this lane)

Reviewer lane: `riordan-diameter-review-r1` (Claude), 2026-11-04 UTC. This is a design for Sol to formalise. Nothing
here was compiled. Every numbered fact below was machine-checked on finite ranges with the reviewer's own code
(`scripts/s7_route.py`, `logs/s7_route.log`), and each has a pencil proof sketched here.

## 1. Endpoints

Notation: `bell A i j` is the binary Bell matrix built row by row from Jung's recurrence (9). `G A n` is the
Riordan graph on `Fin n`: for labels x > y, x ~ y iff `bell A (x-2) (y-1) = 1` (CJKM v2 eq. (4)). `Io A` means
`a 0 = 1 ∧ a 1 = 1 ∧ ∀ m, a (2m+1) = a (2m)` (CJKM v2 Thm 4.6 = Jung Lemma 2.1). `CG n = G 1 n`, where `1` is
the all-ones sequence. `diam` is `SimpleGraph.diam`, with a proved lemma that every `G A n` is connected.

* **E1 (primary; the intended reading R2, both clauses).**
  `(∀ k ≥ 1, diam (CG (2^k)) = k) ∧ ∀ A, Io A → (∀ k ≥ 1, diam (G A (2^k)) = k) → ∀ i, A.a i = 1`.
  Optional restatement: `∀ n, G A n = CG n`.
* **E0 (required companion, zero credit by itself; 372205 packaging).** The literal per-k reading (R1) is false:
  `diam (G (1,1,0,…) 4) = 2 ∧ IsEmpty (G (1,1,0,…) 4 ≃g CG 4)`. A k = 3 witness, 1111110 (CG_8 plus the edge
  {1, 8}), can be added. Both are `decide`-sized.
* **E3 (optional strengthening; HIGH cost).** For every k ≥ 4, `Io A → diam (G A (2^k)) = k → G A (2^k) ≃g CG (2^k)`.
  Together with E0 this gives the exact per-k picture: R1 holds iff k = 1 or k ≥ 4.

E1 does not need E3. If the first zero p of A lies at level K (2^(K−1) ≤ p ≤ 2^K − 2):

* K ≥ 4: Lemma C at level K gives `diam (G A (2^K)) ≤ K − 1 ≠ K`.
* K ≤ 3: p ∈ {2, 4, 6}, a finite check:
  * p ∈ {2, 4}: all 6 io graphs of order 8 have diameter 2 ≠ 3.
  * p = 6: all 16 io graphs of order 16 with prefix 11111100 have diameter 3 ≠ 4.

  The reviewer recomputed both (`logs/s7_route.log`).

There is no induction over k and no Jung Lemma 3.1 (P5). Nothing is used about general io graphs beyond the
recurrence itself.

## 2. Lagrange-free mathematics

1. **Diagonal.** `bell A i i = 1` (a_0 = 1). Hence x ~ x+1, so every `G A n` is connected (Hamiltonian path).
2. **Dependence.** `bell A i j` depends only on a_0, …, a_{i−j}. Proof by induction on i in recurrence (9).
3. **Perturbation.** If A and A′ agree below p, then for every j:
   `bell A (p+j) j − bell A′ (p+j) j = (j+1)(a_p − a′_p)` in ZMod 2.
   * Induction on i. In b_{i+1,j+1} = Σ_t a_t b_{i,j+t}, the t = 0 term carries (j+1)δ by induction and the
     t = p term carries δ · b_{i,i} = δ.
   * In b_{i+1,0} = Σ_t a_{t+1} b_{i,t}, only t = i contributes δ.
   * Checked on 254,589 entries.
4. **Catalan closed form.**
   * `bell 1 i j ≡ C(2i+1−j, i−j)` (mod 2).
   * Both sides satisfy b_{i+1,j+1} = b_{i,j} + b_{i+1,j+2}: the Catalan side from the recurrence, the binomial
     side from Pascal's rule with m = 2i+1−j and r = i−j.
   * The diagonal is 1 on both sides.
   * Column 0: b_{i+1,0} = b_{i+1,1} (Catalan) and C(2i+3, i+1) ≡ C(2i+2, i) (mod 2), because their difference
     C(2i+2, i+1) is even.
   * With Lucas (Kummer at p = 2): **x > y are adjacent in CG iff (x−1) AND (x−1−y) = 0** (bitwise).
   * Checked for rows 0 to 129.
5. **Catalan graph facts from the bit rule.** All checked for K ≤ 8.
   * (i) Vertex 2^s + 1 is universal in CG_{2^s+1}.
   * (ii) For 2^b < n ≤ 2^{b+1}, the window [2^b + 1, n] of CG_n is CG_{n−2^b} via the shift (labelled).
   * (iii) In CG_{2^K} the last vertex is pendant, adjacent only to 2^K − 1.
   * (iv) Edge-length bound: every edge {x > y} of CG_{2^K} has N+1−y ≤ 2(N+1−x).
6. **Catalan distances.**
   * diam(CG_n) ≤ ⌊log₂ n⌋, by strong induction on n using 5(i), 5(ii) and the universal-vertex argument of
     CJKM Thm 4.22, restricted to CG.
   * Hence d_{CG_{2^s}}(1, v) ≤ s − 1 for v < 2^s, via the prefix CG_{2^s−1}. This replaces Jung Thm 2.6.
   * diam(CG_{2^k}) ≥ k: by 5(iv), r = N+1−x at most doubles along each edge from N (r = 1), and vertex 1 has
     r = N. This replaces Jung Thm 2.4's reversal argument.
7. **Lemma B′ (replaces Lemmas A and B).** Let a_t = 1 for t < p and a_p = 0, with p even (first zero) and
   h ≤ p ≤ N − 2. Put j = N − 1 − p, which is odd.
   * Entry (N, j) has gap p.
   * By 3 with A′ = A but a′_p = 1, which agrees with CG up to p by 2, G-entry = CG-entry + j.
   * By 5(iii) the CG-entry is 0, since j ≤ h − 1 < N − 1. So N ~ j.
8. **Lemma C at level K ≥ 4.**
   * By 2, ⟨[1, h+1]⟩ and ⟨[h+1, N]⟩ of G equal those of CG_N, since all their gaps are ≤ h − 1 < p.
   * Then: d ≤ 2 inside V1 (5(i)); ≤ K − 1 inside V2 (5(ii), 6); ≤ 1 + (K − 2) across V1–V2 (6);
     d(x, N) ≤ 3 ≤ K − 1 through j (7).

Mathlib dependencies to confirm (Sol):

* Lucas' theorem for `Nat.choose` mod a prime (believed present as `Choose.lucas_theorem` or similar; otherwise
  prove the p = 2 bit rule directly from Pascal's rule by induction on the top bit);
* the `SimpleGraph.dist` / `Walk` / `diam` API, including mapping walks of an induced prefix or window into G.

## 3. Modules and honest cost (E1 + E0)

| Module | Content | Lines (est.) |
|---|---|---|
| M0 Defs | row-wise computable `bellRow`, `bell` equality lemma, `G`, `Io`, `CG`, connectivity | 150–250 |
| M1 Recurrence | diagonal, dependence, perturbation (facts 1–3) | 200–350 |
| M2 CG closed form | Pascal induction plus Lucas or bit rule (fact 4) | 200–450 |
| M3 CG bit facts | facts 5(i)–(iv) (`Nat.testBit` / `land` arithmetic) | 250–450 |
| M4 Distances | walk transport, diam(CG_n) ≤ ⌊log₂ n⌋, lower bound (fact 6) | 400–800 |
| M5 Lemmas B′, C | facts 7–8 | 200–350 |
| M6 Finite | 6 graphs of order 8 (≤ 2) and 16 of order 16 (≤ 3). Upper bounds only, so a bitmask ball-closure checker needs soundness in one direction only (y ∈ ball_t(x) gives dist ≤ t). Kernel `decide` on Nat bitwise operations (kernel-accelerated); no `native_decide`. | 150–300 |
| M7 Endpoints | E1, E0 (`decide`), statement-fidelity comments | 80–150 |

Total ≈ 1,600–3,100 lines. **MEDIUM.** The main risk is M4 (distance plumbing).

**E3 adds HIGH cost.** Per-k needs Jung Lemma 3.1 (P5) for general io sequences, and therefore:

* general P1 (vertex 2^s + 1 universal for every io A). Route: division-free Lagrange–Bürmann
  [z^n] f^j = [w^{n−j}] A^{n−1}(A − wA′), proved over ℤ (Riordan-array inverse plus torsion-freeness) and mapped to
  ZMod 2, with the io identity A′/A = 1/(1+w). The alternative is CJKM's edge-count Lemmas 4.9–4.10;
* general P2 (Frobenius shift b_{i+2^s, j+2^s} = b_{i,j} for gaps < 2^s), which needs the power-series bridge
  b_{i,j} = [z^i] g f^j.

Add ≈ 1,500–3,000 lines. Recommend E3 only if root asks for the per-k statement.

## 4. Review of the lane's UNCOMPILED draft `lean/Riordan337352.lean` (sha256 2b7aa767…)

Right:

* `bell` matches Jung (9) (lines 24–30).
* `riordanGraph` matches eq. (4) on `Fin n` (lines 34–37).
* `IoBell` matches Thm 4.6 (line 48).
* The logic of `catalan_unique` is sound given its lemmas (lines 94–114).
* The `lemmaA` statement is correct as stated (lines 66–70).
* `conjecture2_family` has the right shape for E1 (lines 123–130).

Wrong or weak:

1. `bell` is a naive non-memoised recursion: exponential evaluation, unusable for the kernel `decide` that
   `base_k4` needs (lines 58–62). Add a row-list implementation plus an equality lemma.
2. `diam'` is `SimpleGraph.diam`, which is 0 for disconnected graphs. A connectivity lemma is needed to match CJKM
   Def. 4.21, and `lemmaC`'s `≤ K − 1` must be proved through distances, not read off `diam`.
3. No endpoint states the isomorphism form ("G ≇ CG"), and nothing formalises the literal negation E0 at k = 2.
4. The plan routes E1 through per-k induction (`diam_step` = P4 + P5) and so needs general P1, P2 and P4 as well as
   Lagrange inversion (`lemmaA`). All of that is avoidable for E1 (§1–2).
5. Jung Thm 2.4 (`diam_catalan`, line 117) is left as `sorry` with no route. Fact 6 gives a short elementary route.
6. Several obligations are left as `sorry` in the induction glue (`hpre` and the arithmetic, lines 101–102 and 130).
   They are routine.
7. The doc comment calls the definitions "source-literal". The io class is defined by the Thm 4.6 A-sequence form,
   not by Def. 4.1's "≅". That choice is correct (see REVIEW §A.3), but it should be stated and justified in the
   file.
