# Candidate 353800: Naslund's function-field Sárközy tightness conjecture is false

Lane expanded-corpus-r160 (Claude Opus 5.5), 2026-11-04. **Status: candidate only. Not self-accepted.**
The Lean source is an UNCOMPILED draft, because this lane may not run Lean.

## 1. Exact statement and provenance

- **MathDB record:** 353800, "Tightness of the function-field Sárközy bound for square differences".
  - Corpus file: `lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0008.jsonl`, line 3105.
  - Raw line sha256: `00a7798f65368f2bdf0c4bef9eba3d37e894abd21ec7ce7c1875c985f3cf8d89`.
  - Chunk sha256: `b99fabbee55f0fd30c63a5583173f4779cc8351f3c04b76d9594d038bf9c8a47`.
  - Statement sha256: `4fee4f099128bd5d2f1056d4c17cf633f0178294871d7e4cbc2a428bd13b2f3d`.
  - MathDB metadata: status open, solution_count 0, first stated 2022.
  - Raw line copied to `sources/353800.raw.jsonl`.
- **Source:** E. Naslund, "Paley graphs and Sárközy's theorem in function fields", arXiv:2203.01293.
  - Current version: v3, 22 May 2022 03:21 UTC (the abstract page lists v1–v3).
  - Published in Q. J. Math. 2022, haac035, doi:10.1093/qmath/haac035.
  - v3 thanks "the anonymous referee", so it is the post-refereeing text. The journal page itself was not opened (OUP was not tried).
  - Receipts: abs sha256 `f5af3738109e4e2a637bdc4301bdb86703bbe454bbf9cd7f156579471ece3496`; e-print sha256 `0eecc56163fe99da45297437b1bf280a07ee7d88adfc561b46e4ccfb361c30c3`.
  - The LaTeX is in `sources/eprint/353800-x/main.tex`. The target is Conjecture 13 (single global theorem counter) in Section 3, subsection "Limits of the Method", LaTeX lines 615–622.
- **Source text, verbatim:** "Let k≥2, and suppose that gcd(k,q−1)>1. For n≡0 (2k), any set A⊂P_{q,n} that does not contain a k-th power difference has size at most |A| ≤ q^{n(1−1/k²)}. In particular, for k=2 and q odd, we conjecture that Theorem 1 is tight." Theorem 1 constructs |A| = q^{n(1−1/2k)}, which for k = 2 is q^{3n/4}.
  - The source's definition of a k-th power difference: distinct u, v ∈ A with u − v = b(T)^k for some b ∈ F_q[T].
  - P_{q,n} is the set of polynomials of degree < n.
  - The MathDB text matches the source.

The exact negation that we prove: **there exist q, k, n with k ≥ 2, gcd(k, q−1) > 1 and 2k | n, and a set A ⊆ P_{q,n} with no k-th power difference, such that |A| > q^{n(1−1/k²)}.** The witness is q = 5, k = 2, n = 4, |A| = 160 > 125.

## 2. The counterexample (q = 5, k = 2, n = 4)

Let X ⊂ F_5^3 be the following 32 triples (c0, c1, c2). These are the 20 solutions of 4·c0·c2 − c1² = 2 (a nonsquare in F_5), together with the 12 points t·(a², 2ab, b²) for t ∈ {1, 4} and [a:b] ∈ PG(1,5). This is the q = 5 case of Theorem U in §3. It is also the set used in the Lean draft.

```
(0,0,1) (0,0,4) (1,0,0) (1,0,3) (1,1,2) (1,1,4) (1,2,1) (1,2,4) (1,3,1) (1,3,4) (1,4,2) (1,4,4)
(2,0,4) (2,1,1) (2,2,2) (2,3,2) (2,4,1) (3,0,1) (3,1,4) (3,2,3) (3,3,3) (3,4,4) (4,0,0) (4,0,2)
(4,1,1) (4,1,3) (4,2,1) (4,2,4) (4,3,1) (4,3,4) (4,4,1) (4,4,3)
```

A different 32-point set found earlier by local search is also valid; it is stored in `work/sarkozy/q5n4.json` and was verified the same way.

Then let A = { c0 + c1 T + c2 T² + c3 T³ : (c0,c1,c2) ∈ X, c3 ∈ F_5 }, a set of 160 distinct polynomials in P_{5,4}.

**Lemma 1.** Suppose d ∈ F_q[T] has deg d ≤ 3 and d = b². Then b = β0 + β1 T, and the coefficient vector of d is (β0², 2β0β1, β1², 0).

*Proof.* Over a field, if b ≠ 0 then deg b² = 2 deg b. So 2 deg b ≤ 3 forces deg b ≤ 1. Then expand. ∎

**Proposition 2.** A has no square difference.

*Proof.*
1. Suppose u ≠ v in A and u − v = b². Write u ↔ (x, s) and v ↔ (x', s'), where x, x' ∈ X and s, s' are the T³ coefficients.
2. By Lemma 1, s = s' and x − x' = (β0², 2β0β1, β1²).
3. If β0 = β1 = 0, then x = x' and s = s', so u = v, a contradiction.
4. Otherwise x − x' is a nonzero element of S = {(β0², 2β0β1, β1²) : (β0, β1) ≠ 0}.
5. The finite check (X − X) ∩ S = ∅ excludes this. It covers 32² ordered pairs against 24 pairs (β0, β1), so 12 distinct vectors after the identification b ~ −b.
6. The check was done by two independent scripts:
   - `scripts/sarkozy_verify.py` works on the full 160-element set. For every ordered pair it tests whether u − v equals b² for every nonzero b ∈ F_5[T] of degree ≤ 3, computing b² by direct polynomial multiplication.
   - `scripts/sarkozy_verify_slice.py` works on the slice.
   - Both report 0 violations for both 32-point sets (`work/sarkozy/q5n4-structured.json` and `work/sarkozy/q5n4.json`). ∎

Since k = 2 ≥ 2, gcd(2, 5−1) = 2 > 1, 4 ≡ 0 (mod 4), and |A| = 160 > 125 = 5^{4(1−1/4)}, the conjecture fails. ∎

Interpretation: the squares of degree < 4 are the vectors b b^T of symmetric 2×2 matrices [[x, y/2], [y/2, z]] ≅ (x, y, z). So X is an independent set in the Cayley graph Γ_q on F_q³ whose connection set S ∪ −S is the "square-type" half of the isotropic cone y² = 4xz.

## 3. Uniform construction for every prime power q ≡ 1 (mod 4)

Write D(x,y,z) = 4xz − y². Its polar form is B(v,w) = D(v+w) − D(v) − D(w) = 4(v_x w_z + v_z w_x) − 2 v_y w_y. Let S = {(a², 2ab, b²) : (a,b) ≠ 0}. For q ≡ 1 (mod 4), −1 is a square, so −S = S. Every nonzero isotropic vector (D = 0) has the form λ(a², 2ab, b²) with λ ≠ 0. It lies in S iff λ is a square.

**Theorem U.** Let q ≡ 1 (mod 4) be a prime power and c ∈ F_q a nonsquare. Let I be a set of nonzero squares such that no two distinct elements differ by a square. For each point [a:b] of PG(1,q), fix the representative (a², 2ab, b²). Define

X_q = D⁻¹(c) ∪ { t·(a², 2ab, b²) : [a:b] ∈ PG(1,q), t ∈ I }.

Then X_q has no difference in S, and |X_q| = q² − q + (q+1)|I|. One can always take |I| = 2 when q ≥ 5, which gives |X_q| = q² + q + 2 > q².

*Proof.*
1. **The level set L = D⁻¹(c) is independent.**
   - Suppose v, v + s ∈ L with s ∈ S, so s = (a², 2ab, b²) with (a,b) ≠ 0.
   - Since D(s) = 0, we get D(v + s) = D(v) + B(v,s), hence B(v,s) = 0.
   - But B(v,s) = 4(z a² − y ab + x b²).
   - The binary form z a² − y ab + x b² has discriminant y² − 4xz = −c. Since −1 is a square, −c is a nonsquare.
   - A binary form whose discriminant is a nonsquare has no nonzero zero. This is a contradiction.
2. **The size of L.** For each y, the equation 4xz = c + y² has c + y² ≠ 0, because −c is not a square. So it has q − 1 solutions (x,z), and |L| = q(q−1).
3. **No added point is adjacent to L.**
   - Let v = t(α², 2αβ, β²) with t a square, and let s = (a², 2ab, b²).
   - Then D(v + s) = B(v,s) = 4t(αb − βa)². This is a square or 0, so it never equals c.
   - Hence v + s ∉ L. Since −S = S, this covers both directions of any difference w − v with w ∈ L.
4. **The added points are pairwise non-adjacent.**
   - For u = λ(a², 2ab, b²) and v = μ(c', 2c'd', d'²), we have D(u − v) = −B(u,v) = −4λμ(ad' − bc')².
   - So u − v is isotropic only if [a:b] = [c':d'], that is, only if u and v lie on the same isotropic line.
   - On the line through (a², 2ab, b²), the difference (λ − μ)(a², 2ab, b²) lies in S iff λ − μ is a nonzero square.
   - The choice of I excludes this.
5. **|I| = 2 is achievable for q ≥ 5.**
   - Suppose every difference of two distinct nonzero squares were a square.
   - Then the set of squares together with 0 would be closed under subtraction, so it would be an additive subgroup of order (q+1)/2.
   - But (q+1)/2 > 1 and (q+1)/2 is coprime to p, so it cannot be the order of an additive subgroup. This is a contradiction.
   - Hence two squares t1, t2 with t1 − t2 a nonsquare exist, and I = {t1, t2} works. ∎

**Corollary U.** For every prime power q ≡ 1 (mod 4) and every n = 4m:
- Combine Theorem U with Theorem 3 (taking r = 1).
- This gives a square-difference-free A ⊆ P_{q,n} with |A| = q^{3m−2}(q² + q + 2) = q^{3n/4}(1 + 1/q + 2/q²) > q^{3n/4}.
- So Naslund's conjecture fails for **every** q ≡ 1 (mod 4) and **every** admissible n (k = 2).
- Machine check of Theorem U (`scripts/sarkozy_uniform.py`, direct test against all squares of b0 + b1T): q = 5, 13, 17, 29, 37, 41 give |X_q| = 32, 198, 326, 902, 1446, 1808. These match the formula q² − q + (q+1)|I| with greedy I of sizes 2, 3, 3, 3, 3, 4, and there were 0 violations.
- Local search does better at some q (209 at q = 13), so Theorem U is not claimed to be optimal.

## 4. The failure is not tied to n = 4: every n ≡ 0 (mod 4)

**Theorem 3.** Let q be odd, r ≥ 1, and X ⊆ F_q^{4r−1} a set such that no difference of two distinct elements is the coefficient vector of b², where b ≠ 0 and deg b ≤ 2r − 1. Then for every m ≥ r there is A ⊆ P_{q,4m} with no square difference and |A| = q^{3(m−r)+1} |X|.

In particular, if q|X| > q^{3r}, then |A| > q^{3m} = q^{3n/4} for every n = 4m ≥ 4r.

*Proof.*
1. **Setup.** Write n = 4m and μ = 2m − 1 = (n−2)/2. Define the window W = [μ − (2r−1), μ + (2r−1)] = [2m−2r, 2m+2r−2], which has 4r − 1 positions.
2. **Fixing U.** Fix a nonsquare β and let U = {(t, βt) : t ∈ F_q}. For distinct elements of U, the two coordinate differences are (t, βt) with t ≠ 0, so they are not both squares (0 counts as a square). This is Naslund's Proposition 7.
3. **Defining A.** A consists of all coefficient vectors c ∈ F_q^n such that:
   - (c_i)_{i∈W} ∈ X;
   - (c_i, c_{n−2−i}) ∈ U for every even i ≤ 2m−2r−2;
   - every odd position outside W is free.

   The partners n−2−i are exactly the even positions in [2m+2r, 4m−2]. Counting the outside positions gives 2(m−r)+1 free odd positions and m−r pairs. Hence |A| = q^{2(m−r)+1} · q^{m−r} · |X|.
4. **Extreme coefficients.** Suppose d = u − v = b² ≠ 0 for u, v ∈ A. Let 2l and 2h be the lowest and highest indices of nonzero coefficients of d; both are even. Then d_{2l} = (low coefficient of b)² and d_{2h} = (top coefficient of b)².
5. **Case A: supp d ⊆ W.** Then u and v agree outside W, and l ≥ m − r. Write b = T^{m−r} b'. Then d = T^{2(m−r)} b'², and deg b' ≤ 2r − 1 because 2h ≤ 2m + 2r − 2. So the W-part of d is the coefficient vector of b'². That makes it a nonzero square-vector difference of two elements of X, which contradicts the choice of X.
6. **Case B: setting up.** Otherwise the extreme index j ∈ {2l, 2h} farther from μ lies outside W. By symmetry take j = 2h > μ with 2h − μ ≥ μ − 2l.
   - Then j ≥ 2m + 2r is a paired even position, with partner j' = n − 2 − j.
   - From 2l ≥ 2μ − 2h = j', all coefficients of d below j' vanish.
   - Hence d_{j'} is either the lowest coefficient (a square) or 0.
7. **Case B: contradiction.** So (d_j, d_{j'}) has both coordinates squares (0 included), and d_j ≠ 0. But (d_j, d_{j'}) is the difference of two distinct elements of U, which is impossible. The case j = 2l is symmetric. ∎

Theorem 3 is Naslund's own extreme-coefficient argument (his Theorem 10), with one change: we reserve a middle window, which his proof does not do.

**Consequences.** All witness sets were verified as in §2, and the files are in `work/sarkozy/`.

| q | r | slice \|X\| | \|A\| at n = 4r | bound q^{3r} | violation ratio for every n = 4m ≥ 4r |
|---|---|---|---|---|---|
| 5 | 1 | 32 | 160 | 125 | 1.280 |
| 9 (GF(9)) | 1 | 99 | 891 | 729 | 1.222 |
| 13 | 1 | 209 | 2717 | 2197 | 1.237 |
| 17 | 1 | 311 | 5287 | 4913 | 1.076 |
| 3 | 2 | 297 | 891 | 729 | 1.222 (n ≥ 8) |

Two machine checks of the Theorem 3 construction were run:
- **q = 5, n = 8, r = 1:** |A| = 32·5·5³ = 20000 > 5⁶ = 15625. This was verified completely (`scripts/window_full_q5n8.py`). Because A − A = (X − X) × U × F_5³, it suffices to test all 70624 distinct nonzero differences against the 312 nonzero squares of degree < 8; there were 0 violations. Separately, 200000 random pairs were checked by brute-force square testing (`scripts/window_check.py`), again with 0 violations.
- **q = 3, n = 8, r = 1, with the tight 9-point plane slice:** a full brute-force check of all pairs of the resulting 729 = 3⁶ polynomials found 0 violations, as expected. This confirms that the construction logic is sound.

The source singles out k = 2 and q odd, and asks whether Theorem 1 is tight there. The table rows are local-search slices that improve on Theorem U for those particular q. By Corollary U, every q ≡ 1 (mod 4) already fails at every n ≡ 0 (mod 4). For q = 3 (≡ 3 mod 4), the computational r = 2 slice shows failure at every n ≡ 0 (mod 4) with n ≥ 8. For q ≡ 3 (mod 4) in general and n ≥ 8, there is no uniform proof yet; only q = 3 was checked.

**Boundary.** For q ≡ 3 (mod 4) and n = 4, the conjecture is *true*. In that case S ∪ −S is the whole isotropic cone. The eigenvalues of Γ_q are q·k − q − 1 for k ∈ {0, 1, 2}, so the minimum eigenvalue is −q−1. The Hoffman bound is then exactly q² (`scripts/hoffman.py`: q = 3 and q = 7 give 9 and 49). So for n = 4 the violation genuinely needs −1 to be a square. For q = 3, the first violation is at n = 8.

**Not refuted.** The exponent 3/4 is untouched. Every violation found is a constant factor, so a weaker "exponent" reading of the conjecture (max |A| = q^{3n/4 + o(n)}) remains open. The k ≥ 3 cases searched did not violate the bound:
- k = 3, q = 7, n = 6: best slice 637 vs a threshold of 656.1.
- k = 4, q = 5, n = 8: best 1100 vs 1397.5.
- k = 3, q = 4, n = 6: exact maximum 16·80 = 1280 < 1625.5. The slice graph is 16 copies of the Clebsch graph, each with α = 5; verified by exact search.

## 5. Zero-credit screens (brief items 1–3 and lessons)

1. **The source's own theorems do not imply the result.**
   - The source proves r_{2,2}(F_q) = q, which concerns its pair method only.
   - It writes "one must use a different method to improve the lower bound beyond q^{n(1−1/k²)}", and conjectures exactness.
   - Our improvement comes from the middle-window cone structure, which the source does not use.
   - Theorem 3 reuses the source's pair argument, but that is not needed for the literal refutation: §2 alone suffices.
2. **Cited constructions.**
   - Ruzsa 1984 concerns the integers.
   - Green 2017 (arXiv:1605.07263; read) gives only upper bounds. For lower bounds it cites C. Link's unpublished 2008 manuscript. Green describes Link's examples as A ⊂ P_{5,2n} with |A| = 5^{3n/2}, which equals Naslund's bound and does not exceed it. The manuscript itself was not read, since it is unpublished.
   - Lê–Liu, Acta Arith. 161 (2013), is cited by Green as prior upper-bound work. It is not on arXiv and was **not read**; this is a residual risk.
3. **Generic failure of a rule.** None identified. This is not a convention or boundary effect: it holds for every admissible n at q = 5.
4. **Later literature.** arXiv full-text and title searches were run on 2026-11-04; receipts are in `outputs/fetch-receipts.json`.
   - Li–Sauermann (2212.12754), 2609.12499, 2510.27573 and 2510.27581 were read by grep of their LaTeX.
   - None mentions Naslund's conjecture or a k = 2 lower bound above q^{3n/4}.
5. **Registries.**
   - OpenAI/math HEAD is 4eaee87548250b2682affda7d05d947c05554bae (unchanged, live check). Its only related item is the integer preprint "A power saving for square-difference-free sets" (2026-09-24). Its introduction and bibliography contain no function-field or Naslund material.
   - Omega HEAD is now **b52262a023c4db9bb30a128ebfd80ea4ef4c1a53** (2026-11-04T12:05:53Z, newer than root's 86172888). I fetched the complete D5 tree (13929 entries) and Problems tree (1720 entries), both untruncated. Neither has any Sárközy, Naslund or square-difference path. This was a path screen only.
   - MathDB sibling record: 353799 is a different conjecture from the same source.
6. **Classical-object risk.** Γ_q is one class of the association scheme of symmetric bilinear forms on F_q² (rank 1, square type). Independence numbers of such class graphs might appear in coding-theory work on symmetric rank-metric codes (e.g., K.-U. Schmidt). No such source was located or read, so this is a residual prior-art risk for the q-family. It is not a risk for the literal refutation, which is an explicit verified set.

## 6. Significance assessment (for root; not a self-acceptance)

**For:**
- This is an explicit, small, kernel-checkable refutation (q = 5, n = 4, |A| = 160 > 125) of a conjecture stated in a refereed journal paper.
- It is also a short **uniform** algebraic disproof: Theorem U plus Theorem 3.
  - Naslund's k = 2 conjecture fails for every prime power q ≡ 1 (mod 4) and every admissible n.
  - It also fails at q = 3 for n ≥ 8 (computational).
- It sits exactly in the regime the source singles out ("for k = 2 and q odd, we conjecture that Theorem 1 is tight").
- There is a clean complementary positive statement: for q ≡ 3 (mod 4) and n = 4 the bound is exact (Hoffman).
- The mechanism is new relative to the source. A level set of the discriminant 4xz − y² is independent because its tangent planes are anisotropic. The source's method only uses extreme coefficient pairs, and the source says explicitly that a different method would be needed.

**Against:**
- The gain is a factor 1 + 1/q + 2/q² (at most 1.28 found), so the exponent 3/4 is untouched. A reviewer may argue that the conjecture was intended as an exponent statement. The printed inequality is exact, though, and "tight" refers to the specific Theorem 1.
- Residual prior-art risks are listed in §5: Lê–Liu 2013 unread, Link 2008 manuscript unread, and the symmetric-bilinear-forms literature not searched.

## 7. Lean plan (UNCOMPILED draft `lean/MathDB353800.lean`)

**Endpoint.** `MathDB353800.not_conjecture : ¬ Conjecture`. `Conjecture` is the literal statement:
- it quantifies over every `F : Type` with `[Field F] [Fintype F] [DecidableEq F]` and every k, n with `2 ≤ k`, `1 < Nat.gcd k (Fintype.card F - 1)`, `n % (2*k) = 0`;
- it quantifies over every `A : Finset F[X]` with `∀ f ∈ A, f.degree < n` and `∀ u ∈ A, ∀ v ∈ A, u ≠ v → ∀ b, u - v ≠ b ^ k`;
- it concludes `(A.card : ℝ) ≤ (Fintype.card F : ℝ) ^ ((n:ℝ) * (1 - 1/(k:ℝ)^2))`.

**Statement correspondence.**
- "q a prime power" is automatic, because the card of a finite field is a prime power.
- "P_{q,n}" is `degree < n`, and it includes 0.
- "no nonzero k-th power difference" is `u ≠ v → u − v ≠ b^k`.

**Proof structure.**
- `slice` is the 32 triples. `A` is the image of `slice.toFinset ×ˢ univ` under `toPoly`.
- Card 160 comes from `toPoly_injective` (coefficients 0–3) plus `slice_nodup` by `decide`.
- The degree bound comes from `compute_degree`.
- Key step: `natDegree_sub_le` and `Polynomial.natDegree_pow` (domain version, `Mathlib/Algebra/Polynomial/Degree/Domain.lean:52`) give `b.natDegree ≤ 1`. Then `eq_X_add_C_of_natDegree_le_one` gives `b = C b1 * X + C b0`. Comparing coefficients 0–2 reduces to `slice_check`.
- `slice_check` is a kernel `decide` over 32·32·25 cases. If plain `decide` is slow, use `decide +kernel`; never `native_decide`.
- The real inequality: rewrite 4·(1 − 1/2²) = 3, then `Real.rpow_natCast`, then `norm_num` (160 ≤ 125 is false).
- Mathlib names were checked against the pinned cache (`.../2026-10-14/formal/.lake/packages/mathlib`). They are `Polynomial.natDegree_pow`, `eq_X_add_C_of_natDegree_le_one` (Degree/SmallDegree.lean:41) and `Real.rpow_natCast` (Pow/Real.lean:62). Expected axioms: propext, Classical.choice, Quot.sound.

**Optional second endpoint.** Theorem 3 for all n ≡ 0 (mod 4) with q = 5 is not needed for the literal negation.

## 8. Reproduction

All runs used `scripts/cap.sh` (CPU 120 s, wall 140 s, RSS cap) and `python3 -I`, one process at a time. Logs and outputs are in `outputs/` and `work/sarkozy/`.

1. `scripts/sarkozy_ils.py p k n seconds seed out.json` finds the slices.
2. `scripts/sarkozy_find.py` writes the q = 5 file.
3. `scripts/sarkozy_verify.py work/sarkozy/q5n4.json` is the full-polynomial verifier. It reports `|A| 160 bound 125.0 violations 0 COUNTEREXAMPLE`.
4. `scripts/sarkozy_verify_slice.py` checks each slice file.
5. `scripts/sarkozy_gf9.py` handles q = 9.
6. `scripts/hoffman.py` computes the Hoffman bounds.
7. `scripts/sarkozy_exact.py 5 31` re-found 32 but did not finish proving optimality within the CPU cap, so the exact maximum for q = 5 is **unknown**. It lies in [32, 42], where 42 is the Hoffman bound.
