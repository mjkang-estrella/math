# Romik's sequence modulo powers of primes p ≡ 3 (mod 4): the odd clause of Krattenthaler–Müller's Conjecture 44 and an exact description of the even-clause exceptions

*Manuscript accompanying a Lean 4 / Mathlib formalization (MathDB 358162). Drafted 2026-11-20.
The mathematical route was first proposed in a GPT-6.1 proof write-up (pool 060). The proof given here is the one that was formalized; at the residue step it differs from that write-up (see Remark 4.6). The Lean development is in `LEAN-SOURCE-APPENDIX.md`.*

## Abstract

Let v(n) be Romik's sequence, defined by recurrence (2.6) of Krattenthaler and Müller [KM]. Let p be a prime with p ≡ 3 (mod 4). We prove the first part of their Conjecture 44 exactly as printed: if e is odd, then p^e | v(n) for all n ≥ (ep+2)(p+1)/4. For even e we determine every n ≥ ⌈ep²/4⌉ with p^e ∤ v(n). Such an n exists only if e = (p+1)(2j+1) with 0 ≤ j < (p−1)/2. In that case 4n = ep² + (p+1) + 4r, where r ranges over an explicit set E_p ⊆ [0, (p+1)/4). The set E_p is the support of a power of a small polynomial over F_p. At every exception p^(e−1) still divides v(n). The classification reproduces the four exceptional pairs (p,e) = (7,8), (7,24), (7,40), (11,36) listed in [KM], with exactly their corrected lower bounds 102, 298, 494 and 1095. Their list is not complete: (p,e) = (3,4) at n = 10 and (11,12) at n = 366, 367, 368 are exceptions too. All results are machine-checked in Lean 4 with Mathlib. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## 1. The conjecture and the source definitions

**Source definitions** ([KM], arXiv:2304.11471v4, §2, quoted verbatim):

> For convenience, we shall later frequently use the short notations
> Π₁(N) := ∏_{j=1}^{N} (4j−1)²  and  Π₃(N) := ∏_{j=1}^{N} (4j−3)².   (2.3)
>
> The sequence (v(n))_{n≥0} is also defined via an exponential generating function, namely by (cf. [10, Eq. (10) and Lemma 6])
> Σ_{n≥0} v(n)/(2^n (2n)!) t^{2n} = ₂F₁[1/4, 1/4; 1/2; 4t²]^{1/2} = ( Σ_{j≥0} ∏_{ℓ=1}^{j}(4ℓ−3)²/(2j)! · t^{2j} )^{1/2}.   (2.5)
>
> Again, it is not difficult to see (cf. [10, Eq. (20)]) that an equivalent definition of v(n) is by the recurrence
> v(n) = 2^{n−1} Π₃(n) − ½ Σ_{m=1}^{n−1} binom(2n,2m) v(m) v(n−m),  with v(0) = 1.   (2.6)
>
> The first few values turn out to be 1, 1, 47, 7395, 2453425, 1399055625, 1221037941375, 1513229875486875, 2526879997358510625, 5469272714829657020625, 14892997153152592003359375, …

**Conjecture 44** ([KM], v4, §13, verbatim):

> (1) If p ≡ 3 (mod 4) and e is odd, we have v(n) ≡ 0 (mod p^e) for n ≥ (ep+2)(p+1)/4.
>
> (2) If p ≡ 3 (mod 4) and e is even, we have v(n) ≡ 0 (mod p^e) for n ≥ ⌈ep²/4⌉, "with very few exceptions." Based on data for v(n) with n ≤ 1500, the only exceptions that we found were
> • p = 7 and e = 8, where the correct lower bound is 102 instead of ⌈8·7²/4⌉ = 98;
> • p = 7 and e = 24, where the correct lower bound is 298 instead of ⌈24·7²/4⌉ = 294;
> • p = 7 and e = 40, where the correct lower bound is 494 instead of ⌈40·7²/4⌉ = 490;
> • p = 11 and e = 36, where the correct lower bound is 1095 instead of ⌈36·11²/4⌉ = 1089.

**The Lean counterparts** (module `RomikDefs`). The definitions follow the source literally. v is defined by (2.6) over ℚ, so the factor ½ is the rational number ½. Integrality is then proved rather than assumed.

```lean
def Pi3 (n : ℕ) : ℕ := ∏ j ∈ Finset.range n, (4 * (j + 1) - 3) ^ 2          -- (2.3)
def romikQ : ℕ → ℚ  -- (2.6) over ℚ; restated literally by romikQ_zero / romikQ_rec:
theorem romikQ_zero : romikQ 0 = 1
theorem romikQ_rec (n : ℕ) (hn : 1 ≤ n) :
    romikQ n = 2 ^ (n - 1) * (Pi3 n : ℚ) -
      (1 / 2) * ∑ m ∈ Finset.Ico 1 n,
        ((Nat.choose (2 * n) (2 * m) : ℕ) : ℚ) * romikQ m * romikQ (n - m)
theorem romikQ_int : ∀ n, ∃ z : ℤ, romikQ n = z                               -- integrality
noncomputable def romikV (n : ℕ) : ℤ := Classical.choose (romikQ_int n)       -- v(n)
theorem romikV_printed_values :
    (List.range 11).map romikV = [1, 1, 47, 7395, 2453425, 1399055625, 1221037941375,
      1513229875486875, 2526879997358510625, 5469272714829657020625,
      14892997153152592003359375]
noncomputable def smallW (p : ℕ) : Polynomial (ZMod p) :=
  ∑ r ∈ Finset.range ((p + 1) / 4),
    Polynomial.C (((∏ i ∈ Finset.range r, (4 * (i + 1) - 1) ^ 2 : ℕ) : ZMod p) *
      (((2 * r + 1).factorial : ℕ) : ZMod p)⁻¹) * Polynomial.X ^ r
```

(`romikQ` is written with the sum indexed by `Fin (n−1)` so that the recursion is structural. `romikQ_rec` is exactly (2.6).) The denominators in `smallW` are units: 2r+1 < p for r < (p+1)/4 (`smallW_denominator_unit`).

## 2. Results

Throughout, p is a prime with p ≡ 3 (mod 4). Write

  a = (p+1)/2,  h = (p−1)/2,  d = (p+1)/4,

and in F_p[T] let

  W_p(T) = Σ_{r<d} ( ∏_{i=1}^{r} (4i−1)² / (2r+1)! ) T^r,   E_p = { r < d : [T^r] W_p(T)^a ≠ 0 }.

**Theorem A (Conjecture 44(1)).** If e is odd and n ≥ (ep+2)(p+1)/4, then p^e | v(n).

**Theorem B (Conjecture 44(2), exact form).** Let e ≥ 2 be even and n ≥ ⌈ep²/4⌉. Then p^(e−1) | v(n). Moreover p^e ∤ v(n) if and only if there are j and r with

  0 ≤ j < h,  e = (p+1)(2j+1),  r ∈ E_p,  4n = ep² + (p+1) + 4r.

So for each p there are exactly h·|E_p| ≤ (p²−1)/8 exceptional pairs (e,n). All of them have e ≤ (p+1)(p−2), and each falls short by a single factor of p. Since [T⁰]W_p(T)^a = 1, we always have 0 ∈ E_p. So every p ≡ 3 (mod 4) has at least h = (p−1)/2 exceptional pairs; for example e = p+1 and 4n = (p+1)(p²+1). Each prime has finitely many exceptions, but taken over all primes there are infinitely many.

In Lean (module `RomikMain`):

```lean
theorem romik_conj44_odd {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he : Odd e) (hn : (e * p + 2) * (p + 1) ≤ 4 * n) : (p : ℤ) ^ e ∣ romikV n

theorem romik_conj44_even_lower {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he : Even e) (hn : e * p ^ 2 ≤ 4 * n) : (p : ℤ) ^ (e - 1) ∣ romikV n

theorem romik_conj44_even_exact {p e n : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he0 : 0 < e) (he : Even e) (hn : e * p ^ 2 ≤ 4 * n) :
    ¬ (p : ℤ) ^ e ∣ romikV n ↔ ∃ j r, 2 * j < p - 1 ∧ e = (p + 1) * (2 * j + 1) ∧ 4 * r < p + 1 ∧
        ((smallW p) ^ ((p + 1) / 2)).coeff r ≠ 0 ∧ 4 * n = e * p ^ 2 + (p + 1) + 4 * r
```

The hypothesis `(e*p+2)*(p+1) ≤ 4*n` is n ≥ (ep+2)(p+1)/4 with denominators cleared, and `e*p^2 ≤ 4*n` is n ≥ ⌈ep²/4⌉.

**The exceptions for small p** (the theorem evaluated with `scripts/exceptions_table.py`; the Lean development checks the case (7,8) itself):

| p | E_p | exceptional (e, n) |
|---|-----|--------------------|
| 3 | {0} | (4, 10) |
| 7 | {0,1} | (8, 100–101), (24, 296–297), (40, 492–493) |
| 11 | {0,1,2} | (12, 366–368), (36, 1092–1094), (60, …), (84, …), (108, …) |
| 19 | {0,1,2,4} | (20, 1810, 1811, 1812, 1814), … |
| 23 | {0,…,5} | (24, 3180–3185), … |

For p = 7 the exceptions give exactly the corrected bounds 102, 298 and 494 of [KM]. For (11,36) they give 1095. The pairs (3,4) and (11,12) are exceptions that [KM] did not list. The case (11,12) lies inside their stated search range n ≤ 1500. The case (3,4) can be read off the value v(10) printed in [KM] after (2.6): that value is divisible by 3³ but not by 3⁴. Two independent computations reproduce the table. The first runs (2.6) modulo p^E for p = 3, 7, 11, 19, 23 and n ≤ 6000. The second runs exact arithmetic through the generating function (2.5) for n ≤ 372. In both, the set of even-clause failures equals the predicted set, and no odd-clause failure occurs. These side findings are not the content of the result. Because of the qualifier "with very few exceptions", they do not refute anything. The content is Theorem A together with the exact description in Theorem B.

## 3. Formal sanity guards

All of the following are proved in Lean.
- `romikV_printed_values`: the eleven values printed after (2.6).
- `romikV_10_not_dvd`: ¬ 3⁴ | v(10), by direct computation.
- `romikV_seven_eight`: 7⁸ | v(102) ∧ ¬ 7⁸ | v(101). This is the source's own data point, the corrected bound 102 for (p,e) = (7,8), obtained from Theorem B.
- Vacuity: `romik_odd_hyp_satisfiable` (p = 3, e = 1, n = 5 satisfy the odd hypotheses). `romik_even_iff_both_sides`: at p = 7, e = 8, the right-hand side of the iff is true for n = 101 and false for n = 102.

## 4. Proof

### 4.1 The square-root coefficients (bridge to (2.5))

Put c_n = v(n)/(2^n (2n)!) and f_j = Π₃(j)/(2j)!. Since binom(2n,2m)(2m)!(2n−2m)! = (2n)!, dividing (2.6) by 2^n(2n)! gives, for n ≥ 1,

  2c_n + Σ_{m=1}^{n−1} c_m c_{n−m} = f_n,   c_0 = f_0 = 1.   (4.1)

That is, (Σ c_n tⁿ)² = Σ f_j t^j, which is (2.5) with t² renamed t. (`Romik.conv`.)

*Integrality.* We argue by strong induction. The sum S = Σ_{m=1}^{n−1} binom(2n,2m) v(m)v(n−m) is even. The involution m ↦ n−m preserves the summands. Its only possible fixed point is m = n/2, which contributes binom(2n,n)v(n/2)², and the central binomial coefficient is even. Hence (2.6) gives v(n) = 2^{n−1}Π₃(n) − S/2 ∈ ℤ. (`romikQ_int`.)

### 4.2 The weight bound

**Lemma 4.1.** If 2j < p^{2B+1}, then ν_p((2j)!) ≤ ν_p(Π₃(j)) + B.

*Proof.* Write Π₃(j) = A_j² with A_j = ∏_{i<j}(4i+1). For L large, counting by prime powers gives ν_p(A_j) = Σ_{s=1}^{L} N_s, where N_s = #{i < j : p^s | 4i+1}. Legendre gives ν_p((2j)!) = Σ_s ⌊2j/p^s⌋. Fix P = p^s. Since 4 is invertible mod P, there is a unique v_P ∈ [0,P) with P | 4v_P+1, and N_s = ⌊j/P⌋ + [v_P < j mod P]. Since ⌊2j/P⌋ ≤ 2⌊j/P⌋+1, every s contributes 2N_s − ⌊2j/P⌋ ≥ −1. If s is even, then P ≡ 1 (mod 4) and v_P = (P−1)/4. Now ⌊2j/P⌋ = 2⌊j/P⌋+1 forces j mod P ≥ P/2 > v_P, so the contribution is ≥ 0. If P > 2j, the contribution is ≥ 0. So only odd s with p^s ≤ 2j < p^{2B+1} can contribute −1, and there are at most B of them. ∎ (`RomikWeight.weight`.)

Let K(j) = ⌊j/a⌋, so K(j) = ⌊2j/(p+1)⌋. Take B ≥ 0 least with 2j < p^{2B+1}. If B = 1, then 2j ≥ p, and since 2j is even and p is odd, 2j ≥ p+1, so K(j) ≥ 1. Moreover K(j) ≥ 2 = B+1 when j ≥ 2a. If B ≥ 2, then 2j ≥ p^{2B−1} ≥ (p+1)(B+1), using (p+1)(B'+2) ≤ p^{2B'+1} for B' ≥ 1 (by induction), so K(j) ≥ B+1. Lemma 4.1 then gives

  ν_p((2j)!) ≤ ν_p(Π₃(j)) + K(j) for all j,   ν_p((2j)!) + 1 ≤ ν_p(Π₃(j)) + K(j) for j ≥ 2a.   (4.2)

### 4.3 Normalisation and the no-carry recurrence

Put d_n = p^{K(n)} c_n and g_j = p^{K(j)} f_j. By (4.2), every g_j is p-integral, and g_j ≡ 0 (mod p) for j ≥ 2a. For m ≤ n,

  K(m) + K(n−m) + [m mod a > n mod a] = K(n)   (carry lemma).

So p^{K(n)} c_m c_{n−m} = p^{[carry]} d_m d_{n−m}. Multiplying (4.1) by p^{K(n)}, induction shows that every d_n is p-integral (2 is a p-unit). Reducing mod p, D_n := d_n mod p and G_j := g_j mod p satisfy D_0 = 1 and

  Σ_{0 ≤ m ≤ n, m mod a ≤ n mod a} D_m D_{n−m} = G_n   (n ≥ 1).   (NC)

(`Romik.dd_pint`, `Romik.noCarry_rec`.)

### 4.4 The explicit square root in characteristic p

In F_p[x][y], put F₀ = Σ_{r<a} G_r x^r, W₁ = Σ_{r<a} G_{a+r} x^r, G = F₀ + W₁y and c = G_a. For M ≥ 0 let

  E_M = G^a · ∏_{i<M} (1 + c·y^{p^{i+1}})^h.

**Lemma 4.2.** E_M² ≡ G (mod x^a, y^{p^{M+1}}).

*Proof.* Since 2a = p+1 and 2h = p−1, we have E_M² = G · G^p · ∏_{i<M}(1 + c y^{p^{i+1}})^{p−1}. By Frobenius, G^p = F₀^p + W₁^p y^p. Both F₀ − 1 and W₁ − c are divisible by x, and c^p = c. So F₀^p − 1 = (F₀−1)^p and W₁^p − c = (W₁−c)^p are divisible by x^p, hence by x^a (a ≤ p). Therefore G^p ≡ 1 + c y^p. Next, by induction on M, (1 + cY)∏_{i<M}(1 + cY^{p^i})^{p−1} = 1 + cY^{p^M}, since (1 + cY^{p^M})^p = 1 + cY^{p^{M+1}}. Substituting Y = y^p gives (1 + cy^p)∏_{i<M}(1 + cy^{p^{i+1}})^{p−1} = 1 + c y^{p^{M+1}} ≡ 1. ∎ (`RomikPoly.sq_mem`.)

**Proposition 4.3.** D_n = [y^{⌊n/a⌋} x^{n mod a}] E_M whenever ⌊n/a⌋ < p^{M+1}.

*Proof.* Write e(K,R) for the coefficients of E_M. Because G_j = 0 for j ≥ 2a, Lemma 4.2 read at y^K x^R (R < a, K < p^{M+1}) says that Σ_{K₁≤K, R₁≤R} e(K₁,R₁) e(K−K₁,R−R₁) = G_{aK+R}. The map (K₁,R₁) ↦ aK₁+R₁ is a bijection from [0,K]×[0,R] onto {m ≤ n : m mod a ≤ n mod a}, where n = aK+R. So n ↦ e(⌊n/a⌋, n mod a) satisfies (NC). It also takes the value 1 at n = 0. Since 2 is invertible mod p, (NC) determines its solution by strong induction. ∎ (`RomikPoly.main`.)

**Lemma 4.4 (reading digits).** If deg_y A < p, then [y^K](A · B(y^p)) = [y^{K mod p}]A · [y^{⌊K/p⌋}]B. We have deg_y G^a ≤ a < p and [y^j]G^a = binom(a,j) W₁^j F₀^{a−j}. Consequently:
- (V) if K mod p > a, then [y^K]E_M = 0;
- (T) for M = 2 (so K < p³), with base-p digits k₀ = K mod p, k₁ = ⌊K/p⌋ mod p, k₂ = ⌊K/p²⌋,
  [y^K x^R]E₂ = binom(a,k₀) · c^{k₁}binom(h,k₁) · c^{k₂}binom(h,k₂) · [x^R](W₁^{k₀}F₀^{a−k₀}).

(`RomikPoly.co_EE_eq_zero`, `RomikPoly.co_EE_two`.)

**Lemma 4.5.** c ≠ 0, and G_{a+r} = c·w_r for r < d, where w_r = ∏_{i=1}^{r}(4i−1)²/(2r+1)!. Hence [x^R]W₁^a = c^a [x^R]W_p^a for R < d.

*Proof.* (2a)! = (p+1)·p·(p−1)!, so c = Π₃(a)/((p+1)(p−1)!) mod p. For i < a we have 0 < 4i+1 < 2p and 4i+1 ≢ 0 (mod p), because 4i+1 = p would force p ≡ 1 (mod 4). So c ≠ 0. Next, f_{j+1}(2j+1)(2j+2) = f_j(4j+1)². For j = a+r with r+1 < d this reduces mod p to G_{a+r+1}(2r+2)(2r+3) = G_{a+r}(4r+3)². This is the recursion of w_r, and its factors are units because 2r+3 < p. So W₁ ≡ c·W_p (mod x^d), and x^d divides W₁^a − (cW_p)^a. ∎ (`Romik.Gr_a_ne`, `Romik.W1_pow_coeff`.)

*Remark 4.6.* The pool-060 write-up obtains (T), its formula (F), by expanding √F with the binomial series and reducing a sum over minimal compositions. Proposition 4.3 replaces that step. It identifies the reduced coefficients directly as those of the unique square root of F₀ + W₁y in characteristic p. The digit formula then follows from Frobenius alone. Everything is a finite polynomial identity.

### 4.5 Valuation links

Write ν = ν_p((2n)!) = ν_p of (2n)!, with (2n)! = p^ν u and p ∤ u, and put K = K(n). Then v(n) = 2^n u p^{ν−K} d_n. Hence:
(i) if K + e ≤ ν, then p^e | v(n);
(ii) if K + e ≤ ν + 1 and D_n = 0, then p^e | v(n);
(iii) if ν + 1 = K + e and D_n ≠ 0, then p^e ∤ v(n), because v(n)/p^{e−1} = 2^n u d_n is a p-adic unit.
(`Romik.link_ge`, `Romik.link_red`, `Romik.link_not`.)

### 4.6 Theorem A

Let e = 2t+1 and write n = aK + R with 0 ≤ R < a. Then 2n = pK + (K + 2R). Since 4R < 2(p+1), the hypothesis forces K ≥ tp + a. Legendre gives ν ≥ ⌊2n/p⌋ + ⌊2n/p²⌋ = K + ⌊(K+2R)/p⌋ + ⌊2n/p²⌋, and both floors are at least t. If ν ≥ K + e we are done by (i). Otherwise ⌊(K+2R)/p⌋ = t, so K + 2R < p(t+1). If K = tp + a, the hypothesis gives 2R ≥ a and so K + 2R > p(t+1), which is impossible. Hence tp + a < K < p(t+1), and K mod p = K − tp > a. By (V) and Proposition 4.3 (with M large), D_n = 0. Since ν ≥ K + e − 1, (ii) gives p^e | v(n). ∎ (`RomikArith.odd_arith`, `romik_conj44_odd`.)

### 4.7 Theorem B

Let e = 2t ≥ 2 and tp² ≤ 2n. Write 2n = p²T + pS + U with 0 ≤ S, U < p. Legendre gives ν = (p+1)T + S + ν_p(T!), and T ≥ t. From (p+1)K + 2R = p²T + pS + U, 2R ≤ p−1 and U ≤ p−1 we get the φ-bound K + T ≤ pT + S + ⌊T/p⌋ + 1. Hence K + e ≤ K + 2T ≤ ν + 1, and p^{e−1} | v(n) by (i).

*Confinement.* Suppose ν < K + e. Then T = t and K + t = pt + S + ν_p(t!) + 1. If t ≥ p², the sharper bound K + T + 1 ≤ pT + S + ⌊T/p⌋ + ⌊T/p²⌋ ≤ pT + S + ν_p(T!) gives a contradiction, so t < p². Write t = pq + r₀ with q, r₀ < p. Then ν_p(t!) = q, and the two relations combine to U + r₀ = 2R + S + q + p + 1. They also give K = p²q + p(r₀ − q − 1) + (U − 2R), with digits (k₂,k₁,k₀) = (q, r₀−q−1, U−2R). In particular K < p³. (`RomikArith.even_conf`.)

*Necessity.* If p^e ∤ v(n), then (i) and (ii) give ν < K + e and D_n ≠ 0. By (T), k₀ ≤ a, k₁ ≤ h and k₂ ≤ h. Then r₀ ≤ q + a and k₀ = p + q + 1 + S − r₀ ≥ a + S. So S = 0, k₀ = a, r₀ = q + a and q < h. Hence e = 2t = (p+1)(2q+1). Also U = a + 2R < p, which gives 4R < p+1, and 4n = 2(p²t + U) = ep² + (p+1) + 4R. The residue is D_n = c^{a+h+q} binom(h,q) [x^R]W₁^a = c^{2a+h+q} binom(h,q) [x^R]W_p^a, so R ∈ E_p.

*Sufficiency.* Suppose q < h, R ∈ E_p, e = (p+1)(2q+1) and 4n = ep² + (p+1) + 4R. Then n = aK + R with K = p²q + ph + a. Also 2n = p²t + (a + 2R) with t = pq + q + a, which gives ν + 1 = K + e. The digits of K are (q, h, a), and D_n = c^{2a+h+q} binom(h,q) [x^R]W_p^a ≠ 0, because binom(h,q) is not divisible by p (h < p). By (iii), p^e ∤ v(n). ∎ (`RomikArith.even_conv`, `romik_conj44_even_exact`.)

## 5. Formal verification

Ten modules, 2,187 lines in total: `RomikDefs` (definitions, bridge, integrality), `RomikValues` (printed values), `RomikPint` (p-integral rationals), `RomikWeight` (Lemma 4.1), `RomikNorm` (§4.1–4.3), `RomikPoly` (Lemma 4.2, Proposition 4.3), `RomikDigits` (Lemma 4.4), `RomikArith` (§4.6–4.7 arithmetic), `RomikLink` (§4.5, Lemma 4.5) and `RomikMain` (endpoints and guards). Toolchain: Lean 4.34.1 and Mathlib `d13f23b7`, with specific imports only. No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` is used. Every module compiles in under 25 s and passes the standalone kernel checker. A fresh replay extracted from the printed appendix reproduced the oleans byte for byte. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every endpoint and guard.

## 6. Significance

Krattenthaler and Müller proved v(n) ≡ 0 (mod p^e) for n ≥ ⌈(e−1)p²/2⌉ for every odd prime p (their Theorem 17), using a double induction on recurrence (2.6). For p ≡ 3 (mod 4), their data suggested thresholds roughly a factor of 2 smaller. The conjecture appears in all four arXiv versions. In v1 (April 2023) it is Conjecture 41, and its even clause names the single exception (p,e) = (7,8). In v4 (October 2024) it is Conjecture 44: three further exceptions are listed and the clause is weakened to "with very few exceptions". Theorem A settles the precise odd-exponent threshold. Theorem B gives the even-exponent threshold in the strongest possible form: an exact, finitely checkable list of exceptions for each p. It explains why the authors' list kept growing, and it completes the list.

The methods are elementary: Legendre counting, a Newton-polygon normalisation, and Frobenius in characteristic p. The new ingredient is the observation that the normalised residues of √F form the square root of a polynomial that is *linear in the second variable*. That square root has the explicit product form E_M. This makes the result a modest but genuine sharpening of a published theorem, settling a precise conjecture of a specialist paper. It is not a breakthrough.

Three limitations. The formal statement covers only p ≡ 3 (mod 4), as the conjecture does. It says nothing about Conjectures 43 and 45 of [KM]. The even clause is resolved by an exact classification, not by a yes/no answer, because the source's own wording ("very few exceptions") leaves no sharper target. The classification decides each reading of that wording:
- "only the four listed exceptions" is false, because of (3,4) and (11,12);
- "finitely many exceptions for each p" is true;
- "finitely many exceptions in total" is false, because every p has at least (p−1)/2 exceptions.

## 7. Prior art

The following is taken from the adversarial review (`REVIEW-358162.md`, §1, 2026-11-20). The arXiv record 2304.11471 has versions v1 (22 Apr 2023) to v4 (13 Oct 2024) and no journal reference. Krattenthaler's publication list still gives it as a preprint. Oberwolfach Preprint OWP 2024-12 is the same paper and prints Conjecture 44 identically. Semantic Scholar and OpenAlex (W4366999535) show zero citations. A web search found only the source, the earlier mod-p paper (arXiv:1904.04509, Scherer) and Romik's original article. None of them resolves the conjecture. Searches of the Omega registry and of the campaign's Principia list found no entry.

A final check on 2026-11-20 refreshed these searches.
- The arXiv abstract page still shows v4 as the latest version, with no journal reference.
- OpenAlex lists the arXiv record (W4366999535) and the Oberwolfach preprint record (RENATE, DOI 10.34657/31035). Both have zero citing works.
- The omega registry's GitHub issues and pull requests contain nothing on "2304.11471", "Romik sequence", "Krattenthaler Müller theta" or "358162".
- A GitHub code search for "2304.11471" found one research note that cites only the source's Theorem 23, on d(n).
- The local Principia, mio-math, omega and openai/math clones have no entry for the source or for Conjecture 44.

As far as a bounded search can tell, the result is not public.

## References

[KM] C. Krattenthaler and T. W. Müller, *The congruence properties of Romik's sequence of Taylor coefficients of Jacobi's theta function θ₃*, arXiv:2304.11471 (v4, 2024); Oberwolfach Preprint OWP 2024-12.
[R] D. Romik, *The Taylor coefficients of the Jacobi theta constant θ₃*, Ramanujan J. 52 (2020), 275–290.
[S] R. Scherer, *Congruences modulo primes of the Romik sequence related to the Taylor expansion of the Jacobi theta constant θ₃*, Ramanujan J. 54 (2021), 427–448; arXiv:1904.04509.
