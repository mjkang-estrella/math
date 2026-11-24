# The number of bias orderings for k-indivisible partitions grows polynomially

**A machine-checked proof of the Jackson–Otgonbayar growth conjecture (MathDB 355348)**

## Abstract

Jackson and Otgonbayar studied how parts of k-indivisible partitions of n distribute among the residue classes modulo t.
For each k ≥ 2 coprime to t, their second-order asymptotic term orders the classes 1, …, t, and they let 𝒪(t) count the
distinct orderings over all such k. They conjectured that 𝒪(t)/φ(t) = o(t) and log t = o(𝒪(t)/φ(t)). We prove both
assertions. For every family of relations sandwiched between the strict and the weak comparison of the source's scores
(which includes the source's eventual-bias relation, by the source's Corollary 1.2), and every integer H ≥ 1,

    𝒪(t) ≤ φ(t) (⌊t/H⌋ + 2H² + 2)        (t ≥ 2),
    𝒪(t) ≥ φ(t) t^{1/4} / 80              (t sufficiently large).

The lower bound comes from a new invariant: on a positive proportion of units q, the residue k mod t is the unique label
with the most right inversions, so orderings from different residue classes cannot coincide. The full argument,
including the bridge from Γ′/Γ to its series, is checked in Lean 4 with Mathlib, using only the axioms propext,
Classical.choice and Quot.sound. The written argument gives the sharper bounds c φ(t) t^{1/3} ≤ 𝒪(t) ≤ C φ(t) √t log(2t)
(Remark 6.1); those sharper rates are not part of the Lean certificate.

## 1. The conjecture and the source's definitions

Source: F. Jackson and M. Otgonbayar, *Unexpected Biases between Congruence Classes for Parts in k-indivisible
Partitions*, arXiv:2207.06365v1 (2022); J. Number Theory 248 (2023) 310–342. Quotations are from the arXiv v1 text
(PDF text extraction, with mathematical typesetting restored).

**Conjecture 1.5** (verbatim). "As t → ∞, we have 𝒪(t)/φ(t) = o(t) and log t = o(𝒪(t)/φ(t))."

MathDB record 355348 states the same: "Let 𝒪(t) denote the number of possible orderings arising from the biases among
congruence classes for k-indivisible partitions, and let φ(t) be Euler's totient function. **Growth conjecture.** As
t → ∞, we have 𝒪(t)/φ(t) = o(t) and log t = o(𝒪(t)/φ(t)). …" The record names 𝒪(t) only informally; the definition
used here is the source's (quoted below).

The source's definitions, verbatim:

- (1.4) "D×_k(r,t;n) := Σ_{λ⊢n, λ∈D×_k} #{λ_j : λ_j ≡ r (mod t)}, where D×_k denotes the set of k-indivisible partitions."
- Theorem 1.1: "Let k, t ≥ 2 be coprime integers and let 1 ≤ r ≤ t. If K := 1 − 1/k and 1 ≤ r̄ ≤ t is a representative of
  k⁻¹r modulo t, then as n → ∞, D×_k(r,t;n) = [main factor] · ( (K/2) log n − ψ(r/t) + k⁻¹ ψ(r̄/t) + C_{k,t} + O(n^{−1/2} log n) ),
  where ψ(x) := Γ′(x)/Γ(x) is the digamma function".
- (1.5) "ψ_{k,t}(r) := −ψ(r/t) + (1/k) ψ(r̄/t)."
- Corollary 1.2: "Furthermore, if we have ψ_{k,t}(r) > ψ_{k,t}(s), then for sufficiently large n we have that
  D×_k(r,t;n) > D×_k(s,t;n)."
- "For 1 ≤ r, s ≤ t, we write r ≺_{k,t} s (resp. r ≻_{k,t} s) if D×_k(r,t;n) < D×_k(s,t;n) (resp. D×_k(r,t;n) > D×_k(s,t;n))
  for all sufficiently large n. Also, let 𝒪(t) be the number of distinct orderings of {1, . . . t} induced by ≺_{k,t} over
  all k such that k ≥ 2 and gcd(k, t) = 1."
- §2: "the digamma function ψ, defined as the logarithmic derivative of Γ, ψ(x) := Γ′(x)/Γ(x)".

The source remarks that ≺_{k,t} might fail to be total when two scores tie; a later paper of the same authors
(arXiv:2305.05753, Theorem 1.1) proves there are no ties. We do not use that theorem.

### 1.1 The Lean transcription

All definitions live in namespace `BiasGrowth`, file `BiasDefinitions.lean`. A label `r : Fin t` stands for the source's
residue class r+1 ∈ {1, …, t}. `R k r s` means "class r+1 is eventually strictly more common than class s+1", that is,
r+1 ≻_{k,t} s+1.

```lean
/-- The real part of the logarithmic derivative of the complex Gamma function. -/
noncomputable def psi (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

/-- Positive representative of the inverse residue, with zero represented by t. -/
noncomputable def rbar (k t r : ℕ) : ℕ :=
  let v := (((r : ZMod t) * (k : ZMod t)⁻¹) : ZMod t).val
  if v = 0 then t else v

/-- The source's second-order score, equation (1.5). -/
noncomputable def psiKT (k t r : ℕ) : ℝ :=
  -psi ((r : ℝ) / t) + psi ((rbar k t r : ℝ) / t) / k

def Compatible (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) : Prop :=
  ∀ k, 2 ≤ k → Nat.Coprime k t → ∀ r s : Fin t,
    (psiKT k t (r.val+1) > psiKT k t (s.val+1) → R k r s) ∧
    (R k r s → psiKT k t (r.val+1) ≥ psiKT k t (s.val+1)) ∧ ¬ R k r r

noncomputable def orderCount (t : ℕ) (R : ℕ → Fin t → Fin t → Prop) : ℕ :=
  Set.ncard {S : Fin t → Fin t → Prop | ∃ k : ℕ, 2 ≤ k ∧ Nat.Coprime k t ∧ S = R k}
```

`Complex.digamma` is Mathlib's `logDeriv Complex.Gamma`, so `psi` is Γ′/Γ on the positive reals. `rbar k t r` is the
representative in [1, t] of k⁻¹r mod t. `psiKT` is (1.5) literally. `orderCount t R` counts the distinct labelled
relations R k over all k ≥ 2 coprime to t, with no upper bound on k.

**Why `Compatible` captures the source's ≺.** Let R_k(r, s) be "r ≻_{k,t} s". Corollary 1.2 gives
ψ_{k,t}(r) > ψ_{k,t}(s) ⇒ R_k(r, s). If R_k(r, s) and ψ_{k,t}(s) > ψ_{k,t}(r), Corollary 1.2 applied to (s, r) would make s
eventually more common than r, a contradiction; so R_k(r, s) ⇒ ψ_{k,t}(r) ≥ ψ_{k,t}(s). R_k is irreflexive. Hence the
source's family is `Compatible`, and 𝒪(t) = `orderCount t R` (the relation ≻ and the relation ≺ determine each other, so
counting either gives the same number). The theorem below is proved for **every** compatible family, so it applies to the
source's ≺ whatever it does at ties. The only step outside Lean is this use of the source's Corollary 1.2, which rests
on the source's circle-method Theorem 1.1.

### 1.2 The formal endpoints

```lean
theorem conjecture_355348 (R : ∀ t : ℕ, ℕ → Fin t → Fin t → Prop)
    (hR : ∀ t, 2 ≤ t → Compatible t (R t)) :
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop] (fun t => (t : ℝ)) ∧
    (fun t : ℕ => Real.log t) =o[atTop] (fun t => (orderCount t (R t) : ℝ) / Nat.totient t)

theorem conjecture_355348_strict :
    let R := fun t k (r s : Fin t) => psiKT k t (s.val+1) < psiKT k t (r.val+1)
    (fun t : ℕ => (orderCount t (R t) : ℝ) / Nat.totient t) =o[atTop] (fun t => (t : ℝ)) ∧
    (fun t : ℕ => Real.log t) =o[atTop] (fun t => (orderCount t (R t) : ℝ) / Nat.totient t)
```

Both print `[propext, Classical.choice, Quot.sound]` under `#print axioms`. They are, character for character after
whitespace normalisation, the statements fixed by the independent pre-Lean review (REVIEW-355348.md §5); the five
definitions agree with the review's up to the keyword `noncomputable` and docstrings.

**Non-vacuity checks**, all proved in Lean:
1. `compatible_strict`: the strict score relation is `Compatible` for every t, so the hypothesis of
   `conjecture_355348` is satisfiable, and `conjecture_355348_strict` is its instance.
2. `psi_gap_series`: ψ(1) − ψ(x) = Σ_{n≥0} (1/(n+x) − 1/(n+1)) for 0 < x ≤ 1, and `psi_one`: ψ(1) = −γ.
   So `psi` is the genuine digamma function, not a stand-in.
3. `rbar_pos`, `rbar_le`, `rbar_modEq`: 1 ≤ r̄ ≤ t and k·r̄ ≡ r (mod t) when gcd(k, t) = 1; `rbar_bijOn`: r ↦ r̄ permutes
   [1, t].
4. `orderings_finite`, `orderings_nonempty`, `orderCount_pos`: the set of relations is finite (there are finitely many
   relations on Fin t) and contains R (t+1) for t ≥ 2, so `Set.ncard` is the true count, never the infinite-set default 0.
5. k ranges over all of ℕ. No hypothesis assumes the absence of ties or any asymptotic.

## 2. Analytic estimates

Put A(x) = ψ(1) − ψ(x) and F(x) = −A(x) for 0 < x ≤ 1. We use only the recurrence ψ(x+1) = ψ(x) + 1/x and the fact
that ψ is nondecreasing on (0, ∞) (from log-convexity of Γ, the Bohr–Mollerup property in Mathlib).

**Lemma 2.1 (series).** For 0 < x ≤ 1, A(x) = Σ_{n≥0} (1/(n+x) − 1/(n+1)), the summands being nonnegative.

*Proof.* Iterating the recurrence, ψ(x+N) = ψ(x) + Σ_{n<N} 1/(x+n). So the N-th partial sum equals
A(x) − (ψ(1+N) − ψ(x+N)). By monotonicity and one step of the recurrence, 0 ≤ ψ(1+N) − ψ(x+N) ≤ ψ(x+N+1) − ψ(x+N) = 1/(x+N),
which tends to 0. Nonnegative summands with convergent partial sums give a `HasSum`. ∎

**Lemma 2.2.** For 0 < x ≤ 1:
(1) 1/x − 1 ≤ A(x) ≤ 1/x.
(2) For x ≤ y ≤ 1: ψ(y) − ψ(x) ≥ (3/2)(y − x).
(3) If moreover x ≥ 9/10: ψ(y) − ψ(x) ≤ (5/2)(y − x).

*Proof.* (1) Monotonicity gives ψ(1) ≤ ψ(x+1) = ψ(x) + 1/x and ψ(x+1) ≤ ψ(2) = ψ(1) + 1.
(2) Subtracting the two series, ψ(y) − ψ(x) = (y − x) Σ_{n≥0} 1/((n+x)(n+y)), and the first seven terms are at least
Σ_{j=1}^{7} j⁻² > 3/2. (3) The n = 0 term is at most 1/x², and for n ≥ 1, 1/((n+x)(n+y)) ≤ 1/(n−1+x) − 1/(n+x), which
telescopes to 1/x. So the coefficient is at most 1/x² + 1/x ≤ 100/81 + 10/9 = 190/81 < 5/2. ∎

For a label a ∈ [1, t] write A_a = A(a/t), F_a = F(a/t), and ρ(r) = r̄. Define

    B_k(r) = ψ(r/t) + A_{ρ(r)}/k = ψ(1)/k − ψ_{k,t}(r).                  (4)

So B is minus the source's score plus a constant independent of r: R_k(r, s) forces B_k(r) ≤ B_k(s), and B_k(r) < B_k(s)
forces R_k(r, s). Small B means "more common". Since ρ depends on k only through k mod t, along a residue class
k ≡ q (mod t) the permutation ρ is fixed and, for r < s,

    B_k(s) − B_k(r) = c + d/k,  c = ψ(s/t) − ψ(r/t) > 0,  d = A_{ρ(s)} − A_{ρ(r)}.     (5)

**Lemma 2.3 (support).** If r < s and B_k(s) ≤ B_k(r) (a weak inversion), then 3k·ρ(r)·(s − r) ≤ 2t².

*Proof.* By (2), c ≥ (3/2)(s − r)/t, and by (1), −d ≤ A_{ρ(r)} ≤ t/ρ(r). A weak inversion means c ≤ −d/k. ∎

## 3. The upper bound

**Theorem 3.1.** For every t ≥ 2, H ≥ 1 and compatible R, orderCount(t, R) ≤ φ(t)(⌊t/H⌋ + 2H² + 2).

*Proof.* Split the admissible k by their residue q = k mod t, a unit; there are φ(t) classes. Within a class, split
k into the small part kH < t² and the tail kH ≥ t².

*Small part.* The map k ↦ ⌊k/t⌋ is injective on a residue class and takes values ≤ ⌊t/H⌋, so at most ⌊t/H⌋ + 1 values of k,
hence at most that many relations.

*Tail.* If r < s is weakly inverted at some tail k, Lemma 2.3 and t² ≤ kH give ρ(r)(s − r) ≤ 2H/3, so ρ(r) ≤ H and
s − r ≤ H. The map (r, s) ↦ (ρ(r) − 1, s − r − 1) is injective (ρ is a bijection) into [0, H)², so the set P of pairs that can
ever be weakly inverted in the tail has at most H² elements. All other pairs r < s satisfy B_k(r) < B_k(s) strictly
throughout the tail. By (5) and c > 0, each pair in P has at most one tail parameter with B_k(s) = B_k(r) (an affine function
of 1/k with positive intercept has at most one zero), and its set of strict inversions is downward closed in k. Call a tail
k *exceptional* if some pair in P ties at k; there are at most |P| ≤ H² exceptional k. At a non-exceptional k every pair is
strictly ordered, and compatibility then determines R_k completely from the set of strictly inverted pairs in P
(`compatible_iff_B`, `same_relation_of_pair_signs`). These sets form a chain under inclusion as k increases, and a chain of
subsets of P has at most |P| + 1 members. Each exceptional k contributes one relation, however R resolves its ties. So the
tail contributes at most 2H² + 1 relations. This argument works on any finite sample of the unbounded tail
(`chain_with_exceptions_card_le`, `reciprocal_patterns_card_le`), so no cap on k is introduced.

Adding, each residue class contributes at most ⌊t/H⌋ + 2H² + 2 relations; summing over the φ(t) classes, with overlaps
counted, gives the bound. ∎

**Corollary 3.2.** 𝒪(t)/φ(t) = o(t). *Given ε > 0, fix an integer H > 2/ε. Then ⌊t/H⌋ ≤ εt/2, and 2H² + 2 ≤ εt/2 for large t.* ∎

## 4. Class recovery: the residue of k is visible in the ordering

For a relation S on Fin t, let I_S(r) = #{s > r : S(s, r)}, the number of right inversions of r (labels to the right of r
that are strictly more common). This depends only on the labelled relation.

**Theorem 4.1 (class recovery).** Let t > 40, k ≥ 20t, gcd(k, t) = 1, let q ∈ [1, t] satisfy k ≡ q (mod t) and
9t ≤ 10q, 20q ≤ 19t, and put X = t²/k with X > 60. For every compatible R and every label r ≠ q,
I_{R_k}(r) < I_{R_k}(q).

*Proof.* *Other labels.* For r ≠ q, ρ(r) ≥ 2, since ρ(r) = 1 means r ≡ k ≡ q (mod t). A right inversion
s of r under R_k is a weak inversion in B, so by Lemma 2.3, s − r ≤ 2t²/(3ρ(r)k) ≤ X/3. There is one label at each
distance, so I(r) ≤ ⌊X/3⌋ (`other_inversion_count_le`).

*The label q.* Put h = t − q, so t/20 ≤ h ≤ t/10. For 1 ≤ a ≤ 9, the label with ρ = a is ≡ qa ≡ −ah, that is t − ah ≤ q.
So every s > q has ρ(s) ≥ 10 (`right_label_inverse_ge_ten`), and by (1), A_1 − A_{ρ(s)} ≥ (t − 1) − t/10 = 9t/10 − 1
(`distinguished_gap_lower`). If moreover k(s − q) ≤ (7/20)t², then by (3),
k(ψ(s/t) − ψ(q/t)) ≤ (5/2)k(s − q)/t ≤ 7t/8 < 9t/10 − 1 ≤ A_1 − A_{ρ(s)} for t > 40, so B_k(s) < B_k(q) strictly, and s is a right inversion of
q under every compatible R (`forced_right_inversion`). Since k ≥ 20t, the labels q < s ≤ q + ⌊7X/20⌋ satisfy this and stay
≤ t (⌊7X/20⌋ ≤ 7t/400 < h). Hence I(q) ≥ ⌊7X/20⌋ > X/3 when X > 60. ∎

So, among the selected parameters, a relation determines its residue class q as the unique maximiser of I
(`recover_label_of_unique_maxima`). This is what prevents collisions between the φ(t) residue classes.

## 5. Consecutive switches within a class

**Lemma 5.1 (monotonicity).** Let k < l be admissible with k ≡ l (mod t), and r < s. If R_l(s, r) then R_k(s, r).

*Proof.* R_l(s, r) gives B_l(s) ≤ B_l(r), i.e. c + d/l ≤ 0 with c > 0, so d < 0 and c + d/k < c + d/l ≤ 0; this is a strict
score comparison at k, which forces R_k(s, r) (`right_inversions_antitone`). ∎

**Theorem 5.2 (strict drop).** Let m ≥ 20, t > 100(m+2)³, q ∈ [9t/10, 19t/20], k = mt + q, with k and k + t coprime to t.
Then I_{R_{k+t}}(q) < I_{R_k}(q) for every compatible R.

*Proof.* By Lemma 5.1, inversions at q can only disappear from k to k + t; it suffices to find one label s > q with
B_k(s) < B_k(q) and B_{k+t}(s) > B_{k+t}(q) strictly (`rightInvCount_strict_drop`). Put A = 4(m+2), y_j = ψ((q+j)/t) − ψ(q/t)
for 0 ≤ j ≤ h, u = A_1/(k+t), v = (A_1 − t/A)/k. By (3) the increments of y are at most δ = 5/(2t); y_0 = 0 ≤ u; and
y_h ≥ (3/2)h/t ≥ 3/40 > v. Explicit scalar bounds (`switch_scalar_bounds`) give A·δ < v − u under t > 100(m+2)³. A mesh
with steps ≤ δ that crosses an interval longer than Aδ has at least A points in it (`mesh_point`,
`mesh_avoids_small_labels`), and as ρ is injective at most A − 1 labels have ρ < A; so some j ∈ [1, h] has u < y_j < v and
a = ρ(q+j) ≥ A. For s = q + j: at k, y_j < (A_1 − t/A)/k ≤ (A_1 − A_a)/k, so B_k(s) < B_k(q); at k + t,
y_j > A_1/(k+t) ≥ (A_1 − A_a)/(k+t), so B_{k+t}(s) > B_{k+t}(q). ∎

## 6. Counting, unit density, and the lower bound

**Theorem 6.1 (injection).** Let M ≥ 1 and t > 100(M+22)³. Let G(t) be the set of q ∈ [1, t] with gcd(q, t) = 1,
9t ≤ 10q and 20q ≤ 19t. Then for every compatible R, |G(t)|·M ≤ orderCount(t, R).

*Proof.* Map (q, i) ∈ G(t) × [0, M) to the relation R_k with k = (20+i)t + q, which is admissible. The conditions of
Theorem 4.1 hold for every such k (k ≤ (M+21)t and 60(M+21) < t give X > 60), so the relation determines q. For fixed q,
Theorem 5.2 with m = 20 + i (note 100(m+2)³ < t) makes i ↦ I_{R_k}(q) strictly decreasing on [0, M), so the relation
determines i. The map is injective into the full, uncapped set counted by orderCount. ∎

**Theorem 6.2 (unit density).** For all sufficiently large t, |G(t)| ≥ φ(t)/40.

*Proof.* Let P be the set of prime factors of t, E = 2^{|P|}, and U(x) = #{1 ≤ q ≤ x : gcd(q, t) = 1}. Expanding the indicator
of "no prime of P divides q" over subsets of P (`sieve_interval_identity`) and replacing each ⌊x/d⌋ by x/d gives
|U(x) − xφ(t)/t| ≤ E (`unitPrefix_error`); the main coefficient is identified exactly with φ(t)/t by evaluating at x = t.
Taking the difference of the prefixes at ⌊9t/10⌋ and ⌊19t/20⌋ gives |G(t)| ≥ φ(t)/20 − 1 − 2E (using φ(t) ≤ t). It remains to
see 160E ≤ φ(t) eventually. Multiplicativity gives t ≤ 2φ(t)² (`totient_square_lower`; for odd p^e, p^e ≤ φ(p^e)², and
2^e ≤ 2φ(2^e)²). Splitting P into primes below 16 (at most 16 of them, crudely) and primes ≥ 16 (each contributing a factor
16 ≤ p to the radical, which divides t) gives E⁴ ≤ 16¹⁶ t (`prime_factor_error_fourth`). Hence (160E)⁴ ≤ 160⁴·16¹⁶ t ≤ t²/4
≤ φ(t)⁴ once t ≥ 51200²·16¹⁶ (`prime_factor_error_small`). Then
φ(t)/20 − 2E − 1 ≥ 3φ(t)/80 − 1 ≥ φ(t)/40, as φ(t) ≥ 160E ≥ 160. ∎

No prime number theorem or distribution result for primes is used.

**Corollary 6.3.** For t large, orderCount(t, R)/φ(t) ≥ t^{1/4}/80; hence log t = o(𝒪(t)/φ(t)).

*Proof.* Let x = t^{1/4} ≥ 1000 and M = ⌊x⌋ ≥ x/2. Then M + 22 ≤ 2x, so 100(M+22)³ ≤ 800x³ < x⁴ = t, and Theorems 6.1 and
6.2 give orderCount ≥ (φ(t)/40)(x/2). Since log t = o(t^{1/4}) (Mathlib's `isLittleO_log_rpow_atTop`), the second
assertion follows. ∎

Corollaries 3.2 and 6.3 together are `conjecture_355348`; specialising to the strict family gives
`conjecture_355348_strict`.

**Remark 6.1 (sharper rates, not formalised).** With H = ⌊√t⌋ and the harmonic count D(H) = Σ_{a≤H} ⌊H/a⌋ ≤ H(1 + log H)
of the supported pairs in place of H², Theorem 3.1 gives 𝒪(t) ≤ C φ(t) √t log(2t). With M = ⌊(t/200)^{1/3}⌋ − 2 in
place of t^{1/4}, Theorem 6.1 gives 𝒪(t) ≥ c φ(t) t^{1/3}. These are the rates of the written proof; the Lean certificate
proves the weaker rates stated in the abstract, which already settle the conjecture. The independent reviewer computed
𝒪(t) exactly for t ≤ 120 and for eleven larger t up to 499 and found 𝒪(t)/φ(t) ≈ (0.18–0.20)·√t log(2t), so the upper
rate looks sharp and the true lower rate is probably far above t^{1/3}.

## 7. Significance

Conjecture 1.5 was posed on numerical evidence by the authors, who noted that pairs switch at most once within a residue
class of k and suggested spacing switching points as a route to a logarithmic lower bound, while saying the difficulty lay
in finding suitable pairs. The source itself only gets 𝒪(t) ≥ φ(t)/2 (Theorem 1.4(5)): for t/2 < k < t the class k is the least common one, so
those φ(t)/2 values of k give distinct orderings.

Of the two assertions, the upper bound is close to routine: a specialist would find the support-and-single-crossing count
quickly from the source's own lemmas, though some argument is needed because the trivial bound 𝒪(t) ≲ t² is not
o(tφ(t)). The lower bound carries the content. Its new idea is the class-recovery invariant of §4: on a positive
proportion of units q, the label q is the unique label with the most right inversions, so different residue classes give
different orderings. Combined with the mesh-and-exceptions switch of §5, this gives a polynomial lower bound, well beyond
the conjectured superlogarithmic growth. Everything is elementary once the invariant is seen; the independent review put
the probability that experts would not call it routine at 0.60. The result is a resolution of a conjecture from an
undergraduate-research paper in analytic combinatorics; it does not determine the true growth rate, which numerics suggest
is about φ(t)√t log t.

The formal proof covers everything after the source's Corollary 1.2. It does not formalise the circle-method asymptotic
behind Corollary 1.2, and it does not need the later no-ties theorem: the result holds for every way of resolving
possible ties consistently with Corollary 1.2.

## 8. Prior art (independent review REVIEW-355348.md §1, refreshed by the final check on 2026-11-20)

The pre-Lean reviewer's findings, with the final check's refresh marked:

- arXiv:2207.06365 has only v1 (13 Jul 2022), read in full; Conjecture 1.5 is on p. 5. The authors' own PDF is the same
  text, conjecture included.
- Journal version: J. Number Theory 248 (2023) 310–342, DOI 10.1016/j.jnt.2023.01.006 (arXiv metadata gives 2025 by
  mistake). ScienceDirect returned HTTP 403 to the pre-Lean reviewer; on 2026-11-20 its robots.txt answers but reads
  "User-agent: * / Disallow: /", so the publisher text (including the author manuscript OpenAlex lists) was not
  fetched, and **the journal text is unread**. Indirect evidence that the conjecture is still open there: the same authors' May 2023 sequel, written after
  the journal publication, proves only the no-ties conjecture and does not mention Conjecture 1.5 as resolved.
- Sequel arXiv:2305.05753 (JNT 2024), read in full: its Theorem 1.1 is "no ties"; nothing on 𝒪(t).
- Citing papers (OpenAlex, 8 citations of the JNT paper, 7 listed; Semantic Scholar, 7 citing the arXiv paper, rechecked
  2026-11-20): hook-length and reciprocal-sum bias papers (latest arXiv:2610.33791), an AMS Notices profile and the
  sequel; Semantic Scholar also lists the k-regular companion. None concerns the order count.
- The omega-institute registry (code clone of 2026-11-19, and its GitHub issues and pull requests searched on
  2026-11-20 for the arXiv id, the author name and the object), the Principia list and archive, the mio-qwq and
  openai/math clones had no entry for this problem. arXiv keyword searches (author Otgonbayar; "indivisible partitions")
  return only the source, the companion and the sequel. Web searches found only the source,
  the sequel, the k-regular companion paper (2207.04352) and a seminar abstract.

## 9. Reproducibility

The Lean sources (34 modules, Lean 4.34.1, pinned Mathlib d13f23b7) are reproduced byte-for-byte in
LEAN-SOURCE-APPENDIX.md. REPORT.md lists the compile and kernel-check receipts and the axiom output.
