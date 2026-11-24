# Lean source appendix (MathDB 372900)

Modules are listed in import order; each block is byte-identical to `src/<Module>.lean`.

### `RightShiftDefs.lean`

```lean
import Mathlib.Data.Int.Init
import Mathlib.Order.MinMax

/-!
# Source definitions (Yuan, Li, Zeng, arXiv:2602.01134, Section 2) and Conjecture 1

Binary sequences of length `n` are functions `Fin n → Bool` (the source works over `ℤ₂`;
`!x` is `x ⊕ 1`).  `get s i` is the letter `s_i`; every use below has `i < n`.
-/

namespace RightShift

/-- The letter `s_i` of `s = (s_0, …, s_{n-1})` (the value `false` for `i ≥ n` is never used). -/
def get {n : ℕ} (s : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then s ⟨i, h⟩ else false

/-- Source (Section 2): "A sequence `(s_0, s_1, …, s_{n-1})` is called a periodic finite-length
sequence if it is formed by multiple repetitions of a short sequence of length `e`, where `e` is a
proper divisor of `n`; otherwise, it is termed an aperiodic finite-length sequence." -/
def Aperiodic {n : ℕ} (s : Fin n → Bool) : Prop :=
  ¬ ∃ e : ℕ, e < n ∧ 0 < e ∧ e ∣ n ∧ ∀ i < n, get s i = get s (i % e)

/-- The prefix `s_d = (s_0, …, s_{d-1})` of `s`. -/
def pre {n : ℕ} (d : ℕ) (s : Fin n → Bool) : Fin d → Bool := fun i => get s i.val

/-- The structural part of Definition 2: for `c ≥ ⌊n/2⌋` and `1 ≤ d ≤ min{n - c, ⌊n/2⌋}`,
`s_n = s_{c+d} s[c+d:n]` with
`s_{c+d} = (s_0, …, s_{d-1})^q (s_0, …, s_{r-1}, s̄_r)`, `q = ⌊(c+d-1)/d⌋`,
`r = (c+d-1) - qd`, `s_d = (s_0, …, s_{d-1})` aperiodic, `s̄_r = s_r ⊕ 1`, and `s[c+d:n]` arbitrary. -/
def InBStruct (n c d : ℕ) (s : Fin n → Bool) : Prop :=
  n / 2 ≤ c ∧ 1 ≤ d ∧ d ≤ min (n - c) (n / 2) ∧ Aperiodic (pre d s) ∧
  (∀ j < (c + d - 1) / d, ∀ i < d, get s (j * d + i) = get s i) ∧
  (∀ i < (c + d - 1) - (c + d - 1) / d * d,
      get s ((c + d - 1) / d * d + i) = get s i) ∧
  get s ((c + d - 1) / d * d + ((c + d - 1) - (c + d - 1) / d * d))
    = !(get s ((c + d - 1) - (c + d - 1) / d * d))

/-- Definition 2: `B(n, c, d)` is "the set of aperiodic binary sequences `s_n` starting with
`s_{c+d}`" of the form above.  (The source notes that the structure already forces `s_n` to be
aperiodic; we keep the word "aperiodic" literally.) -/
def InB (n c d : ℕ) (s : Fin n → Bool) : Prop := Aperiodic s ∧ InBStruct n c d s

/-- Definition 3: `add(s_n) = t` when `s_{n-1-i} = s_{(d-1-i) mod d}` for `0 ≤ i < t` and
`s_{n-1-t} ≠ s_{(d-1-t) mod d}`.  Here `d` is the spacing of `s ∈ B(n, c, d)`; the residue
`(d-1-i) mod d ∈ [0, d)` is computed in `ℤ`.  (The source says "a certain positive integer `t`";
we also allow `t = 0`, which the source uses elsewhere; this only enlarges the statement.) -/
def IsAdd (n d : ℕ) (s : Fin n → Bool) (t : ℕ) : Prop :=
  t < n ∧ (∀ i < t, get s (n - 1 - i) = get s ((((d : ℤ) - 1 - i) % d).toNat)) ∧
  get s (n - 1 - t) ≠ get s ((((d : ℤ) - 1 - t) % d).toNat)

/-- The right circular shift `R^b(s_n) = (s_{n-b}, …, s_{n-1}, s_0, …, s_{n-b-1})`. -/
def rotR (n b : ℕ) (s : Fin n → Bool) : Fin n → Bool :=
  fun j => if j.val < b then get s (n - b + j.val) else get s (j.val - b)

/-- **Conjecture 1** (Yuan–Li–Zeng).  For `c ≥ ⌈n/2⌉` and `s_n ∈ B(n, c, n - c)`, if there
exists an integer `0 < b < n` such that `R^b(s_n) ∈ B(n, c, d₂)` satisfies
`add(R^b(s_n)) > add(s_n)`, then `b = d₂`. -/
def Conjecture1 : Prop :=
  ∀ (n c : ℕ) (s : Fin n → Bool), (n + 1) / 2 ≤ c → InB n c (n - c) s →
    ∀ b d₂ : ℕ, 0 < b → b < n → InB n c d₂ (rotR n b s) →
      ∀ t₁ t₂ : ℕ, IsAdd n (n - c) s t₁ → IsAdd n d₂ (rotR n b s) t₂ → t₁ < t₂ → b = d₂

end RightShift
```

### `RightShiftCount.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring

/-!
# Counting over integer intervals

`cntI F a b` is the sum of `F i` over the integer interval `[a, b)`.  We prove splitting,
shifting and periodicity lemmas, and the parity fact used in the Run Lemma: the
shift-difference word `j ↦ W j xor W (j + s)` of an `e`-periodic binary word has an even
number of `true` entries in every window of length `e`.
-/

namespace RightShift

/-- Sum of `F i` over the integer interval `[a, b)`. -/
def cntI (F : ℤ → ℕ) (a b : ℤ) : ℕ := ∑ i ∈ Finset.range (b - a).toNat, F (a + i)

lemma cntI_split (F : ℤ → ℕ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    cntI F a c = cntI F a b + cntI F b c := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = b - a := ⟨(b - a).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = c - b := ⟨(c - b).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h1 : (c - a).toNat = p + q := by omega
  have h2 : (b - a).toNat = p := by omega
  have h3 : (c - b).toNat = q := by omega
  unfold cntI
  rw [h1, h2, h3, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  push_cast
  omega

lemma cntI_single (F : ℤ → ℕ) (a : ℤ) : cntI F a (a + 1) = F a := by
  unfold cntI
  rw [show (a + 1 - a).toNat = 1 by omega, Finset.sum_range_one]
  simp

lemma cntI_zero (F : ℤ → ℕ) {a b : ℤ} (h : ∀ i, a ≤ i → i < b → F i = 0) : cntI F a b = 0 := by
  unfold cntI
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  exact h _ (by omega) (by omega)

lemma cntI_shift (F G : ℤ → ℕ) {a b : ℤ} (δ : ℤ) (h : ∀ i, a ≤ i → i < b → F i = G (i + δ)) :
    cntI F a b = cntI G (a + δ) (b + δ) := by
  unfold cntI
  rw [show b + δ - (a + δ) = b - a by ring]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [h _ (by omega) (by omega)]
  congr 1
  ring

lemma cntI_add (F G : ℤ → ℕ) (a b : ℤ) :
    cntI (fun j => F j + G j) a b = cntI F a b + cntI G a b := by
  unfold cntI
  exact Finset.sum_add_distrib

lemma cntI_mul (F : ℤ → ℕ) (k : ℕ) (a b : ℤ) :
    cntI (fun j => k * F j) a b = k * cntI F a b := by
  unfold cntI
  rw [Finset.mul_sum]

lemma cntI_step (F : ℤ → ℕ) {e : ℤ} (he : 0 ≤ e) (hF : ∀ i, F (i + e) = F i) (a : ℤ) :
    cntI F (a + 1) (a + 1 + e) = cntI F a (a + e) := by
  have h1 := cntI_split F (show a ≤ a + 1 by omega) (show a + 1 ≤ a + 1 + e by omega)
  have h2 := cntI_split F (show a ≤ a + e by omega) (show a + e ≤ a + 1 + e by omega)
  rw [cntI_single] at h1
  rw [show a + 1 + e = a + e + 1 by ring, cntI_single, hF] at h2
  rw [show a + 1 + e = a + e + 1 by ring] at h1 ⊢
  omega

/-- Sums over a full period of a periodic function do not depend on the starting point. -/
lemma cntI_period (F : ℤ → ℕ) {e : ℤ} (he : 0 ≤ e) (hF : ∀ i, F (i + e) = F i) (a b : ℤ) :
    cntI F a (a + e) = cntI F b (b + e) := by
  have key : ∀ k : ℤ, cntI F (a + k) (a + k + e) = cntI F a (a + e) := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [show a + (k + 1) = a + k + 1 by ring, cntI_step F he hF]
      exact ih
    | pred k ih =>
      rw [← ih, show a + -(k : ℤ) = a + (-(k : ℤ) - 1) + 1 by ring, cntI_step F he hF]
  have := key (b - a)
  rw [show a + (b - a) = b by ring] at this
  exact this.symm

/-- The shift-difference word of `W` with shift `s`. -/
def dw (W : ℤ → Bool) (s j : ℤ) : Bool := xor (W j) (W (j + s))

lemma dw_period (W : ℤ → Bool) {e : ℤ} (hW : ∀ j, W (j + e) = W j) (s j : ℤ) :
    dw W s (j + e) = dw W s j := by
  unfold dw
  rw [hW, show j + e + s = j + s + e by ring, hW]

lemma toNat_xor (x y : Bool) : (xor x y).toNat + 2 * (x && y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> rfl

/-- Parity: every period of a shift-difference word has an even number of `true` entries. -/
lemma dw_even (W : ℤ → Bool) {e : ℤ} (he : 0 ≤ e) (hW : ∀ j, W (j + e) = W j) (s p : ℤ) :
    Even (cntI (fun j => (dw W s j).toNat) p (p + e)) := by
  have hpt : ∀ j, (dw W s j).toNat + 2 * (W j && W (j + s)).toNat
      = (W j).toNat + (W (j + s)).toNat := fun j => toNat_xor _ _
  have hsum : cntI (fun j => (dw W s j).toNat) p (p + e)
      + 2 * cntI (fun j => (W j && W (j + s)).toNat) p (p + e)
      = cntI (fun j => (W j).toNat) p (p + e) + cntI (fun j => (W (j + s)).toNat) p (p + e) := by
    rw [← cntI_mul, ← cntI_add, ← cntI_add]
    unfold cntI
    exact Finset.sum_congr rfl (fun j _ => hpt _)
  have hshift : cntI (fun j => (W (j + s)).toNat) p (p + e)
      = cntI (fun j => (W j).toNat) (p + s) (p + e + s) :=
    cntI_shift _ _ s (fun i _ _ => rfl)
  have hper : cntI (fun j => (W j).toNat) (p + s) (p + e + s)
      = cntI (fun j => (W j).toNat) p (p + e) := by
    rw [show p + e + s = p + s + e by ring]
    exact cntI_period _ he (fun i => by simp only [hW]) _ _
  rw [hshift, hper] at hsum
  refine ⟨cntI (fun j => (W j).toNat) p (p + e)
      - cntI (fun j => (W j && W (j + s)).toNat) p (p + e), ?_⟩
  omega

/-- After a `true` entry of a shift-difference word, the next `true` entry comes within `e - 1`. -/
lemma dw_next (W : ℤ → Bool) {e : ℤ} (he : 0 < e) (hW : ∀ j, W (j + e) = W j) (s p : ℤ)
    (hp : dw W s p = true) : ∃ q, p < q ∧ q < p + e ∧ dw W s q = true := by
  by_contra hcon
  push Not at hcon
  have hz : cntI (fun j => (dw W s j).toNat) (p + 1) (p + e) = 0 := by
    refine cntI_zero _ (fun i hi1 hi2 => ?_)
    have h := hcon i (by omega) hi2
    cases hq : dw W s i
    · rfl
    · exact absurd hq h
  have hsplit := cntI_split (fun j => (dw W s j).toNat) (show p ≤ p + 1 by omega)
    (show p + 1 ≤ p + e by omega)
  rw [cntI_single, hz, hp] at hsplit
  have hev := dw_even W he.le hW s p
  rw [hsplit] at hev
  exact absurd hev (by decide)

end RightShift
```

### `RightShiftRun.lean`

```lean
import RightShiftCount

/-!
# The Run Lemma

Let `W : ℤ → Bool` be `e`-periodic and write `a_s j = W j xor W (j + s)` (`dw W s`).
If `f < f'` are consecutive `true` entries of `a_{d+m}` (with `0 ≤ m < e`) and `g < g'` are
consecutive `true` entries of `a_d` with `g ≤ f'`, then `(g - f) + (g' - f') ≤ e + m`.

The proof compares two readings of one period of `a_m`: the reading starting at `f`, and the
reading starting at `f + d`.  Both are windows of length `e` of the same periodic word, so they
have the same number of `true` entries and the same number of zero-runs of each length.  We use
the counting invariant "number of starts of a zero-run of length exactly `y`" (`Gap`).
-/

namespace RightShift

/-- `Gap F y j`: position `j` is `true`, the next `y` positions are `false`, and position
`j + y + 1` is `true` (a zero-run of length exactly `y` starts after `j`). -/
def Gap (F : ℤ → Bool) (y j : ℤ) : Prop :=
  F j = true ∧ (∀ k, j < k → k ≤ j + y → F k = false) ∧ F (j + y + 1) = true

open Classical in
/-- Indicator of `Gap F y j`. -/
noncomputable def gapInd (F : ℤ → Bool) (y j : ℤ) : ℕ := if Gap F y j then 1 else 0

lemma gap_shift (F : ℤ → Bool) (y j δ : ℤ) : Gap F y (j + δ) ↔ Gap (fun i => F (i + δ)) y j := by
  unfold Gap
  constructor
  · rintro ⟨h0, hz, h1⟩
    refine ⟨h0, fun k hk1 hk2 => hz (k + δ) (by omega) (by omega), ?_⟩
    show F (j + y + 1 + δ) = true
    rw [show j + y + 1 + δ = j + δ + y + 1 by ring]
    exact h1
  · rintro ⟨h0, hz, h1⟩
    refine ⟨h0, fun k hk1 hk2 => ?_, ?_⟩
    · have := hz (k - δ) (by omega) (by omega)
      simp only [sub_add_cancel] at this
      exact this
    · have : F (j + y + 1 + δ) = true := h1
      rw [show j + y + 1 + δ = j + δ + y + 1 by ring] at this
      exact this

lemma gapInd_shift (F : ℤ → Bool) (y j δ : ℤ) :
    gapInd F y (j + δ) = gapInd (fun i => F (i + δ)) y j := by
  unfold gapInd
  by_cases h : Gap F y (j + δ)
  · rw [ite_eq_left h, ite_eq_left ((gap_shift F y j δ).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((gap_shift F y j δ).mpr h'))]

lemma gapInd_period (F : ℤ → Bool) {e : ℤ} (hF : ∀ i, F (i + e) = F i) (y j : ℤ) :
    gapInd F y (j + e) = gapInd F y j := by
  rw [gapInd_shift]
  congr 1
  funext i
  exact hF i

lemma gapInd_of_false (F : ℤ → Bool) (y j : ℤ) (h : F j = false) : gapInd F y j = 0 := by
  unfold gapInd
  rw [ite_eq_right]
  rintro ⟨h0, -, -⟩
  rw [h] at h0
  exact absurd h0 (by decide)

/-- Transfer of gap starts along a block that ends with a `true` entry. -/
lemma gap_transfer (F G : ℤ → Bool) {y a b δ j : ℤ} (hy : 0 ≤ y)
    (hrel : ∀ i, a ≤ i → i ≤ b → F i = G (i + δ)) (hb : F b = true) (hj : a ≤ j) (hjb : j < b) :
    Gap F y j ↔ Gap G y (j + δ) := by
  have hb' : G (b + δ) = true := by rw [← hrel b (by omega) le_rfl]; exact hb
  constructor
  · rintro ⟨h0, hz, h1⟩
    have hle : j + y + 1 ≤ b := by
      by_contra hc
      have := hz b (by omega) (by omega)
      rw [hb] at this
      exact absurd this (by decide)
    refine ⟨?_, fun k hk1 hk2 => ?_, ?_⟩
    · rw [← hrel j hj (by omega)]; exact h0
    · have := hrel (k - δ) (by omega) (by omega)
      rw [sub_add_cancel] at this
      rw [← this]
      exact hz _ (by omega) (by omega)
    · rw [show j + δ + y + 1 = (j + y + 1) + δ by ring, ← hrel _ (by omega) hle]
      exact h1
  · rintro ⟨h0, hz, h1⟩
    have hle : j + y + 1 ≤ b := by
      by_contra hc
      have := hz (b + δ) (by omega) (by omega)
      rw [hb'] at this
      exact absurd this (by decide)
    refine ⟨?_, fun k hk1 hk2 => ?_, ?_⟩
    · rw [hrel j hj (by omega)]; exact h0
    · rw [hrel k (by omega) (by omega)]
      exact hz _ (by omega) (by omega)
    · rw [hrel _ (by omega) hle, show j + y + 1 + δ = j + δ + y + 1 by ring]
      exact h1

lemma cnt_gap_transfer (F G : ℤ → Bool) {y a b δ : ℤ} (hy : 0 ≤ y)
    (hrel : ∀ i, a ≤ i → i ≤ b → F i = G (i + δ)) (hb : F b = true) :
    cntI (gapInd F y) a b = cntI (gapInd G y) (a + δ) (b + δ) := by
  refine cntI_shift _ _ δ (fun i hi1 hi2 => ?_)
  have hiff := gap_transfer F G hy hrel hb hi1 hi2
  unfold gapInd
  by_cases h : Gap F y i
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

lemma cnt_wt_transfer (F G : ℤ → Bool) {a b δ : ℤ}
    (hrel : ∀ i, a ≤ i → i < b → F i = G (i + δ)) :
    cntI (fun j => (F j).toNat) a b = cntI (fun j => (G j).toNat) (a + δ) (b + δ) :=
  cntI_shift _ _ δ (fun i hi1 hi2 => by rw [hrel i hi1 hi2])

lemma cnt_gap_zero (F : ℤ → Bool) (y : ℤ) {a b : ℤ} (h : ∀ i, a ≤ i → i < b → F i = false) :
    cntI (gapInd F y) a b = 0 :=
  cntI_zero _ (fun i h1 h2 => gapInd_of_false F y i (h i h1 h2))

lemma cnt_wt_zero (F : ℤ → Bool) {a b : ℤ} (h : ∀ i, a ≤ i → i < b → F i = false) :
    cntI (fun j => (F j).toNat) a b = 0 :=
  cntI_zero _ (fun i h1 h2 => by rw [h i h1 h2]; rfl)

/-- Identity (β): `a_m j = a_{d+m} j xor a_d (j + m)`. -/
lemma dw_beta (W : ℤ → Bool) (d m j : ℤ) : dw W m j = xor (dw W (d + m) j) (dw W d (j + m)) := by
  unfold dw
  rw [show j + m + d = j + (d + m) by ring]
  cases W j <;> cases W (j + m) <;> cases W (j + (d + m)) <;> rfl

/-- Identity (α): `a_m (j + d) = a_{d+m} j xor a_d j`. -/
lemma dw_alpha (W : ℤ → Bool) (d m j : ℤ) :
    dw W m (j + d) = xor (dw W (d + m) j) (dw W d j) := by
  unfold dw
  rw [show j + d + m = j + (d + m) by ring]
  cases W j <;> cases W (j + d) <;> cases W (j + (d + m)) <;> rfl

theorem run_lemma (W : ℤ → Bool) {e : ℤ} (he : 0 < e) (hW : ∀ j, W (j + e) = W j)
    (d m f f' g g' : ℤ) (hm0 : 0 ≤ m) (hme : m < e)
    (hff : f < f') (hf : dw W (d + m) f = true) (hf' : dw W (d + m) f' = true)
    (hfz : ∀ j, f < j → j < f' → dw W (d + m) j = false)
    (_hgg : g < g') (hg : dw W d g = true) (hg' : dw W d g' = true)
    (hgz : ∀ j, g < j → j < g' → dw W d j = false)
    (hgf : g ≤ f') : (g - f) + (g' - f') ≤ e + m := by
  -- periodic copies
  have hpc : ∀ s j, dw W s (j + e) = dw W s j := fun s j => dw_period W hW s j
  have hpc' : ∀ s j, dw W s (j - e) = dw W s j := fun s j => by
    rw [← hpc s (j - e), sub_add_cancel]
  -- parity: consecutive breaks are less than `e` apart
  have hfe : f' - f ≤ e - 1 := by
    by_contra hc
    obtain ⟨q, hq1, hq2, hq⟩ := dw_next W he hW (d + m) f hf
    rw [hfz q hq1 (by omega)] at hq
    exact absurd hq (by decide)
  have hge : g' - g ≤ e - 1 := by
    by_contra hc
    obtain ⟨q, hq1, hq2, hq⟩ := dw_next W he hW d g hg
    rw [hgz q hq1 (by omega)] at hq
    exact absurd hq (by decide)
  -- generic "not strictly between" facts
  have notin_f : ∀ x, dw W (d + m) x = true → ¬ (f < x ∧ x < f') := by
    rintro x hx ⟨h1, h2⟩
    rw [hfz x h1 h2] at hx
    exact absurd hx (by decide)
  have notin_g : ∀ x, dw W d x = true → ¬ (g < x ∧ x < g') := by
    rintro x hx ⟨h1, h2⟩
    rw [hgz x h1 h2] at hx
    exact absurd hx (by decide)
  -- zero regions, including the copy of `(g, g')` shifted by `-e`
  have zf : ∀ j, f < j → j < f' → dw W (d + m) j = false := hfz
  have zg : ∀ j, g < j → j < g' → dw W d j = false := hgz
  have zg' : ∀ j, g - e < j → j < g' - e → dw W d j = false := by
    intro j h1 h2
    rw [← hpc d j]
    exact hgz _ (by omega) (by omega)
  have hge' : dw W d (g' - e) = true := by rw [hpc']; exact hg'
  have hfe' : dw W (d + m) (f + e) = true := by rw [hpc]; exact hf
  rcases Nat.lt_or_ge 0 m.toNat with hm | hm
  swap
  · -- the case `m = 0`
    have hm' : m = 0 := by omega
    subst hm'
    simp only [add_zero] at hf hf' hfz notin_f hfe'
    have n1 := notin_g f hf
    have n2 := notin_g f' hf'
    have n3 := notin_f g hg
    have n4 := notin_f g' hg'
    have n5 := notin_g (f + e) hfe'
    omega
  · -- the case `m ≥ 1`
    have hm1 : 1 ≤ m := by omega
    by_contra H
    push Not at H
    -- position facts
    have p1 : f + m + 2 ≤ g := by omega
    have p2 : f' + m + 2 ≤ g' := by omega
    have p3 : f + m + 1 + (f' - g) ≤ g' - e := by omega
    -- the two readings
    set am := dw W m with ham
    set ac := dw W (d + m) with hac
    set ad := dw W d with had
    have beta : ∀ j, am j = xor (ac j) (ad (j + m)) := fun j => dw_beta W d m j
    have alpha : ∀ j, am (j + d) = xor (ac j) (ad j) := fun j => dw_alpha W d m j
    have amper : ∀ j, am (j + e) = am j := fun j => hpc m j
    let F3 : ℤ → Bool := fun j => am (j + d)
    have F3per : ∀ j, F3 (j + e) = F3 j := by
      intro j
      show am (j + e + d) = am (j + d)
      rw [show j + e + d = j + d + e by ring, amper]
    -- common values
    have v_amf : am f = true := by
      rw [beta, hf, zg' (f + m) (by omega) (by omega)]; rfl
    have v_F3f : F3 f = true := by
      show am (f + d) = true
      rw [alpha, hf, zg' f (by omega) (by omega)]; rfl
    have z_am1 : ∀ j, f < j → j < g' - e - m → am j = false := by
      intro j h1 h2
      rw [beta, zf j h1 (by omega), zg' (j + m) (by omega) (by omega)]; rfl
    have z_F3a : ∀ j, f < j → j < g' - e → F3 j = false := by
      intro j h1 h2
      show am (j + d) = false
      rw [alpha, zf j h1 (by omega), zg' j (by omega) (by omega)]; rfl
    have rel1 : ∀ i, g' - e - m ≤ i → i < g - m → am i = F3 (i + m) := by
      intro i h1 h2
      show am i = am (i + m + d)
      rw [beta, alpha, zf i (by omega) (by omega), zf (i + m) (by omega) (by omega)]
    have rel2 : ∀ i, f' < i → i ≤ f + e → am i = F3 i := by
      intro i h1 h2
      show am i = am (i + d)
      rw [beta, alpha, zg i (by omega) (by omega), zg (i + m) (by omega) (by omega)]
    have v_amfe : am (f + e) = true := by rw [amper]; exact v_amf
    rcases eq_or_lt_of_le hgf with hgf' | hgf'
    · -- Step 2: `g = f'`; the two readings have different weights
      subst hgf'
      have v_amgm : am (g - m) = true := by
        rw [beta, zf (g - m) (by omega) (by omega), sub_add_cancel, hg]; rfl
      have z_am2 : ∀ j, g - m < j → j < g → am j = false := by
        intro j h1 h2
        rw [beta, zf j (by omega) h2, zg (j + m) (by omega) (by omega)]; rfl
      have v_amg : am g = true := by
        rw [beta, hf', zg (g + m) (by omega) (by omega)]; rfl
      have v_F3g : F3 g = false := by
        show am (g + d) = false
        rw [alpha, hf', hg]; rfl
      have rel2' : ∀ i, g + 1 ≤ i → i < f + e → am i = F3 (i + 0) := by
        intro i h1 h2
        rw [add_zero]
        exact rel2 i (by omega) h2.le
      -- weight of reading 1
      have w1 : cntI (fun j => (am j).toNat) f (f + e)
          = 3 + cntI (fun j => (am j).toNat) (g' - e - m) (g - m)
            + cntI (fun j => (am j).toNat) (g + 1) (f + e) := by
        rw [cntI_split _ (show f ≤ f + 1 by omega) (show f + 1 ≤ f + e by omega),
          cntI_split _ (show f + 1 ≤ g' - e - m by omega) (show g' - e - m ≤ f + e by omega),
          cntI_split _ (show g' - e - m ≤ g - m by omega) (show g - m ≤ f + e by omega),
          cntI_split _ (show g - m ≤ g - m + 1 by omega) (show g - m + 1 ≤ f + e by omega),
          cntI_split _ (show g - m + 1 ≤ g by omega) (show g ≤ f + e by omega),
          cntI_split _ (show g ≤ g + 1 by omega) (show g + 1 ≤ f + e by omega),
          cntI_single, cntI_single, cntI_single, v_amf, v_amgm, v_amg,
          cnt_wt_zero _ (fun i h1 h2 => z_am1 i (by omega) h2),
          cnt_wt_zero _ (fun i h1 h2 => z_am2 i (by omega) h2)]
        simp only [Bool.toNat_true]
        omega
      have w3 : cntI (fun j => (F3 j).toNat) f (f + e)
          = 1 + cntI (fun j => (F3 j).toNat) (g' - e) g
            + cntI (fun j => (F3 j).toNat) (g + 1) (f + e) := by
        rw [cntI_split _ (show f ≤ f + 1 by omega) (show f + 1 ≤ f + e by omega),
          cntI_split _ (show f + 1 ≤ g' - e by omega) (show g' - e ≤ f + e by omega),
          cntI_split _ (show g' - e ≤ g by omega) (show g ≤ f + e by omega),
          cntI_split _ (show g ≤ g + 1 by omega) (show g + 1 ≤ f + e by omega),
          cntI_single, cntI_single, v_F3f, v_F3g,
          cnt_wt_zero _ (fun i h1 h2 => z_F3a i (by omega) h2)]
        simp only [Bool.toNat_true, Bool.toNat_false]
        omega
      have t1 : cntI (fun j => (am j).toNat) (g' - e - m) (g - m)
          = cntI (fun j => (F3 j).toNat) (g' - e) g := by
        have := cnt_wt_transfer am F3 (a := g' - e - m) (b := g - m) (δ := m) rel1
        rw [this, sub_add_cancel, sub_add_cancel]
      have t2 : cntI (fun j => (am j).toNat) (g + 1) (f + e)
          = cntI (fun j => (F3 j).toNat) (g + 1) (f + e) := by
        have := cnt_wt_transfer am F3 (a := g + 1) (b := f + e) (δ := 0) rel2'
        rw [this, add_zero, add_zero]
      have heq : cntI (fun j => (F3 j).toNat) f (f + e) = cntI (fun j => (am j).toNat) f (f + e) := by
        have h1 := cnt_wt_transfer F3 am (a := f) (b := f + e) (δ := d) (fun i _ _ => rfl)
        rw [h1, show f + e + d = f + d + e by ring]
        exact cntI_period _ he.le (fun i => by simp only [amper]) _ _
      omega
    · -- Step 3: `g < f'`; compare the numbers of zero-runs of length `y`
      set y := g' - e - m - f - 1 with hy
      have hy0 : 0 ≤ y := by omega
      have v_amy : am (f + y + 1) = true := by
        rw [show f + y + 1 = g' - e - m by omega, beta, zf _ (by omega) (by omega),
          sub_add_cancel, hge']; rfl
      have gap1 : Gap am y f :=
        ⟨v_amf, fun k h1 h2 => z_am1 k h1 (by omega), v_amy⟩
      have v_amgm : am (g - m) = true := by
        rw [beta, zf (g - m) (by omega) (by omega), sub_add_cancel, hg]; rfl
      have v_F3f' : F3 f' = true := by
        show am (f' + d) = true
        rw [alpha, hf', zg f' (by omega) (by omega)]; rfl
      have z_F3b : ∀ j, g < j → j < f' → F3 j = false := by
        intro j h1 h2
        show am (j + d) = false
        rw [alpha, zf j (by omega) h2, zg j h1 (by omega)]; rfl
      have nogap3 : gapInd F3 y f = 0 := by
        unfold gapInd
        rw [ite_eq_right]
        rintro ⟨-, -, h⟩
        rw [z_F3a _ (by omega) (by omega)] at h
        exact absurd h (by decide)
      have rel1' : ∀ i, g' - e - m ≤ i → i ≤ g - m → am i = F3 (i + m) := by
        intro i h1 h2
        show am i = am (i + m + d)
        rw [beta, alpha, zf i (by omega) (by omega), zf (i + m) (by omega) (by omega)]
      have rel2' : ∀ i, f' ≤ i → i ≤ f + e → am i = F3 (i + 0) := by
        intro i h1 h2
        rw [add_zero]
        rcases eq_or_lt_of_le h1 with h | h
        · subst h
          rw [v_F3f']
          rw [beta, hf', zg (f' + m) (by omega) (by omega)]; rfl
        · exact rel2 i h h2
      have n1 : cntI (gapInd am y) f (f + e)
          ≥ 1 + cntI (gapInd am y) (g' - e - m) (g - m) + cntI (gapInd am y) f' (f + e) := by
        rw [cntI_split _ (show f ≤ f + 1 by omega) (show f + 1 ≤ f + e by omega),
          cntI_split _ (show f + 1 ≤ g' - e - m by omega) (show g' - e - m ≤ f + e by omega),
          cntI_split _ (show g' - e - m ≤ g - m by omega) (show g - m ≤ f + e by omega),
          cntI_split _ (show g - m ≤ f' by omega) (show f' ≤ f + e by omega),
          cntI_single]
        have : gapInd am y f = 1 := by unfold gapInd; rw [ite_eq_left gap1]
        omega
      have n3 : cntI (gapInd F3 y) f (f + e)
          = gapInd F3 y g + cntI (gapInd F3 y) (g' - e) g + cntI (gapInd F3 y) f' (f + e) := by
        rw [cntI_split _ (show f ≤ f + 1 by omega) (show f + 1 ≤ f + e by omega),
          cntI_split _ (show f + 1 ≤ g' - e by omega) (show g' - e ≤ f + e by omega),
          cntI_split _ (show g' - e ≤ g by omega) (show g ≤ f + e by omega),
          cntI_split _ (show g ≤ g + 1 by omega) (show g + 1 ≤ f + e by omega),
          cntI_split _ (show g + 1 ≤ f' by omega) (show f' ≤ f + e by omega),
          cntI_single, cntI_single, nogap3,
          cnt_gap_zero _ _ (fun i h1 h2 => z_F3a i (by omega) h2),
          cnt_gap_zero _ _ (fun i h1 h2 => z_F3b i (by omega) h2)]
        omega
      have t1 : cntI (gapInd am y) (g' - e - m) (g - m) = cntI (gapInd F3 y) (g' - e) g := by
        have := cnt_gap_transfer am F3 hy0 rel1' v_amgm
        rw [this, sub_add_cancel, sub_add_cancel]
      have t2 : cntI (gapInd am y) f' (f + e) = cntI (gapInd F3 y) f' (f + e) := by
        have := cnt_gap_transfer am F3 hy0 rel2' v_amfe
        rw [this, add_zero, add_zero]
      have heq : cntI (gapInd F3 y) f (f + e) = cntI (gapInd am y) f (f + e) := by
        have h1 := cntI_shift (gapInd F3 y) (gapInd am y) (a := f) (b := f + e) d
          (fun i _ _ => (gapInd_shift am y i d).symm)
        rw [h1, show f + e + d = f + d + e by ring]
        exact cntI_period _ he.le (fun i => gapInd_period am amper y i) _ _
      have hg3 : gapInd F3 y g = 1 := by
        have := gapInd F3 y g
        unfold gapInd at *
        by_cases h : Gap F3 y g
        · rw [ite_eq_left h]
        · rw [ite_eq_right h] at n3; omega
      have hgap3 : Gap F3 y g := by
        unfold gapInd at hg3
        by_contra h
        rw [ite_eq_right h] at hg3
        exact absurd hg3 (by decide)
      obtain ⟨-, hz3, h13⟩ := hgap3
      have c1 : ¬ (g + y + 1 < f') := by
        intro h
        rw [z_F3b _ (by omega) h] at h13
        exact absurd h13 (by decide)
      have c2 : ¬ (f' ≤ g + y) := by
        intro h
        have := hz3 f' (by omega) h
        rw [v_F3f'] at this
        exact absurd this (by decide)
      omega

end RightShift

#print axioms RightShift.run_lemma
```

### `RightShiftCore.lean`

```lean
import RightShiftRun
import Mathlib.Tactic.Linarith

/-!
# The core argument on the bi-infinite word

`Config X n c d t e β ε` collects the facts about the `n`-periodic bi-infinite word `X`
(the periodic extension of `s ∈ B(n, c, d)` with `d = n - c`) that the proof uses:

* `X` has period `d` on `A₀ = [-t, n - 2]`, with breaks at both ends (`t = add(s)`);
* no window of length `d + e` inside `A₀` has period `e` (when `e < d`), a consequence of the
  primitivity of the first `d` letters;
* `X` has period `e` on `B = [β, ε]` with breaks at both ends, and `|B| ≥ c + e + t`.

The conclusion is `ε ≡ c - 2 (mod n)`, which is equivalent to `b = d₂`.
-/

namespace RightShift

structure Config (X : ℤ → Bool) (n c d t e β ε : ℤ) : Prop where
  hn : n = c + d
  hdc : d ≤ c
  hd1 : 1 ≤ d
  he1 : 1 ≤ e
  hed : e ≤ d
  ht : 0 ≤ t
  per : ∀ i, X (i + n) = X i
  runA : ∀ i, -t ≤ i → i + d ≤ n - 2 → X i = X (i + d)
  brAr : X (n - 1) ≠ X (n - 1 - d)
  brAl : X (-t - 1) ≠ X (-t - 1 + d)
  fw : e < d → ∀ a, -t ≤ a → a + d + e - 1 ≤ n - 2 →
    ¬ (∀ i, a ≤ i → i + e ≤ a + d + e - 1 → X i = X (i + e))
  runB : ∀ i, β ≤ i → i + e ≤ ε → X i = X (i + e)
  brBr : X (ε + 1) ≠ X (ε + 1 - e)
  brBl : X (β - 1) ≠ X (β - 1 + e)
  len : c + e + t ≤ ε - β + 1

section

variable {X : ℤ → Bool} {n c d t e β ε : ℤ}

lemma Config.per' (H : Config X n c d t e β ε) (i j : ℤ) (h : j = i + n) : X j = X i := by
  rw [h]; exact H.per i

lemma Config.perMul (H : Config X n c d t e β ε) (i q : ℤ) : X (i + n * q) = X i := by
  induction q using Int.induction_on with
  | zero => simp
  | succ k ih => rw [show i + n * (k + 1) = i + n * k + n by ring, H.per, ih]
  | pred k ih =>
    rw [← ih, show i + n * -(k : ℤ) = i + n * (-(k : ℤ) - 1) + n by ring, H.per]

lemma Config.perMul' (H : Config X n c d t e β ε) (i j q : ℤ) (h : j = i + n * q) :
    X j = X i := by
  rw [h]; exact H.perMul i q

lemma Config.runA' (H : Config X n c d t e β ε) (i j : ℤ) (h1 : -t ≤ i) (h2 : j = i + d)
    (h3 : j ≤ n - 2) : X i = X j := by
  rw [h2]; exact H.runA i h1 (by omega)

lemma Config.runB' (H : Config X n c d t e β ε) (i j : ℤ) (h1 : β ≤ i) (h2 : j = i + e)
    (h3 : j ≤ ε) : X i = X j := by
  rw [h2]; exact H.runB i h1 (by omega)

/-- Translating `B` by a multiple of `n`. -/
lemma Config.translate (H : Config X n c d t e β ε) (q : ℤ) :
    Config X n c d t e (β + n * q) (ε + n * q) where
  hn := H.hn
  hdc := H.hdc
  hd1 := H.hd1
  he1 := H.he1
  hed := H.hed
  ht := H.ht
  per := H.per
  runA := H.runA
  brAr := H.brAr
  brAl := H.brAl
  fw := H.fw
  runB := by
    intro i h1 h2
    have := H.runB (i - n * q) (by omega) (by omega)
    rw [← H.perMul (i - n * q) q, ← H.perMul (i - n * q + e) q] at this
    rw [show i - n * q + n * q = i by ring, show i - n * q + e + n * q = i + e by ring] at this
    exact this
  brBr := by
    rw [H.perMul' (ε + 1) (ε + n * q + 1) q (by ring),
      H.perMul' (ε + 1 - e) (ε + n * q + 1 - e) q (by ring)]
    exact H.brBr
  brBl := by
    rw [H.perMul' (β - 1) (β + n * q - 1) q (by ring),
      H.perMul' (β - 1 + e) (β + n * q - 1 + e) q (by ring)]
    exact H.brBl
  len := by have := H.len; omega

/-- The reversal symmetry `i ↦ 2n - 2 - t - i`. -/
lemma Config.reflect (H : Config X n c d t e β ε) :
    Config (fun i => X (2 * n - 2 - t - i)) n c d t e (2 * n - 2 - t - ε) (2 * n - 2 - t - β) where
  hn := H.hn
  hdc := H.hdc
  hd1 := H.hd1
  he1 := H.he1
  hed := H.hed
  ht := H.ht
  per := by
    intro i
    exact (H.per' _ _ (by ring)).symm
  runA := by
    intro i h1 h2
    show X (2 * n - 2 - t - i) = X (2 * n - 2 - t - (i + d))
    have hn := H.hn
    rw [H.per' (n - 2 - t - i) (2 * n - 2 - t - i) (by ring),
      H.per' (n - 2 - t - i - d) (2 * n - 2 - t - (i + d)) (by ring)]
    exact (H.runA' (n - 2 - t - i - d) (n - 2 - t - i) (by omega) (by ring) (by omega)).symm
  brAr := by
    show X (2 * n - 2 - t - (n - 1)) ≠ X (2 * n - 2 - t - (n - 1 - d))
    rw [H.per' (-t - 1) (2 * n - 2 - t - (n - 1)) (by ring),
      H.per' (-t - 1 + d) (2 * n - 2 - t - (n - 1 - d)) (by ring)]
    exact H.brAl
  brAl := by
    show X (2 * n - 2 - t - (-t - 1)) ≠ X (2 * n - 2 - t - (-t - 1 + d))
    rw [H.per' (n - 1) (2 * n - 2 - t - (-t - 1)) (by ring),
      H.per' (n - 1 - d) (2 * n - 2 - t - (-t - 1 + d)) (by ring)]
    exact H.brAr
  fw := by
    intro hed a h1 h2 hper
    have hn := H.hn
    apply H.fw hed (n - t - a - d - e - 1) (by omega) (by omega)
    intro i hi1 hi2
    have := hper (n - 2 - t - i - e) (by omega) (by omega)
    rw [H.per' (2 * n - 2 - t - (n - 2 - t - i - e) - n) (2 * n - 2 - t - (n - 2 - t - i - e))
      (by ring),
      H.per' (2 * n - 2 - t - (n - 2 - t - i - e + e) - n) (2 * n - 2 - t - (n - 2 - t - i - e + e))
      (by ring)] at this
    rw [show 2 * n - 2 - t - (n - 2 - t - i - e) - n = i + e by ring,
      show 2 * n - 2 - t - (n - 2 - t - i - e + e) - n = i by ring] at this
    exact this.symm
  runB := by
    intro i h1 h2
    show X (2 * n - 2 - t - i) = X (2 * n - 2 - t - (i + e))
    exact (H.runB' (2 * n - 2 - t - i - e) (2 * n - 2 - t - i) (by omega) (by ring)
      (by omega)).symm.trans (congrArg X (by ring))
  brBr := by
    show X (2 * n - 2 - t - (2 * n - 2 - t - β + 1)) ≠ X (2 * n - 2 - t - (2 * n - 2 - t - β + 1 - e))
    rw [show 2 * n - 2 - t - (2 * n - 2 - t - β + 1) = β - 1 by ring,
      show 2 * n - 2 - t - (2 * n - 2 - t - β + 1 - e) = β - 1 + e by ring]
    exact H.brBl
  brBl := by
    show X (2 * n - 2 - t - (2 * n - 2 - t - ε - 1)) ≠ X (2 * n - 2 - t - (2 * n - 2 - t - ε - 1 + e))
    rw [show 2 * n - 2 - t - (2 * n - 2 - t - ε - 1) = ε + 1 by ring,
      show 2 * n - 2 - t - (2 * n - 2 - t - ε - 1 + e) = ε + 1 - e by ring]
    exact H.brBr
  len := by have := H.len; omega

lemma xor_true_of_ne {a b : Bool} (h : a ≠ b) : xor a b = true := by
  cases a <;> cases b <;> simp_all

lemma xor_false_of_eq {a b : Bool} (h : a = b) : xor a b = false := by
  subst h; cases a <;> rfl

/-- On an `e`-periodic interval, `X` is determined by the residue modulo `e`. -/
lemma Config.runB_mod (H : Config X n c d t e β ε) :
    ∀ i, β ≤ i → i ≤ ε → X i = X (β + (i - β) % e) := by
  have he := H.he1
  have key : ∀ k : ℕ, ∀ i, i - β = k → i ≤ ε → X i = X (β + (i - β) % e) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hk hi
      by_cases hlt : i - β < e
      · rw [Int.emod_eq_of_lt (by omega) hlt, show β + (i - β) = i by ring]
      · have h1 := ih (k - e.toNat) (by omega) (i - e) (by omega) (by omega)
        have h2 := H.runB' (i - e) i (by omega) (by ring) hi
        rw [← h2, h1, show i - e - β = (i - β) + e * (-1) by ring, Int.add_mul_emod_self_left]
  intro i h1 h2
  exact key (i - β).toNat i (by omega) h2

/-- Position of the normalized run: `n - 1 ≤ ε ≤ 2n - 3` (uses the Fine–Wilf consequence `fw`). -/
lemma Config.bounds (H : Config X n c d t e β ε) (hed : e < d) (hβ1 : -t ≤ β) (hβ2 : β ≤ n - t - 1) :
    n - 1 ≤ ε ∧ ε ≤ 2 * n - 3 := by
  have hn := H.hn
  have hdc := H.hdc
  have he1 := H.he1
  have ht := H.ht
  have hlen := H.len
  constructor
  · by_contra hc
    exact H.fw hed β hβ1 (by omega) (fun i h1 h2 => H.runB i h1 (by omega))
  · by_contra hc
    apply H.fw hed (-t) le_rfl (by omega)
    intro i h1 h2
    rw [← H.per i, ← H.per (i + e), show i + e + n = i + n + e by ring]
    exact H.runB (i + n) (by omega) (by omega)

/-- Case (b) of the proof is impossible: the `e`-run meets `A₀` in fewer than `e` positions. -/
theorem Config.caseB (H : Config X n c d t e β ε) (hed : e < d) (hβ1 : -t ≤ β) (hβ2 : β ≤ n - t - 1)
    (hb : n - e ≤ β) : False := by
  obtain ⟨hε1, hε2⟩ := H.bounds hed hβ1 hβ2
  have hn := H.hn
  have hdc := H.hdc
  have he1 := H.he1
  have ht := H.ht
  have hlen := H.len
  have he0 : 0 < e := by omega
  -- the `e`-periodic word read off the run `B`
  let W : ℤ → Bool := fun j => X (β + (n + j - β) % e)
  have hWper : ∀ j, W (j + e) = W j := by
    intro j
    show X (β + (n + (j + e) - β) % e) = X (β + (n + j - β) % e)
    rw [show n + (j + e) - β = (n + j - β) + e * 1 by ring, Int.add_mul_emod_self_left]
  have hWX : ∀ j, β ≤ n + j → n + j ≤ ε → W j = X (n + j) := by
    intro j h1 h2
    show X (β + (n + j - β) % e) = X (n + j)
    exact (H.runB_mod (n + j) h1 h2).symm
  have hWmul : ∀ j q, W (j + e * q) = W j := by
    intro j q
    show X (β + (n + (j + e * q) - β) % e) = X (β + (n + j - β) % e)
    rw [show n + (j + e * q) - β = (n + j - β) + e * q by ring, Int.add_mul_emod_self_left]
  -- `m = (c - d) mod e`
  set m := (c - d) % e with hm
  have hm0 : 0 ≤ m := Int.emod_nonneg _ (by omega)
  have hme : m < e := Int.emod_lt_of_pos _ he0
  have hq0 : 0 ≤ (c - d) / e := Int.ediv_nonneg (by omega) (by omega)
  have hmd : c - d = m + e * ((c - d) / e) := by rw [hm, Int.emod_def]; ring
  have hmc : m ≤ c - d := by nlinarith
  have hWc : ∀ j, dw W c j = dw W (d + m) j := by
    intro j
    unfold dw
    rw [show j + c = j + (d + m) + e * ((c - d) / e) by linarith, hWmul]
  set κ := ε - n with hκ
  -- breaks of `a_d`
  have hg : dw W d (-t - 1) = true := by
    unfold dw
    rw [hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_true_of_ne
    rw [H.per' (-t - 1) (n + (-t - 1)) (by ring), H.per' (-t - 1 + d) (n + (-t - 1 + d)) (by ring)]
    exact H.brAl
  have hgz : ∀ j, -t - 1 < j → j < κ - d + 1 → dw W d j = false := by
    intro j h1 h2
    unfold dw
    rw [hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_false_of_eq
    rw [H.per' j (n + j) (by ring), H.per' (j + d) (n + (j + d)) (by ring)]
    exact H.runA j (by omega) (by omega)
  have hg' : dw W d (κ - d + 1) = true := by
    unfold dw
    rw [show κ - d + 1 + d = (ε + 1 - e - n) + e * 1 by ring, hWmul,
      hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_true_of_ne
    rw [show n + (κ - d + 1) = ε + 1 - d by ring, show n + (ε + 1 - e - n) = ε + 1 - e by ring]
    rw [H.per' (ε + 1 - d - n) (ε + 1 - d) (by ring)]
    rw [H.runA' (ε + 1 - d - n) (ε + 1 - n) (by omega) (by ring) (by omega)]
    rw [← H.per' (ε + 1 - n) (ε + 1) (by ring)]
    exact H.brBr
  -- breaks of `a_c`
  have hf' : dw W c (-1) = true := by
    unfold dw
    rw [hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_true_of_ne
    rw [show n + (-1) = n - 1 by ring, H.per' (n - 1 - d) (n + (-1 + c)) (by omega)]
    exact H.brAr
  have hfz : ∀ j, β - n - 1 < j → j < -1 → dw W c j = false := by
    intro j h1 h2
    unfold dw
    rw [hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_false_of_eq
    rw [← H.runA' (n + j - d) (n + j) (by omega) (by ring) (by omega)]
    exact (H.per' (n + j - d) (n + (j + c)) (by omega)).symm
  have hf : dw W c (β - n - 1) = true := by
    unfold dw
    rw [← hWper (β - n - 1), hWX _ (by omega) (by omega), hWX _ (by omega) (by omega)]
    apply xor_true_of_ne
    rw [show n + (β - n - 1 + e) = β - 1 + e by ring, show n + (β - n - 1 + c) = β - 1 + c by ring]
    rw [H.per' (β - 1 - d) (β - 1 + c) (by omega)]
    rw [H.runA' (β - 1 - d) (β - 1) (by omega) (by ring) (by omega)]
    exact H.brBl.symm
  rw [hWc] at hf hf'
  have hfz' : ∀ j, β - n - 1 < j → j < -1 → dw W (d + m) j = false := by
    intro j h1 h2
    rw [← hWc]
    exact hfz j h1 h2
  have := run_lemma W he0 hWper d m (β - n - 1) (-1) (-t - 1) (κ - d + 1) hm0 hme
    (by omega) hf hf' hfz' (by omega) hg hg' hgz (by omega)
  omega

/-- The main argument after normalizing `B` so that `-t ≤ β ≤ n - t - 1`. -/
theorem Config.normalized (H : Config X n c d t e β ε) (hβ1 : -t ≤ β) (hβ2 : β ≤ n - t - 1) :
    ε = n + c - 2 := by
  have hn := H.hn
  have hdc := H.hdc
  have hd1 := H.hd1
  have he1 := H.he1
  have hedl := H.hed
  have ht := H.ht
  have hlen := H.len
  rcases eq_or_lt_of_le hedl with hde | hde
  · -- the case `e = d`
    exfalso
    subst hde
    by_cases hP : β ≤ n - 1 - e
    · exact H.brAr (H.runB' (n - 1 - e) (n - 1) hP (by ring) (by omega)).symm
    · apply H.brAl
      rw [← H.per' (-t - 1) (n - t - 1) (by ring), ← H.per' (-t - 1 + e) (n - t - 1 + e) (by ring)]
      exact H.runB' (n - t - 1) (n - t - 1 + e) hβ2 rfl (by omega)
  -- from now on `e < d`
  obtain ⟨hP1, hP2⟩ := H.bounds hde hβ1 hβ2
  -- Claim U
  have hU : β ≤ n - 1 - e → ε ≤ n + c - 2 := by
    intro hP
    by_contra hc
    apply H.brAr
    rw [show n - 1 - d = c - 1 by omega]
    rw [← H.runB' (n - 1 - e) (n - 1) hP (by ring) (by omega)]
    rw [← H.runA' (c - 1 - e) (n - 1 - e) (by omega) (by omega) (by omega)]
    rw [← H.per' (c - 1 - e) (n + c - 1 - e) (by ring)]
    rw [H.runB' (n + c - 1 - e) (n + c - 1) (by omega) (by ring) (by omega)]
    exact H.per' (c - 1) (n + c - 1) (by ring)
  -- Claim L
  have hL : ε ≤ n + c - 3 → ε ≤ n + e - t - 2 := by
    intro hR
    by_contra hc
    apply H.brBr
    rw [H.per' (ε + 1 - n) (ε + 1) (by ring), H.per' (ε + 1 - e - n) (ε + 1 - e) (by ring)]
    rw [H.runA' (ε + 1 - n) (ε + 1 - c) (by omega) (by omega) (by omega)]
    rw [H.runA' (ε + 1 - e - n) (ε + 1 - e - c) (by omega) (by omega) (by omega)]
    exact (H.runB' (ε + 1 - e - c) (ε + 1 - c) (by omega) (by ring) (by omega)).symm
  -- Claim U*
  have hUs : n - t - 1 + e ≤ ε → d - t ≤ β := by
    intro hPs
    by_contra hc
    apply H.brAl
    rw [← H.per' (-t - 1) (n - t - 1) (by ring)]
    rw [H.runB' (n - t - 1) (n - t - 1 + e) hβ2 rfl hPs]
    rw [H.per' (e - t - 1) (n - t - 1 + e) (by ring)]
    rw [H.runA' (e - t - 1) (e - t - 1 + d) (by omega) rfl (by omega)]
    rw [show e - t - 1 + d = (-t - 1 + d) + e by ring]
    exact (H.runB' (-t - 1 + d) (-t - 1 + d + e) (by omega) rfl (by omega)).symm
  -- Claim L*
  have hLs : d - t + 1 ≤ β → n - e ≤ β := by
    intro hRs
    by_contra hc
    apply H.brBl
    rw [H.runA' (β - 1 - d) (β - 1) (by omega) (by ring) (by omega) |>.symm]
    rw [H.runA' (β - 1 + e - d) (β - 1 + e) (by omega) (by ring) (by omega) |>.symm]
    rw [← H.per' (β - 1 - d) (β - 1 + c) (by omega), ← H.per' (β - 1 + e - d) (β - 1 + c + e) (by omega)]
    exact H.runB' (β - 1 + c) (β - 1 + c + e) (by omega) rfl (by omega)
  -- case analysis
  by_cases hP : β ≤ n - 1 - e
  · by_cases hPs : n - t - 1 + e ≤ ε
    · -- case (a)
      have h1 := hU hP
      have h2 := hUs hPs
      by_contra hne
      have h3 := hL (by omega)
      rcases eq_or_lt_of_le h2 with h4 | h4
      · omega
      · have := hLs (by omega)
        omega
    · -- case (c): reflect and use case (b)
      exfalso
      have HR := H.reflect
      exact HR.caseB hde (by omega) (by omega) (by omega)
  · -- case (b)
    exact (H.caseB hde hβ1 hβ2 (by omega)).elim

/-- The main abstract theorem: `ε ≡ c - 2 (mod n)`. -/
theorem Config.main (H : Config X n c d t e β ε) : ∃ q : ℤ, ε = c - 2 + n * q := by
  have hn := H.hn
  have hd1 := H.hd1
  have hdc := H.hdc
  have hnpos : 0 < n := by omega
  set q := -((β + t) / n) with hq
  have HT := H.translate q
  have hr0 : 0 ≤ (β + t) % n := Int.emod_nonneg _ (by omega)
  have hr1 : (β + t) % n < n := Int.emod_lt_of_pos _ hnpos
  have hβ' : β + n * q = (β + t) % n - t := by rw [hq, Int.emod_def]; ring
  have := HT.normalized (by omega) (by omega)
  exact ⟨1 - q, by linarith⟩

end

end RightShift
```

### `RightShiftBridge.lean`

```lean
import RightShiftDefs
import RightShiftCore

/-!
# From finite words to the bi-infinite word

`ext w` is the periodic extension `w^∞` of `w : Fin n → Bool`, indexed by `ℤ`.  For
`w ∈ B(n, c, d)` (structural part) with `add(w) = t`, the extension has period `d` on
`[-t, c + d - 2]`, with breaks just outside both ends (`runData`).
-/

namespace RightShift

/-- The periodic extension of `w`, indexed by `ℤ`. -/
def ext {n : ℕ} (w : Fin n → Bool) (i : ℤ) : Bool := get w ((i % (n : ℤ)).toNat)

section
variable {n : ℕ} (w : Fin n → Bool)

lemma ext_per (i : ℤ) : ext w (i + n) = ext w i := by
  unfold ext
  rw [show i + (n : ℤ) = i + n * 1 by ring, Int.add_mul_emod_self_left]

lemma ext_mul (i q : ℤ) : ext w (i + n * q) = ext w i := by
  unfold ext
  rw [Int.add_mul_emod_self_left]

lemma ext_of_lt (k : ℕ) (hk : k < n) : ext w k = get w k := by
  unfold ext
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

lemma get_of_lt (k : ℕ) (hk : k < n) : get w k = w ⟨k, hk⟩ := by
  unfold get
  rw [dite_eq_left hk]

lemma get_rotR (b p : ℕ) (hp : p < n) :
    get (rotR n b w) p = if p < b then get w (n - b + p) else get w (p - b) := by
  rw [get_of_lt _ p hp]
  rfl

lemma ext_rotR (b : ℕ) (hb : b < n) (j : ℤ) : ext (rotR n b w) j = ext w (j + ((n : ℤ) - b)) := by
  have hn : (0 : ℤ) < n := by omega
  have hp0 : 0 ≤ j % n := Int.emod_nonneg _ (by omega)
  have hpn : j % n < n := Int.emod_lt_of_pos _ hn
  have hj : j = j % n + n * (j / n) := by rw [Int.emod_def]; ring
  unfold ext
  rw [get_rotR w b _ (by omega)]
  rw [show j + ((n : ℤ) - b) = (j % n + (n - b)) + n * (j / n) by
    conv_lhs => rw [hj]
    ring, Int.add_mul_emod_self_left]
  by_cases hlt : (j % n).toNat < b
  · have h := Int.emod_eq_of_lt (show 0 ≤ j % (n : ℤ) + ((n : ℤ) - b) by omega)
      (show j % (n : ℤ) + ((n : ℤ) - b) < n by omega)
    rw [ite_eq_left hlt, h]
    congr 1
    omega
  · have h := Int.emod_eq_of_lt (show 0 ≤ j % (n : ℤ) - b by omega)
      (show j % (n : ℤ) - b < n by omega)
    rw [ite_eq_right hlt, show j % n + (n - b) = (j % n - b) + n * 1 by ring,
      Int.add_mul_emod_self_left, h]
    congr 1
    omega

end

section
variable {n c d : ℕ} {w : Fin n → Bool}

lemma InBStruct.d_pos (hS : InBStruct n c d w) : 1 ≤ d := hS.2.1

lemma InBStruct.cd_le (hS : InBStruct n c d w) : c + d ≤ n := by
  obtain ⟨-, hd1, hd2, -⟩ := hS
  have := le_trans hd2 (min_le_left _ _)
  omega

/-- The block structure gives `s_j = s_{j mod d}` for `j ≤ c + d - 2`. -/
lemma InBStruct.blk (hS : InBStruct n c d w) (j : ℕ) (hj : j + 2 ≤ c + d) :
    get w j = get w (j % d) := by
  obtain ⟨-, hd1, -, -, h1, h2, -⟩ := hS
  have hQ : (c + d - 1) / d * d + (c + d - 1) % d = c + d - 1 := Nat.div_add_mod' _ _
  have hjd : j / d * d + j % d = j := Nat.div_add_mod' j d
  have hjm : j % d < d := Nat.mod_lt _ (by omega)
  have hmod : (c + d - 1) % d < d := Nat.mod_lt _ (by omega)
  by_cases hlt : j / d < (c + d - 1) / d
  · have := h1 (j / d) hlt (j % d) hjm
    rw [hjd] at this
    exact this
  · push Not at hlt
    have hQeq : j / d = (c + d - 1) / d := by
      by_contra hne
      have h3 : ((c + d - 1) / d + 1) * d ≤ j / d * d := Nat.mul_le_mul_right d (by omega)
      rw [Nat.add_mul, one_mul] at h3
      omega
    rw [hQeq] at hjd
    have := h2 (j % d) (by omega)
    rw [hjd] at this
    exact this

/-- The break: `s_{c+d-1} = s̄_r` with `r = (c + d - 1) mod d`. -/
lemma InBStruct.brk (hS : InBStruct n c d w) :
    get w (c + d - 1) = !(get w ((c + d - 1) % d)) := by
  obtain ⟨-, hd1, -, -, -, -, h3⟩ := hS
  have hQ : (c + d - 1) / d * d + (c + d - 1) % d = c + d - 1 := Nat.div_add_mod' _ _
  rw [show (c + d - 1) / d * d + ((c + d - 1) - (c + d - 1) / d * d) = c + d - 1 by omega,
    show (c + d - 1) - (c + d - 1) / d * d = (c + d - 1) % d by omega] at h3
  exact h3

lemma toNat_emod_natCast (k d : ℕ) : (((k : ℤ) % (d : ℤ)).toNat) = k % d := by
  rw [← Int.natCast_emod, Int.toNat_natCast]

/-- On `[-t, c + d - 2]` the extension agrees with the `d`-periodic word built on `s_d`. -/
lemma ext_eq_mod (hS : InBStruct n c d w) {t : ℕ} (hA : IsAdd n d w t) (i : ℤ)
    (h1 : -(t : ℤ) ≤ i) (h2 : i ≤ (c : ℤ) + d - 2) : ext w i = get w ((i % (d : ℤ)).toNat) := by
  have hcd := hS.cd_le
  have hd1 := hS.d_pos
  have htn := hA.1
  rcases le_or_gt 0 i with h0 | h0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [ext_of_lt w k (by omega), hS.blk k (by omega), toNat_emod_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, i = -1 - m := ⟨(-1 - i).toNat, by omega⟩
    have hmt : m < t := by omega
    have := hA.2.1 m hmt
    rw [← ext_per, show i + n = ((n - 1 - m : ℕ) : ℤ) by omega, ext_of_lt w _ (by omega), this]
    congr 2
    rw [hm, show (d : ℤ) - 1 - m = (-1 - m) + d * 1 by ring, Int.add_mul_emod_self_left]

/-- The run data of a word in `B(n, c, d)` with `add = t`. -/
theorem runData (hS : InBStruct n c d w) (hc1 : 1 ≤ c) {t : ℕ} (hA : IsAdd n d w t) :
    (∀ i : ℤ, -(t : ℤ) ≤ i → i + d ≤ (c : ℤ) + d - 2 → ext w i = ext w (i + d)) ∧
    ext w ((c : ℤ) + d - 1) ≠ ext w ((c : ℤ) - 1) ∧
    ext w (-(t : ℤ) - 1) ≠ ext w (-(t : ℤ) - 1 + d) := by
  have hcd := hS.cd_le
  have hd1 := hS.d_pos
  have htn := hA.1
  refine ⟨?_, ?_, ?_⟩
  · intro i h1 h2
    rw [ext_eq_mod hS hA i h1 (by omega), ext_eq_mod hS hA (i + d) (by omega) h2,
      show i + (d : ℤ) = i + d * 1 by ring, Int.add_mul_emod_self_left]
  · rw [ext_eq_mod hS hA ((c : ℤ) - 1) (by omega) (by omega), show (c : ℤ) + d - 1 = ((c + d - 1 : ℕ) : ℤ) by omega,
      ext_of_lt w _ (by omega), hS.brk, show (c : ℤ) - 1 = ((c - 1 : ℕ) : ℤ) by omega,
      toNat_emod_natCast, show c + d - 1 = (c - 1) + d by omega, Nat.add_mod_right]
    cases get w ((c - 1) % d) <;> decide
  · rw [ext_eq_mod hS hA (-(t : ℤ) - 1 + d) (by omega) (by omega), ← ext_per,
      show -(t : ℤ) - 1 + n = ((n - 1 - t : ℕ) : ℤ) by omega, ext_of_lt w _ (by omega),
      show -(t : ℤ) - 1 + d = (d : ℤ) - 1 - t by ring]
    exact hA.2.2

end

end RightShift
```

### `RightShiftFineWilf.lean`

```lean
import RightShiftBridge

/-!
# Weak Fine–Wilf and the primitivity step

If an interval of length at least `p + q` has periods `p` and `q`, it has period `gcd(p, q)`.
Consequence (`fw_of`): inside the `d`-run `[-t, c + d - 2]` of `w ∈ B(n, c, d)`, no window of
length `d + e` (`0 < e < d`) has period `e`; otherwise the prefix `s_d` would be a repetition of
a block of length `gcd(d, e)`, a proper divisor of `d`, contradicting aperiodicity.
-/

namespace RightShift

/-- `X` has period `p` on the integer interval `[a, b]`. -/
def PerOn (X : ℤ → Bool) (p a b : ℤ) : Prop := ∀ i, a ≤ i → i + p ≤ b → X i = X (i + p)

lemma perOn_sub (X : ℤ → Bool) {a b p q : ℤ} (_hp : 0 < p) (hpq : p < q) (hlen : p + q ≤ b - a + 1)
    (hP : PerOn X p a b) (hQ : PerOn X q a b) : PerOn X (q - p) a b := by
  intro i h1 h2
  by_cases hiq : i + q ≤ b
  · rw [hQ i h1 hiq, hP (i + (q - p)) (by omega) (by omega)]
    congr 1
    ring
  · have e1 := hP (i - p) (by omega) (by omega)
    have e2 := hQ (i - p) (by omega) (by omega)
    rw [show i - p + p = i by ring] at e1
    rw [show i - p + q = i + (q - p) by ring] at e2
    rw [← e1, e2]

theorem fine_wilf (X : ℤ → Bool) (a b : ℤ) :
    ∀ N : ℕ, ∀ p q : ℕ, p + q = N → 0 < p → 0 < q → ((p : ℤ) + q ≤ b - a + 1) →
      PerOn X p a b → PerOn X q a b → PerOn X (Nat.gcd p q) a b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p q hN hp hq hlen hP hQ
    rcases lt_trichotomy p q with h | h | h
    · have hsub := perOn_sub X (show (0 : ℤ) < p by omega) (show (p : ℤ) < q by omega) hlen hP hQ
      rw [show (q : ℤ) - p = ((q - p : ℕ) : ℤ) by omega] at hsub
      have := ih q (by omega) p (q - p) (by omega) hp (by omega) (by omega) hP hsub
      rwa [Nat.gcd_sub_self_right h.le] at this
    · subst h
      rwa [Nat.gcd_self]
    · have hsub := perOn_sub X (show (0 : ℤ) < q by omega) (show (q : ℤ) < p by omega)
        (by omega) hQ hP
      rw [show (p : ℤ) - q = ((p - q : ℕ) : ℤ) by omega] at hsub
      have := ih p (by omega) (p - q) q (by omega) (by omega) hq (by omega) hsub hQ
      rwa [Nat.gcd_sub_self_left h.le] at this

lemma get_pre {n : ℕ} (d : ℕ) (w : Fin n → Bool) (k : ℕ) (hk : k < d) :
    get (pre d w) k = get w k := by
  rw [get_of_lt _ k hk]
  rfl

/-- A cyclic word of length `d` invariant under rotation by `g ∣ d` is a repetition of its first
`g` letters. -/
lemma rep_of_cyclic {n : ℕ} (w : Fin n → Bool) {d g : ℕ} (_hgd : g ≤ d) (hg : 0 < g)
    (hcyc : ∀ k < d, get w k = get w ((k + g) % d)) : ∀ k < d, get w k = get w (k % g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkg : k < g
    · rw [Nat.mod_eq_of_lt hkg]
    · have h1 := hcyc (k - g) (by omega)
      rw [show k - g + g = k by omega, Nat.mod_eq_of_lt hk] at h1
      rw [← h1, ih (k - g) (by omega) (by omega), ← Nat.mod_eq_sub_mod (by omega)]

/-- The primitivity step. -/
theorem fw_of {n c d : ℕ} {w : Fin n → Bool} (hS : InBStruct n c d w) {t : ℕ} (hA : IsAdd n d w t)
    (hc1 : 1 ≤ c) (e : ℕ) (he : 0 < e) (hed : e < d) (a : ℤ) (ha : -(t : ℤ) ≤ a)
    (hae : a + d + e - 1 ≤ (c : ℤ) + d - 2)
    (hper : ∀ i, a ≤ i → i + e ≤ a + d + e - 1 → ext w i = ext w (i + e)) : False := by
  have hap := hS.2.2.2.1
  have hd1 := hS.d_pos
  have hRD := runData hS hc1 hA
  have hPd : PerOn (ext w) d a (a + d + e - 1) :=
    fun i h1 h2 => hRD.1 i (by omega) (by omega)
  have hPe : PerOn (ext w) e a (a + d + e - 1) := hper
  have hPg := fine_wilf (ext w) a (a + d + e - 1) (d + e) d e rfl (by omega) he (by omega) hPd hPe
  set g := Nat.gcd d e with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hge : g ≤ e := Nat.gcd_le_right _ he
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  -- cyclic invariance of the prefix under rotation by `g`
  have hcyc : ∀ k < d, get w k = get w ((k + g) % d) := by
    intro k hk
    set j : ℤ := a + ((k : ℤ) - a) % d with hj
    have hj0 : 0 ≤ ((k : ℤ) - a) % d := Int.emod_nonneg _ (by omega)
    have hj1 : ((k : ℤ) - a) % d < d := Int.emod_lt_of_pos _ (by omega)
    have hjk : j = k + d * (-(((k : ℤ) - a) / d)) := by rw [hj, Int.emod_def]; ring
    have e1 := ext_eq_mod hS hA j (by omega) (by omega)
    have e2 := ext_eq_mod hS hA (j + g) (by omega) (by omega)
    rw [hjk, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega),
      Int.toNat_natCast] at e1
    rw [hjk, show (k : ℤ) + d * (-(((k : ℤ) - a) / d)) + g = ((k + g : ℕ) : ℤ) + d * (-(((k : ℤ) - a) / d))
      by push_cast; ring, Int.add_mul_emod_self_left, toNat_emod_natCast] at e2
    have hP' := hPg j (by omega) (by omega)
    rw [hjk] at hP'
    rw [← e1, ← e2, hP']
    congr 1
    push_cast
    ring
  apply hap
  refine ⟨g, by omega, hg0, hgd, fun k hk => ?_⟩
  rw [get_pre d w k hk, get_pre d w (k % g) (lt_of_lt_of_le (Nat.mod_lt _ hg0) (by omega))]
  exact rep_of_cyclic w (by omega) hg0 hcyc k hk

end RightShift
```

### `RightShiftAdd.lean`

```lean
import RightShiftBridge

/-!
# `add` is well defined

For `s ∈ B(n, c, d)` (any admissible spacing `d`), the number `add(s)` of Definition 3 exists, is
unique, and satisfies `add(s) < n - c` (the source's Lemma 3(ii)).  The proof of existence is a
parity argument: if no mismatch occurred in the last `n - c` positions, the shift-difference word
of the `d`-periodic word on `s_d` with shift `-n` would have exactly one `true` entry in a period.
-/

namespace RightShift

section
variable {n c d : ℕ} {w : Fin n → Bool}

/-- Uniqueness of `add`. -/
theorem isAdd_unique {t₁ t₂ : ℕ} (h₁ : IsAdd n d w t₁) (h₂ : IsAdd n d w t₂) : t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd (h₂.2.1 t₁ h) h₁.2.2
  · exact h
  · exact absurd (h₁.2.1 t₂ h) h₂.2.2

/-- Existence of `add`, with the bound `add(s) < n - c` (Lemma 3(ii) of the source). -/
theorem isAdd_exists (hS : InBStruct n c d w) : ∃ t, t < n - c ∧ IsAdd n d w t := by
  classical
  have hcd := hS.cd_le
  have hd1 := hS.d_pos
  have hex : ∃ t, t < n - c ∧
      get w (n - 1 - t) ≠ get w ((((d : ℤ) - 1 - t) % d).toNat) := by
    by_contra hno
    push Not at hno
    let U : ℤ → Bool := fun k => get w ((k % (d : ℤ)).toNat)
    have hU : ∀ k, U (k + d) = U k := by
      intro k
      show get w (((k + d) % (d : ℤ)).toNat) = get w ((k % (d : ℤ)).toNat)
      rw [show k + (d : ℤ) = k + d * 1 by ring, Int.add_mul_emod_self_left]
    -- the match at position `k ∈ [c, n - 1]`
    have hmatch : ∀ k : ℕ, c ≤ k → k < n → get w k = U ((k : ℤ) + -(n : ℤ)) := by
      intro k h1 h2
      have := hno (n - 1 - k) (by omega)
      rw [show n - 1 - (n - 1 - k) = k by omega] at this
      rw [this]
      show _ = get w ((((k : ℤ) + -(n : ℤ)) % (d : ℤ)).toNat)
      congr 2
      rw [show (d : ℤ) - 1 - ((n - 1 - k : ℕ) : ℤ) = ((k : ℤ) + -(n : ℤ)) + d * 1 by omega,
        Int.add_mul_emod_self_left]
    have hz : cntI (fun j => (dw U (-(n : ℤ)) j).toNat) c (c + d - 1) = 0 := by
      refine cntI_zero _ (fun i h1 h2 => ?_)
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ i by omega)
      unfold dw
      rw [← hmatch k (by omega) (by omega)]
      show (xor (get w (((k : ℤ) % (d : ℤ)).toNat)) (get w k)).toNat = 0
      rw [toNat_emod_natCast, ← hS.blk k (by omega)]
      cases get w k <;> rfl
    have h1 : dw U (-(n : ℤ)) ((c : ℤ) + d - 1) = true := by
      unfold dw
      rw [show (c : ℤ) + d - 1 = ((c + d - 1 : ℕ) : ℤ) by omega, ← hmatch (c + d - 1) (by omega)
        (by omega), hS.brk]
      show xor (get w ((((c + d - 1 : ℕ) : ℤ) % (d : ℤ)).toNat)) _ = true
      rw [toNat_emod_natCast]
      cases get w ((c + d - 1) % d) <;> rfl
    have hsplit := cntI_split (fun j => (dw U (-(n : ℤ)) j).toNat)
      (show (c : ℤ) ≤ c + d - 1 by omega) (show (c : ℤ) + d - 1 ≤ c + d by omega)
    have hs1 := cntI_single (fun j => (dw U (-(n : ℤ)) j).toNat) ((c : ℤ) + d - 1)
    rw [show (c : ℤ) + d - 1 + 1 = c + d by ring] at hs1
    rw [hz, hs1, h1] at hsplit
    have hev := dw_even U (show (0 : ℤ) ≤ d by omega) hU (-(n : ℤ)) c
    rw [hsplit] at hev
    exact absurd hev (by decide)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, by have := (Nat.find_spec hex).1; omega,
    fun i hi => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hi
  push Not at this
  exact this (by have := (Nat.find_spec hex).1; omega)

/-- Lemma 3(ii) of the source: `add(s) < n - c`. -/
theorem isAdd_lt (hS : InBStruct n c d w) {t : ℕ} (h : IsAdd n d w t) : t < n - c := by
  obtain ⟨t', ht', h'⟩ := isAdd_exists hS
  rw [isAdd_unique h h']
  exact ht'

open Classical in
/-- `add(s)` as a function (the unique `t` of Definition 3 when it exists). -/
noncomputable def add (n d : ℕ) (w : Fin n → Bool) : ℕ :=
  if h : ∃ t, IsAdd n d w t then Nat.find h else 0

theorem add_spec (hS : InBStruct n c d w) : IsAdd n d w (add n d w) := by
  classical
  have h : ∃ t, IsAdd n d w t := by
    obtain ⟨t, -, ht⟩ := isAdd_exists hS
    exact ⟨t, ht⟩
  unfold add
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem isAdd_iff_add_eq (hS : InBStruct n c d w) (t : ℕ) : IsAdd n d w t ↔ add n d w = t :=
  ⟨fun h => isAdd_unique (add_spec hS) h, fun h => h ▸ add_spec hS⟩

end

end RightShift
```

### `RightShiftMain.lean`

```lean
import RightShiftFineWilf
import RightShiftAdd

/-!
# Conjecture 1 of Yuan–Li–Zeng

`conjecture1_struct` proves the statement with only the structural part of `B(n, c, d)` assumed
(the literal definition `InB` additionally requires the whole sequence to be aperiodic, which the
source notes is automatic).  `conjecture1 : Conjecture1` is the literal endpoint, and
`conjecture1_add` is the same statement with `add` as a function.
-/

namespace RightShift

theorem conjecture1_struct (n c : ℕ) (s : Fin n → Bool) (hc : (n + 1) / 2 ≤ c)
    (hs : InBStruct n c (n - c) s) (b d₂ : ℕ) (hb0 : 0 < b) (hbn : b < n)
    (hv : InBStruct n c d₂ (rotR n b s)) (t₁ t₂ : ℕ) (h₁ : IsAdd n (n - c) s t₁)
    (h₂ : IsAdd n d₂ (rotR n b s) t₂) (hlt : t₁ < t₂) : b = d₂ := by
  have hd1 := hs.d_pos
  have hc1 : 1 ≤ c := by omega
  have he1 := hv.d_pos
  have hed : d₂ ≤ n - c := le_trans hv.2.2.1 (min_le_left _ _)
  have RD1 := runData hs hc1 h₁
  have RD2 := runData hv hc1 h₂
  have hrot := ext_rotR s b hbn
  have H : Config (ext s) n c (n - c : ℕ) t₁ d₂ (((n : ℤ) - b) - t₂) (((n : ℤ) - b) + c + d₂ - 2) :=
    { hn := by omega
      hdc := by omega
      hd1 := by omega
      he1 := by omega
      hed := by omega
      ht := by omega
      per := ext_per s
      runA := fun i h1 h2 => RD1.1 i h1 (by omega)
      brAr := by
        have := RD1.2.1
        rwa [show (c : ℤ) + ((n - c : ℕ) : ℤ) - 1 = (n : ℤ) - 1 by omega,
          show (c : ℤ) - 1 = (n : ℤ) - 1 - ((n - c : ℕ) : ℤ) by omega] at this
      brAl := RD1.2.2
      fw := by
        intro hlt' a h1 h2 hper
        exact fw_of hs h₁ hc1 d₂ (by omega) (by omega) a h1 (by omega) hper
      runB := by
        intro i h1 h2
        have := RD2.1 (i - ((n : ℤ) - b)) (by omega) (by omega)
        rw [hrot, hrot, show i - ((n : ℤ) - b) + ((n : ℤ) - b) = i by ring,
          show i - ((n : ℤ) - b) + d₂ + ((n : ℤ) - b) = i + d₂ by ring] at this
        exact this
      brBr := by
        have := RD2.2.1
        rw [hrot, hrot, show (c : ℤ) + d₂ - 1 + ((n : ℤ) - b) = ((n : ℤ) - b) + c + d₂ - 2 + 1 by ring,
          show (c : ℤ) - 1 + ((n : ℤ) - b) = ((n : ℤ) - b) + c + d₂ - 2 + 1 - d₂ by ring] at this
        exact this
      brBl := by
        have := RD2.2.2
        rw [hrot, hrot, show -(t₂ : ℤ) - 1 + ((n : ℤ) - b) = ((n : ℤ) - b) - t₂ - 1 by ring,
          show -(t₂ : ℤ) - 1 + d₂ + ((n : ℤ) - b) = ((n : ℤ) - b) - t₂ - 1 + d₂ by ring] at this
        exact this
      len := by omega }
  obtain ⟨q, hq⟩ := H.main
  have hnq : (n : ℤ) * q = n - b + d₂ := by linarith
  have hdn : d₂ < n := by omega
  rcases (show q ≤ 0 ∨ q = 1 ∨ 2 ≤ q by omega) with h | h | h
  · nlinarith
  · subst h
    omega
  · nlinarith

/-- **Conjecture 1 of Yuan, Li and Zeng (arXiv:2602.01134), proved.** -/
theorem conjecture1 : Conjecture1 := by
  intro n c s hc hs b d₂ hb0 hbn hv t₁ t₂ h₁ h₂ hlt
  exact conjecture1_struct n c s hc hs.2 b d₂ hb0 hbn hv.2 t₁ t₂ h₁ h₂ hlt

/-- Conjecture 1 with `add` as a function. -/
theorem conjecture1_add (n c : ℕ) (s : Fin n → Bool) (hc : (n + 1) / 2 ≤ c)
    (hs : InB n c (n - c) s) (b d₂ : ℕ) (hb0 : 0 < b) (hbn : b < n)
    (hv : InB n c d₂ (rotR n b s)) (hadd : add n (n - c) s < add n d₂ (rotR n b s)) : b = d₂ :=
  conjecture1 n c s hc hs b d₂ hb0 hbn hv _ _ (add_spec hs.2) (add_spec hv.2) hadd

/-- Non-vacuity of `add` where the statement uses it: for `s ∈ B(n, c, n - c)` and
`R^b(s) ∈ B(n, c, d₂)`, both `add` values exist, are unique, and are `< n - c`. -/
theorem add_well_defined (n c d : ℕ) (w : Fin n → Bool) (hw : InB n c d w) :
    ∃ t, t < n - c ∧ IsAdd n d w t ∧ ∀ t', IsAdd n d w t' → t' = t := by
  obtain ⟨t, ht, h⟩ := isAdd_exists hw.2
  exact ⟨t, ht, h, fun t' h' => isAdd_unique h' h⟩

end RightShift
```

### `RightShiftExamples.lean`

```lean
import RightShiftMain
import Mathlib.Data.Fin.VecNotation

/-!
# Non-vacuity, kernel-checked by `decide`

* `instance4`, `instance11`: all hypotheses of Conjecture 1 hold (so the statement is not
  vacuous); in `instance11` the spacing drops from `d = 5` to `d₂ = 3` and `add` rises from 1 to 4.
* `strict_needed`: with `add(R^b(s)) = add(s)` the conclusion fails (`n = 6`, `b = 1`, `d₂ = 2`),
  so the strict inequality in Conjecture 1 cannot be weakened to `≥`.
-/

namespace RightShift

def s4 : Fin 4 → Bool := ![false, true, false, false]

theorem instance4 :
    (4 + 1) / 2 ≤ 2 ∧ InB 4 2 (4 - 2) s4 ∧ 0 < 1 ∧ 1 < 4 ∧ InB 4 2 1 (rotR 4 1 s4) ∧
    IsAdd 4 (4 - 2) s4 0 ∧ IsAdd 4 1 (rotR 4 1 s4) 1 ∧ 0 < 1 := by
  unfold InB InBStruct Aperiodic pre IsAdd
  decide

def s11 : Fin 11 → Bool := ![true, false, false, true, false, true, false, false, true, false, false]

theorem instance11 :
    (11 + 1) / 2 ≤ 6 ∧ InB 11 6 (11 - 6) s11 ∧ 0 < 3 ∧ 3 < 11 ∧ InB 11 6 3 (rotR 11 3 s11) ∧
    IsAdd 11 (11 - 6) s11 1 ∧ IsAdd 11 3 (rotR 11 3 s11) 4 ∧ 1 < 4 := by
  unfold InB InBStruct Aperiodic pre IsAdd
  decide

def s6 : Fin 6 → Bool := ![true, false, true, true, false, false]

theorem instance6_equal_add :
    (6 + 1) / 2 ≤ 3 ∧ InB 6 3 (6 - 3) s6 ∧ 0 < 1 ∧ 1 < 6 ∧ InB 6 3 2 (rotR 6 1 s6) ∧
    IsAdd 6 (6 - 3) s6 0 ∧ IsAdd 6 2 (rotR 6 1 s6) 0 ∧ (1 : ℕ) ≠ 2 := by
  unfold InB InBStruct Aperiodic pre IsAdd
  decide

/-- The non-strict version of Conjecture 1 is false. -/
theorem strict_needed :
    ¬ ∀ (n c : ℕ) (s : Fin n → Bool), (n + 1) / 2 ≤ c → InB n c (n - c) s →
      ∀ b d₂ : ℕ, 0 < b → b < n → InB n c d₂ (rotR n b s) →
        ∀ t₁ t₂ : ℕ, IsAdd n (n - c) s t₁ → IsAdd n d₂ (rotR n b s) t₂ → t₁ ≤ t₂ → b = d₂ := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := instance6_equal_add
  exact h8 (h 6 3 s6 h1 h2 1 2 h3 h4 h5 0 0 h6 h7 le_rfl)

/-- The hypotheses of Conjecture 1 are satisfiable. -/
theorem hypotheses_satisfiable :
    ∃ (n c : ℕ) (s : Fin n → Bool) (b d₂ t₁ t₂ : ℕ), (n + 1) / 2 ≤ c ∧ InB n c (n - c) s ∧
      0 < b ∧ b < n ∧ InB n c d₂ (rotR n b s) ∧ IsAdd n (n - c) s t₁ ∧
      IsAdd n d₂ (rotR n b s) t₂ ∧ t₁ < t₂ :=
  ⟨11, 6, s11, 3, 3, 1, 4, instance11⟩

end RightShift

#print axioms RightShift.conjecture1
#print axioms RightShift.conjecture1_struct
#print axioms RightShift.conjecture1_add
#print axioms RightShift.add_well_defined
#print axioms RightShift.isAdd_unique
#print axioms RightShift.isAdd_lt
#print axioms RightShift.run_lemma
#print axioms RightShift.instance4
#print axioms RightShift.instance11
#print axioms RightShift.instance6_equal_add
#print axioms RightShift.strict_needed
#print axioms RightShift.hypotheses_satisfiable
```

