# Lean source appendix (MathDB 375588)

Modules are listed in import order. Each block is byte-identical to `src/<Module>.lean`.

### `BraidCore.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Words in braid generators: half twists and their basic identities

All identities are proved for an arbitrary monoid `G` and an arbitrary family
`s : ℕ → G` satisfying the braid relations among `s 0, …, s (K-1)` (predicate `BR s K`).
`s i` plays the role of the source's `σ_{i+1}` (0-based indexing).  A word is a `List ℕ`
of generator indices and `wp s l` is its product.
-/

namespace BGL

variable {G : Type*} [Monoid G]

/-- Product of the word `l` in the generators `s`. -/
def wp (s : ℕ → G) (l : List ℕ) : G := (l.map s).prod

@[simp] lemma wp_nil (s : ℕ → G) : wp s [] = 1 := rfl
@[simp] lemma wp_cons (s : ℕ → G) (a : ℕ) (l : List ℕ) : wp s (a :: l) = s a * wp s l := by
  simp [wp]
@[simp] lemma wp_append (s : ℕ → G) (l l' : List ℕ) : wp s (l ++ l') = wp s l * wp s l' := by
  simp [wp]
lemma wp_map (s : ℕ → G) (f : ℕ → ℕ) (l : List ℕ) : wp s (l.map f) = wp (fun i => s (f i)) l := by
  simp [wp, List.map_map, Function.comp_def]
lemma wp_congr {s t : ℕ → G} {l : List ℕ} (h : ∀ x ∈ l, s x = t x) : wp s l = wp t l := by
  unfold wp; rw [List.map_congr_left h]

section
variable {J : Type*} [Group J]

/-- Conjugation acting on generators acts on words. -/
lemma conj_wp (g : J) (s : ℕ → J) (f : ℕ → ℕ) (l : List ℕ)
    (h : ∀ x ∈ l, g * s x * g⁻¹ = s (f x)) : g * wp s l * g⁻¹ = wp s (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [wp_cons, List.map_cons]
    rw [← h a (by simp), ← ih (fun x hx => h x (by simp [hx]))]; group

lemma conj_wp' (g : J) (s : ℕ → J) (f : ℕ → ℕ) (l : List ℕ)
    (h : ∀ x ∈ l, g⁻¹ * s x * g = s (f x)) : g⁻¹ * wp s l * g = wp s (l.map f) := by
  have := conj_wp g⁻¹ s f l (by simpa using h); simpa using this

end

lemma commute_wp {g : G} {s : ℕ → G} {l : List ℕ} (h : ∀ x ∈ l, Commute g (s x)) :
    Commute g (wp s l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [wp_cons]; exact (h a (by simp)).mul_right (ih fun x hx => h x (by simp [hx]))

lemma commute_wp_wp {s t : ℕ → G} {l l' : List ℕ} (h : ∀ x ∈ l, ∀ y ∈ l', Commute (s x) (t y)) :
    Commute (wp s l) (wp t l') := by
  apply commute_wp; intro y hy
  exact (commute_wp (fun x hx => (h x hx y hy).symm)).symm

/-- The braid relations among `s 0, …, s (K-1)`. -/
structure BR (s : ℕ → G) (K : ℕ) : Prop where
  braid : ∀ i, i + 1 < K → s i * s (i + 1) * s i = s (i + 1) * s i * s (i + 1)
  comm : ∀ i j, i + 2 ≤ j → j < K → s i * s j = s j * s i

/-- Shifted family. -/
def sh {α : Type*} (s : ℕ → α) (k : ℕ) : ℕ → α := fun i => s (i + k)

@[simp] lemma sh_apply {α : Type*} (s : ℕ → α) (k i : ℕ) : sh s k i = s (i + k) := rfl

lemma BR.shift {s : ℕ → G} {K : ℕ} (h : BR s K) (k : ℕ) : BR (sh s k) (K - k) where
  braid i hi := by
    have := h.braid (i + k) (by omega)
    simpa [Nat.add_right_comm] using this
  comm i j hij hj := h.comm (i + k) (j + k) (by omega) (by omega)

lemma BR.mono {s : ℕ → G} {K K' : ℕ} (h : BR s K) (h' : K' ≤ K) : BR s K' where
  braid i hi := h.braid i (by omega)
  comm i j hij hj := h.comm i j hij (by omega)

lemma BR.cm {s : ℕ → G} {K : ℕ} (h : BR s K) {i j : ℕ} (hij : i + 2 ≤ j ∨ j + 2 ≤ i)
    (hi : i < K) (hj : j < K) : Commute (s i) (s j) := by
  rcases hij with hij | hij
  · exact h.comm i j hij hj
  · exact (h.comm j i hij hi).symm

/-! ## Basic words -/

/-- `dscL m = [m-1, …, 1, 0]`. -/
def dscL : ℕ → List ℕ
  | 0 => []
  | m + 1 => m :: dscL m

/-- `ascL m = [0, 1, …, m-1]`. -/
def ascL : ℕ → List ℕ
  | 0 => []
  | m + 1 => ascL m ++ [m]

/-- The half twist word on `m` strands:
`hwL m = dscL 0 ++ dscL 1 ++ ⋯ ++ dscL (m-1)`, i.e. `∏_{k=1}^{m-1} (σ_k σ_{k-1} ⋯ σ_1)`. -/
def hwL : ℕ → List ℕ
  | 0 => []
  | m + 1 => hwL m ++ dscL m

@[simp] lemma mem_dscL {x m : ℕ} : x ∈ dscL m ↔ x < m := by
  induction m with
  | zero => simp [dscL]
  | succ m ih => simp [dscL, ih]; omega

@[simp] lemma mem_ascL {x m : ℕ} : x ∈ ascL m ↔ x < m := by
  induction m with
  | zero => simp [ascL]
  | succ m ih => simp [ascL, ih]; omega

lemma mem_hwL {x m : ℕ} (h : x ∈ hwL m) : x + 2 ≤ m := by
  induction m with
  | zero => simp [hwL] at h
  | succ m ih =>
    simp only [hwL, List.mem_append, mem_dscL] at h
    rcases h with h | h
    · have := ih h; omega
    · omega

lemma dscL_succ' (m : ℕ) : dscL (m + 1) = (dscL m).map (· + 1) ++ [0] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (m + 1) :: dscL (m + 1) = (m :: dscL m).map (· + 1) ++ [0]
    rw [ih]; simp

lemma ascL_succ' (m : ℕ) : ascL (m + 1) = 0 :: (ascL m).map (· + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show ascL (m + 1) ++ [m + 1] = 0 :: (ascL m ++ [m]).map (· + 1)
    rw [ih]; simp

lemma dscL_add (a b : ℕ) : dscL (a + b) = (dscL b).map (· + a) ++ dscL a := by
  induction b with
  | zero => simp [dscL]
  | succ b ih => rw [← Nat.add_assoc, dscL, ih]; simp [dscL]; omega

lemma dscL_map_rev (m : ℕ) : (dscL m).map (fun x => m - 1 - x) = ascL m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ascL_succ', dscL]
    simp only [List.map_cons, Nat.add_sub_cancel, Nat.sub_self, List.cons.injEq, true_and]
    rw [← ih, List.map_map]
    apply List.map_congr_left
    intro x hx; simp only [mem_dscL] at hx; simp only [Function.comp_apply]; omega

lemma wp_sh (s : ℕ → G) (k : ℕ) (l : List ℕ) : wp (sh s k) l = wp s (l.map (· + k)) := by
  rw [wp_map]; rfl

lemma sh_sh {α : Type*} (s : ℕ → α) (a b : ℕ) : sh (sh s a) b = sh s (b + a) := by
  funext i; simp [sh, Nat.add_assoc]

lemma sh_zero {α : Type*} (s : ℕ → α) : sh s 0 = s := by funext i; simp

/-- The descending word `σ_m ⋯ σ_1`, the ascending word, and the half twist. -/
def D (s : ℕ → G) (m : ℕ) : G := wp s (dscL m)
def A (s : ℕ → G) (m : ℕ) : G := wp s (ascL m)
def Hw (s : ℕ → G) (m : ℕ) : G := wp s (hwL m)

lemma Hw_succ (s : ℕ → G) (m : ℕ) : Hw s (m + 1) = Hw s m * D s m := by
  simp [Hw, D, hwL]
lemma D_succ (s : ℕ → G) (m : ℕ) : D s (m + 1) = s m * D s m := by simp [D, dscL]
lemma A_succ (s : ℕ → G) (m : ℕ) : A s (m + 1) = A s m * s m := by simp [A, ascL]
lemma D_succ' (s : ℕ → G) (m : ℕ) : D s (m + 1) = D (sh s 1) m * s 0 := by
  simp [D, dscL_succ', wp_sh]
lemma A_succ' (s : ℕ → G) (m : ℕ) : A s (m + 1) = s 0 * A (sh s 1) m := by
  simp [A, ascL_succ', wp_sh]
@[simp] lemma Hw_zero (s : ℕ → G) : Hw s 0 = 1 := rfl
@[simp] lemma Hw_one (s : ℕ → G) : Hw s 1 = 1 := rfl
@[simp] lemma D_zero (s : ℕ → G) : D s 0 = 1 := rfl
@[simp] lemma A_zero (s : ℕ → G) : A s 0 = 1 := rfl

section
variable {s : ℕ → G} {K : ℕ}

lemma commute_D (h : BR s K) {j m : ℕ} (hj : m + 1 ≤ j) (hK : j < K) : Commute (s j) (D s m) := by
  apply commute_wp; intro x hx; simp only [mem_dscL] at hx
  exact h.cm (Or.inr (by omega)) hK (by omega)

lemma commute_A (h : BR s K) {j m : ℕ} (hj : m + 1 ≤ j) (hK : j < K) : Commute (s j) (A s m) := by
  apply commute_wp; intro x hx; simp only [mem_ascL] at hx
  exact h.cm (Or.inr (by omega)) hK (by omega)

lemma commute_Hw (h : BR s K) {j m : ℕ} (hj : m ≤ j) (hK : j < K) : Commute (s j) (Hw s m) := by
  apply commute_wp; intro x hx; have := mem_hwL hx
  exact h.cm (Or.inr (by omega)) hK (by omega)

/-- Lemma A: `σ_i (σ_m ⋯ σ_1) = (σ_m ⋯ σ_1) σ_{i+1}`. -/
lemma s_mul_D (h : BR s K) {m i : ℕ} (hm : m ≤ K) (hi : i + 1 < m) :
    s i * D s m = D s m * s (i + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [D_succ]
    by_cases him : i + 1 < m
    · rw [← mul_assoc, h.comm i m (by omega) (by omega), mul_assoc, ih (by omega) him, mul_assoc]
    · have hm' : m = i + 1 := by omega
      subst hm'
      rw [D_succ]
      have hc := (commute_D h (j := i + 1) (m := i) (by omega) (by omega)).eq
      calc s i * (s (i + 1) * (s i * D s i))
          = (s i * s (i + 1) * s i) * D s i := by simp only [mul_assoc]
        _ = (s (i + 1) * s i * s (i + 1)) * D s i := by rw [h.braid i (by omega)]
        _ = s (i + 1) * s i * (s (i + 1) * D s i) := by simp only [mul_assoc]
        _ = s (i + 1) * s i * (D s i * s (i + 1)) := by rw [hc]
        _ = s (i + 1) * (s i * D s i) * s (i + 1) := by simp only [mul_assoc]

lemma A_mul_s (h : BR s K) {m i : ℕ} (hm : m ≤ K) (hi : i + 1 < m) :
    A s m * s i = s (i + 1) * A s m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [A_succ]
    by_cases him : i + 1 < m
    · rw [mul_assoc, ← h.comm i m (by omega) (by omega), ← mul_assoc, ih (by omega) him, mul_assoc]
    · have hm' : m = i + 1 := by omega
      subst hm'
      rw [A_succ]
      have hc := (commute_A h (j := i + 1) (m := i) (by omega) (by omega)).eq
      calc A s i * s i * s (i + 1) * s i
          = A s i * (s i * s (i + 1) * s i) := by simp only [mul_assoc]
        _ = A s i * (s (i + 1) * s i * s (i + 1)) := by rw [h.braid i (by omega)]
        _ = (A s i * s (i + 1)) * s i * s (i + 1) := by simp only [mul_assoc]
        _ = (s (i + 1) * A s i) * s i * s (i + 1) := by rw [hc]
        _ = s (i + 1) * (A s i * s i * s (i + 1)) := by simp only [mul_assoc]

/-- Second standard form: `Δ_{m+1} = (σ_1 ⋯ σ_m) Δ_m`. -/
lemma Hw_succ_A (h : BR s K) {m : ℕ} (hm : m ≤ K) : Hw s (m + 1) = A s m * Hw s m := by
  induction m with
  | zero => simp [Hw, hwL, dscL]
  | succ m ih =>
    rw [show Hw s (m + 1 + 1) = Hw s (m + 1) * D s (m + 1) from Hw_succ s (m + 1)]
    conv_lhs => rw [ih (by omega)]
    rw [D_succ, A_succ, Hw_succ s m]
    have hc := (commute_Hw h (j := m) (m := m) le_rfl (by omega)).eq
    calc A s m * Hw s m * (s m * D s m) = A s m * (Hw s m * s m) * D s m := by simp only [mul_assoc]
      _ = A s m * (s m * Hw s m) * D s m := by rw [← hc]
      _ = A s m * s m * (Hw s m * D s m) := by simp only [mul_assoc]

/-- (F2) `Δ_m σ_i = σ_{m-i} Δ_m` (0-based: `s i ↦ s (m-2-i)`). -/
lemma Hw_mul_s (h : BR s K) {m i : ℕ} (hm : m ≤ K + 1) (hi : i + 2 ≤ m) :
    Hw s m * s i = s (m - 2 - i) * Hw s m := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rcases i with _ | i
    · by_cases hm1 : m = 1
      · subst hm1; simp [Hw, hwL, dscL]
      · rw [Hw_succ_A h (by omega), mul_assoc, ih (by omega) (by omega), ← mul_assoc,
          A_mul_s h (by omega) (by omega)]
        have : m - 2 - 0 + 1 = m + 1 - 2 - 0 := by omega
        rw [this, mul_assoc]
    · rw [Hw_succ, mul_assoc, ← s_mul_D h (by omega) (by omega), ← mul_assoc,
        ih (by omega) (by omega), mul_assoc, ← Hw_succ]
      have : m - 2 - i = m + 1 - 2 - (i + 1) := by omega
      rw [this]

/-- Palindrome identity `(σ_1⋯σ_m)(σ_{m+1}⋯σ_1) = (σ_{m+1}⋯σ_2)(σ_1⋯σ_{m+1})`. -/
lemma A_mul_D (h : BR s K) {m : ℕ} (hm : m + 1 ≤ K) :
    A s m * D s (m + 1) = D (sh s 1) m * A s (m + 1) := by
  induction m generalizing s K with
  | zero => simp [A, D, ascL, dscL]
  | succ m ih =>
    have h1 := h.shift 1
    have ih' := ih h1 (by omega)
    rw [A_succ' s m, D_succ' s (m + 1), A_succ' s (m + 1)]
    rw [show s 0 * A (sh s 1) m * (D (sh s 1) (m + 1) * s 0)
        = s 0 * (A (sh s 1) m * D (sh s 1) (m + 1)) * s 0 by simp only [mul_assoc], ih']
    rw [D_succ' (sh s 1) m, A_succ' (sh s 1) m]
    have c1 : Commute (s 0) (D (sh (sh s 1) 1) m) := by
      apply commute_wp; intro x hx; simp only [mem_dscL] at hx
      simp only [sh_apply]; exact h.cm (Or.inl (by omega)) (by omega) (by omega)
    have c2 : Commute (s 0) (A (sh (sh s 1) 1) m) := by
      apply commute_wp; intro x hx; simp only [mem_ascL] at hx
      simp only [sh_apply]; exact h.cm (Or.inl (by omega)) (by omega) (by omega)
    simp only [sh_apply, Nat.zero_add]
    have hb := h.braid 0 (by omega)
    simp only [Nat.zero_add] at hb
    calc s 0 * (D (sh (sh s 1) 1) m * (s 1 * A (sh (sh s 1) 1) m)) * s 0
        = (s 0 * D (sh (sh s 1) 1) m) * s 1 * (A (sh (sh s 1) 1) m * s 0) := by simp only [mul_assoc]
      _ = (D (sh (sh s 1) 1) m * s 0) * s 1 * (s 0 * A (sh (sh s 1) 1) m) := by
          rw [c1.eq, c2.eq]
      _ = D (sh (sh s 1) 1) m * (s 0 * s 1 * s 0) * A (sh (sh s 1) 1) m := by simp only [mul_assoc]
      _ = D (sh (sh s 1) 1) m * (s 1 * s 0 * s 1) * A (sh (sh s 1) 1) m := by rw [hb]
      _ = D (sh (sh s 1) 1) m * s 1 * (s 0 * (s 1 * A (sh (sh s 1) 1) m)) := by simp only [mul_assoc]

/-- Third standard form: `Δ_{m+1} = Δ'_m (σ_1 ⋯ σ_m)` with `Δ'_m` on strands `2..m+1`. -/
lemma Hw_succ_sh (h : BR s K) {m : ℕ} (hm : m ≤ K) : Hw s (m + 1) = Hw (sh s 1) m * A s m := by
  induction m with
  | zero => simp [Hw, hwL, dscL]
  | succ m ih =>
    rw [Hw_succ, ih (by omega), mul_assoc, A_mul_D h (by omega), ← mul_assoc, ← Hw_succ]

end

/-- Flip invariance of the half twist: reversing the generator indices fixes `Δ_m`. -/
lemma Hw_flip {s : ℕ → G} {K : ℕ} (h : BR s K) {m : ℕ} (hm : m ≤ K + 1) :
    wp (fun i => s (m - 2 - i)) (hwL m) = Hw s m := by
  induction m generalizing s K with
  | zero => rfl
  | succ m ih =>
    rcases m with _ | m
    · rfl
    · rw [hwL, wp_append]
      have e1 : wp (fun i => s (m + 1 + 1 - 2 - i)) (hwL (m + 1))
          = wp (fun i => (sh s 1) (m + 1 - 2 - i)) (hwL (m + 1)) := by
        apply wp_congr; intro x hx; have := mem_hwL hx; simp only [sh_apply]; congr 1; omega
      have e2 : wp (fun i => s (m + 1 + 1 - 2 - i)) (dscL (m + 1)) = A s (m + 1) := by
        rw [A, ← dscL_map_rev, wp_map]; apply wp_congr; intro x hx; congr 1
      rw [e1, ih (h.shift 1) (by omega), e2, ← Hw_succ_sh h (by omega)]

/-- Half twist on `w` strands starting at strand `u` (0-based). -/
def H (s : ℕ → G) (u w : ℕ) : G := Hw (sh s u) w

lemma H_def (s : ℕ → G) (u w : ℕ) : H s u w = wp s ((hwL w).map (· + u)) := by
  rw [H, Hw, wp_sh]

lemma H_zero (s : ℕ → G) (w : ℕ) : H s 0 w = Hw s w := by rw [H, sh_zero]

section
variable {J : Type*} [Group J]

variable {s : ℕ → J} {K : ℕ} in
lemma Hw_inv_mul_s (h : BR s K) {m i : ℕ} (hm : m ≤ K + 1) (hi : i + 2 ≤ m) :
    (Hw s m)⁻¹ * s i * Hw s m = s (m - 2 - i) := by
  have := Hw_mul_s h hm (i := m - 2 - i) (by omega)
  have e : m - 2 - (m - 2 - i) = i := by omega
  rw [e] at this
  rw [mul_assoc, ← this]; group

variable {s : ℕ → J} {K : ℕ} in
lemma Hw_conj_s (h : BR s K) {m i : ℕ} (hm : m ≤ K + 1) (hi : i + 2 ≤ m) :
    Hw s m * s i * (Hw s m)⁻¹ = s (m - 2 - i) := by
  rw [Hw_mul_s h hm hi]; group

/-- General flip: if conjugation by `g` reverses `s 0, …, s c`, it maps the half twist on
strands `[u, u+w)` to the half twist on `[c+2-u-w, c+2-u)`. -/
lemma conj_H {s : ℕ → J} {K : ℕ} (h : BR s K) (g : J) {c u w : ℕ}
    (hg : ∀ i, i ≤ c → g * s i * g⁻¹ = s (c - i)) (huw : u + w ≤ c + 2) (hc : c < K) :
    g * H s u w * g⁻¹ = H s (c + 2 - u - w) w := by
  rw [H_def, conj_wp g s (fun i => c - i)]
  · rw [List.map_map, wp_map, H, ← Hw_flip (h.shift (c + 2 - u - w)) (m := w) (by omega)]
    apply wp_congr; intro x hx; have := mem_hwL hx; simp only [Function.comp_apply]; congr 1; omega
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    have := mem_hwL hy; exact hg _ (by omega)

lemma conj_H' {s : ℕ → J} {K : ℕ} (h : BR s K) (g : J) {c u w : ℕ}
    (hg : ∀ i, i ≤ c → g⁻¹ * s i * g = s (c - i)) (huw : u + w ≤ c + 2) (hc : c < K) :
    g⁻¹ * H s u w * g = H s (c + 2 - u - w) w := by
  have := conj_H h g⁻¹ (c := c) (u := u) (w := w) (by simpa using hg) huw hc
  simpa using this
end


end BGL
```

### `BraidBlocks.lean`

```lean
import BraidCore

namespace BGL

variable {G : Type*} [Monoid G]

/-- Block words: half twists of consecutive blocks of widths `ws` starting at strand `u`. -/
def blkL : ℕ → List ℕ → List ℕ
  | _, [] => []
  | u, w :: ws => (hwL w).map (· + u) ++ blkL (u + w) ws

def Bk (s : ℕ → G) (u : ℕ) (ws : List ℕ) : G := wp s (blkL u ws)

lemma mem_blkL {x u : ℕ} {ws : List ℕ} (h : x ∈ blkL u ws) : u ≤ x ∧ x + 2 ≤ u + ws.sum := by
  induction ws generalizing u with
  | nil => simp [blkL] at h
  | cons w ws ih =>
    simp only [blkL, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · have := mem_hwL hy; simp; omega
    · have := ih h; simp; omega

lemma blkL_append (u : ℕ) (ws ws' : List ℕ) :
    blkL u (ws ++ ws') = blkL u ws ++ blkL (u + ws.sum) ws' := by
  induction ws generalizing u with
  | nil => simp [blkL]
  | cons w ws ih => simp [blkL, ih, Nat.add_assoc]

lemma blkL_shift (u k : ℕ) (ws : List ℕ) : blkL (u + k) ws = (blkL u ws).map (· + k) := by
  induction ws generalizing u with
  | nil => simp [blkL]
  | cons w ws ih =>
    simp only [blkL, List.map_append, List.map_map]
    rw [show u + k + w = (u + w) + k by omega, ih]
    congr 1; apply List.map_congr_left; intro x _; simp; omega

lemma Bk_cons (s : ℕ → G) (u w : ℕ) (ws : List ℕ) : Bk s u (w :: ws) = H s u w * Bk s (u + w) ws := by
  simp [Bk, blkL, H_def]

lemma Bk_append (s : ℕ → G) (u : ℕ) (ws ws' : List ℕ) :
    Bk s u (ws ++ ws') = Bk s u ws * Bk s (u + ws.sum) ws' := by
  simp [Bk, blkL_append]

@[simp] lemma Bk_nil (s : ℕ → G) (u : ℕ) : Bk s u [] = 1 := rfl

/-- `repL t ws`: `t` consecutive copies of the width pattern `ws`. -/
def repL : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | t + 1, ws => repL t ws ++ ws

lemma repL_sum (t : ℕ) (ws : List ℕ) : (repL t ws).sum = t * ws.sum := by
  induction t with
  | zero => simp [repL]
  | succ t ih => simp [repL, ih, Nat.succ_mul]

lemma repL_succ' (t : ℕ) (ws : List ℕ) : repL (t + 1) ws = ws ++ repL t ws := by
  induction t with
  | zero => simp [repL]
  | succ t ih =>
    show repL (t + 1) ws ++ ws = ws ++ (repL t ws ++ ws)
    rw [ih, List.append_assoc]

omit [Monoid G] in
lemma conjPow {M : Type*} [Group M] (g a : M) (k : ℕ) : (g * a * g⁻¹) ^ k = g * a ^ k * g⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

lemma repL_reverse_pair (t p q : ℕ) : (repL t [q, p]).reverse = repL t [p, q] := by
  induction t with
  | zero => rfl
  | succ t ih => rw [repL, List.reverse_append, ih, repL_succ']; rfl

lemma repL_reverse_single (t p : ℕ) : (repL t [p]).reverse = repL t [p] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    conv_lhs => rw [repL, List.reverse_append, ih]
    rw [repL_succ']; rfl

end BGL
```

### `BraidPositiveCore.lean`

```lean
import BraidBlocks
import Mathlib.Algebra.Group.Opposite

namespace BGL

variable {M : Type*} [Monoid M]

lemma wp_slide {s t : ℕ → M} {l : List ℕ} {g : M}
    (h : ∀ i ∈ l, s i * g = g * t i) : wp s l * g = g * wp t l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wp_cons, wp_cons, mul_assoc, ih (fun j hj => h j (by simp [hj])),
      ← mul_assoc, h i (by simp), mul_assoc]

lemma slide_wp {s t : ℕ → M} {l : List ℕ} {g : M}
    (h : ∀ i ∈ l, g * s i = t i * g) : g * wp s l = wp t l * g := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wp_cons, wp_cons, ← mul_assoc, h i (by simp), mul_assoc,
      ih (fun j hj => h j (by simp [hj])), ← mul_assoc]

def reflect (s : ℕ → M) (n : ℕ) : ℕ → M := fun i => s (n - 2 - i)

lemma BR.reflect {s : ℕ → M} {n : ℕ} (h : BR s (n - 1)) : BR (reflect s n) (n - 1) where
  braid i hi := by
    have e := (h.braid (n - 2 - (i + 1)) (by omega)).symm
    rw [show n - 2 - (i + 1) + 1 = n - 2 - i by omega] at e
    exact e
  comm i j hij hj := (h.comm (n - 2 - j) (n - 2 - i) (by omega) (by omega)).symm

lemma reflect_H {s : ℕ → M} {n u w : ℕ} (h : BR s (n - 1)) (_hn : 2 ≤ n)
    (huw : u + w ≤ n) : H (reflect s n) u w = H s (n - u - w) w := by
  rw [H, H, ← Hw_flip (h.shift (n - u - w)) (m := w) (by omega)]
  apply wp_congr
  intro i hi
  have := mem_hwL hi
  simp only [sh_apply, reflect]
  congr 1
  omega

lemma reflect_Hw {s : ℕ → M} {n w : ℕ} (h : BR s (n - 1)) (hn : 2 ≤ n) (hw : w ≤ n) :
    Hw (reflect s n) w = H s (n - w) w := by
  simpa [H_zero] using reflect_H (u := 0) (w := w) h hn (by omega)

lemma reflect_full {s : ℕ → M} {n : ℕ} (h : BR s (n - 1)) (hn : 2 ≤ n) :
    Hw (reflect s n) n = Hw s n := by
  rw [reflect_Hw h hn le_rfl, Nat.sub_self, H_zero]

lemma Hw_succ_right {s : ℕ → M} {K m : ℕ} (h : BR s K) (hm : m ≤ K) :
    Hw s (m + 1) = D s m * H s 1 m := by
  rcases m with _ | m
  · simp [H, D, dscL]
  let r := reflect s (m + 2)
  have hr : BR r (m + 2 - 1) := (h.mono (by omega)).reflect
  have hsmall : BR s (m + 2 - 1) := h.mono (by omega)
  have hf := reflect_full (s := s) (n := m + 2) hsmall (by omega)
  have e := Hw_succ_A hr (m := m + 1) (by omega)
  rw [show Hw r (m + 1 + 1) = Hw s (m + 2) from hf,
    show Hw r (m + 1) = H s 1 (m + 1) by
      rw [show r = reflect s (m + 2) by rfl, reflect_Hw hsmall (by omega) (by omega)]
      congr 1
      omega] at e
  rw [e]
  congr 1
  have hword : (ascL (m + 1)).map (fun i => m - i) = dscL (m + 1) := by
    rw [← dscL_map_rev (m + 1), List.map_map]
    conv_rhs => rw [← List.map_id (dscL (m + 1))]
    apply List.map_congr_left
    intro i hi
    simp only [mem_dscL] at hi
    simp only [Function.comp_apply, id]
    omega
  change wp r (ascL (m + 1)) = _
  rw [show r = (fun i => s (m - i)) by rfl, ← wp_map, hword]
  rfl

lemma Bk_reflect {s : ℕ → M} {n : ℕ} (h : BR s (n - 1)) (hn : 2 ≤ n)
    (u : ℕ) (ws : List ℕ) (hu : u + ws.sum ≤ n) :
    Bk (reflect s n) u ws = Bk s (n - u - ws.sum) ws.reverse := by
  induction ws generalizing u with
  | nil => simp
  | cons w ws ih =>
    simp only [List.sum_cons] at hu
    rw [Bk_cons, reflect_H h hn (by omega), ih (u + w) (by omega), List.reverse_cons,
      Bk_append, List.sum_reverse, Bk_cons, Bk_nil, mul_one, List.sum_cons]
    rw [show n - u - (w + ws.sum) + ws.sum = n - u - w by omega,
      show n - (u + w) - ws.sum = n - u - (w + ws.sum) by omega]
    symm
    apply Commute.eq
    rw [H_def, Bk]
    apply commute_wp_wp
    intro x hx y hy
    have hx' := mem_blkL hx
    simp only [List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := mem_hwL hz
    simp only [List.sum_reverse] at hx'
    exact h.cm (Or.inl (by omega)) (by omega) (by omega)

lemma BR.op {s : ℕ → M} {K : ℕ} (h : BR s K) : BR (fun i => MulOpposite.op (s i)) K where
  braid i hi := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, mul_assoc] using h.braid i hi
  comm i j hij hj := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using (h.comm i j hij hj).symm

lemma wp_op {s : ℕ → M} (l : List ℕ) :
    MulOpposite.unop (wp (fun i => MulOpposite.op (s i)) l) = wp s l.reverse := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.reverse_cons, ih]

lemma ascL_reverse (m : ℕ) : (ascL m).reverse = dscL m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ascL, dscL, ih]

lemma Hw_op {s : ℕ → M} {K : ℕ} (h : BR s K) {m : ℕ} (hm : m ≤ K + 1) :
    MulOpposite.unop (Hw (fun i => MulOpposite.op (s i)) m) = Hw s m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Hw_succ_A h.op (by omega), MulOpposite.unop_mul, ih (by omega), A, wp_op, ascL_reverse,
      ← D, ← Hw_succ]

lemma H_op {s : ℕ → M} {K u w : ℕ} (h : BR s K) (hu : u + w ≤ K + 1) :
    MulOpposite.unop (H (fun i => MulOpposite.op (s i)) u w) = H s u w :=
  Hw_op (h.shift u) (by omega)

end BGL
```

### `BraidRho.lean`

```lean
import BraidBlocks

/-!
# The periodic braid `ρ`, Lemma B, block products, and cases I and II

Throughout, `s` satisfies the braid relations of `n` strands (`BR s (n-1)`), `Δ = Hw s n`,
`ρ = D s (n-1) = σ_{n-1} ⋯ σ_1`.
-/

namespace BGL

variable {G : Type*} [Group G]

section
variable {s : ℕ → G} {n : ℕ}

/-- Conjugation by `Δ` reverses the generators. -/
lemma Delta_conj (h : BR s (n - 1)) {i : ℕ} (hi : i ≤ n - 2) (hn : 2 ≤ n) :
    Hw s n * s i * (Hw s n)⁻¹ = s (n - 2 - i) :=
  Hw_conj_s h (by omega) (by omega)

lemma Delta_inv_conj (h : BR s (n - 1)) {i : ℕ} (hi : i ≤ n - 2) (hn : 2 ≤ n) :
    (Hw s n)⁻¹ * s i * Hw s n = s (n - 2 - i) :=
  Hw_inv_mul_s h (by omega) (by omega)

/-- `Δ H(u,w) Δ⁻¹ = H(n-u-w, w)`. -/
lemma Delta_conj_H (h : BR s (n - 1)) (hn : 2 ≤ n) {u w : ℕ} (huw : u + w ≤ n) :
    Hw s n * H s u w * (Hw s n)⁻¹ = H s (n - u - w) w := by
  have := conj_H h (Hw s n) (c := n - 2) (u := u) (w := w)
    (fun i hi => Delta_conj h hi hn) (by omega) (by omega)
  rwa [show n - 2 + 2 - u - w = n - u - w by omega] at this

/-- `Δ²` commutes with every generator, hence with every word. -/
lemma Delta_sq_comm (h : BR s (n - 1)) (hn : 2 ≤ n) {l : List ℕ} (hl : ∀ x ∈ l, x + 2 ≤ n) :
    Commute (Hw s n ^ 2) (wp s l) := by
  apply commute_wp; intro i hi
  have hi' := hl i hi
  show Hw s n ^ 2 * s i = s i * Hw s n ^ 2
  rw [pow_two, mul_assoc, Hw_mul_s h (by omega) (by omega), ← mul_assoc,
    Hw_mul_s h (by omega) (by omega), show n - 2 - (n - 2 - i) = i by omega, mul_assoc]

lemma Delta_sq_comm_H (h : BR s (n - 1)) (hn : 2 ≤ n) {u w : ℕ} (huw : u + w ≤ n) :
    Commute (Hw s n ^ 2) (H s u w) := by
  rw [H_def]; apply Delta_sq_comm h hn
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
  have := mem_hwL hy; omega

lemma Delta_sq_comm_Bk (h : BR s (n - 1)) (hn : 2 ≤ n) {u : ℕ} {ws : List ℕ}
    (hu : u + ws.sum ≤ n) : Commute (Hw s n ^ 2) (Bk s u ws) := by
  apply Delta_sq_comm h hn; intro x hx; have := mem_blkL hx; omega

lemma Delta_sq_comm_rho (h : BR s (n - 1)) (hn : 2 ≤ n) : Commute (Hw s n ^ 2) (D s (n - 1)) := by
  apply Delta_sq_comm h hn; intro x hx; simp only [mem_dscL] at hx; omega

lemma inv_conj_eq_conj {Δ Z : G} (hc : Commute (Δ ^ 2) Z) : Δ⁻¹ * Z * Δ = Δ * Z * Δ⁻¹ := by
  have : Δ * Z * Δ⁻¹ = Δ⁻¹ * (Δ ^ 2 * Z) * Δ⁻¹ := by rw [pow_two]; group
  rw [this, hc.eq, pow_two]; group

/-- Lemma A, iterated: `ρ^{-k} Z ρ^k` shifts the word `Z` up by `k`. -/
lemma rho_pow_conj (h : BR s (n - 1)) (k : ℕ) {l : List ℕ} (hl : ∀ x ∈ l, x + k + 2 ≤ n) :
    (D s (n - 1) ^ k)⁻¹ * wp s l * D s (n - 1) ^ k = wp s (l.map (· + k)) := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_inv_rev,
      show (D s (n - 1))⁻¹ * (D s (n - 1) ^ k)⁻¹ * wp s l * (D s (n - 1) ^ k * D s (n - 1))
        = (D s (n - 1))⁻¹ * ((D s (n - 1) ^ k)⁻¹ * wp s l * D s (n - 1) ^ k) * D s (n - 1) by group,
      ih (fun x hx => by have := hl x hx; omega)]
    rw [conj_wp' (D s (n - 1)) s (· + 1)]
    · rw [List.map_map]; congr 1
    · intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have := hl y hy
      have e := s_mul_D h (m := n - 1) (i := y + k) le_rfl (by omega)
      rw [mul_assoc, e]; group

lemma rho_pow_conj_Bk (h : BR s (n - 1)) (k u : ℕ) (ws : List ℕ) (hu : u + ws.sum + k ≤ n) :
    (D s (n - 1) ^ k)⁻¹ * Bk s u ws * D s (n - 1) ^ k = Bk s (u + k) ws := by
  rw [Bk, rho_pow_conj h k, Bk, blkL_shift]
  intro x hx; have := mem_blkL hx; omega

/-- Lemma B: `Δ[1,n-k] ρ^k = Δ Δ[1,k]`. -/
lemma lemmaB (h : BR s (n - 1)) (hn : 2 ≤ n) :
    ∀ k m, m + k = n → Hw s m * D s (n - 1) ^ k = Hw s n * Hw s k := by
  intro k
  induction k with
  | zero => intro m hm; simp at hm; subst hm; simp
  | succ k ih =>
    intro m hm
    have hρ : D s (n - 1) = wp s ((dscL k).map (· + m)) * D s m := by
      rw [D, show n - 1 = m + k by omega, dscL_add, wp_append]; rfl
    have hc : Commute (Hw s m) (wp s ((dscL k).map (· + m))) := by
      apply commute_wp_wp; intro x hx y hy
      have := mem_hwL hx; simp only [List.mem_map, mem_dscL] at hy; obtain ⟨z, hz, rfl⟩ := hy
      exact h.cm (Or.inl (by omega)) (by omega) (by omega)
    have hU : (Hw s n)⁻¹ * wp s ((dscL k).map (· + m)) * Hw s n = A s k := by
      rw [conj_wp' (Hw s n) s (fun i => n - 2 - i)]
      · rw [A, ← dscL_map_rev, List.map_map]; congr 1
        apply List.map_congr_left; intro x hx; simp only [mem_dscL] at hx
        simp only [Function.comp_apply]; omega
      · intro x hx; simp only [List.mem_map, mem_dscL] at hx; obtain ⟨z, hz, rfl⟩ := hx
        exact Delta_inv_conj h (by omega) hn
    calc Hw s m * D s (n - 1) ^ (k + 1)
        = Hw s m * (wp s (List.map (· + m) (dscL k)) * D s m * D s (n - 1) ^ k) := by
          rw [pow_succ', ← hρ]
      _ = wp s (List.map (· + m) (dscL k)) * (Hw s m * D s m) * D s (n - 1) ^ k := by
          rw [← mul_assoc, ← mul_assoc, hc.eq]; group
      _ = wp s (List.map (· + m) (dscL k)) * (Hw s (m + 1) * D s (n - 1) ^ k) := by
          rw [Hw_succ]; group
      _ = wp s (List.map (· + m) (dscL k)) * (Hw s n * Hw s k) := by rw [ih (m + 1) (by omega)]
      _ = Hw s n * ((Hw s n)⁻¹ * wp s (List.map (· + m) (dscL k)) * Hw s n) * Hw s k := by group
      _ = Hw s n * Hw s (k + 1) := by rw [hU, mul_assoc, ← Hw_succ_A h (by omega)]

lemma rho_pow_n (h : BR s (n - 1)) (hn : 2 ≤ n) : D s (n - 1) ^ n = Hw s n ^ 2 := by
  have := lemmaB h hn n 0 (by simp); simpa [pow_two] using this

/-- `Δ[1,n-k] = Δ · Δ[1,k] · ρ^{-k}`. -/
lemma Hw_eq_Delta_W (h : BR s (n - 1)) (hn : 2 ≤ n) {k : ℕ} (hk : k ≤ n) :
    Hw s (n - k) = Hw s n * (Hw s k * (D s (n - 1) ^ k)⁻¹) := by
  rw [← mul_assoc, ← lemmaB h hn k (n - k) (by omega)]; group

/-- Powers of a block pattern times `ρ^{-j}`. -/
lemma block_pow (h : BR s (n - 1)) (ws : List ℕ) :
    ∀ t, t * ws.sum ≤ n →
      (Bk s 0 ws * (D s (n - 1) ^ ws.sum)⁻¹) ^ t = Bk s 0 (repL t ws) * (D s (n - 1) ^ (t * ws.sum))⁻¹ := by
  intro t
  induction t with
  | zero => intro _; simp [repL]
  | succ t ih =>
    intro ht
    rw [pow_succ, ih (by nlinarith)]
    have e := rho_pow_conj_Bk h (t * ws.sum) 0 ws (by simp; nlinarith)
    rw [repL, Bk_append, repL_sum]
    simp only [Nat.zero_add] at e ⊢
    rw [← e, Nat.succ_mul, pow_add, mul_inv_rev]; group

/-- Cases I: closed form of `(XY)^m` for `X = Δ[1,n-q]`, `Y = Δ[p+1,n]`, `m(p+q) = n`. -/
lemma caseI_pow (h : BR s (n - 1)) (hn : 2 ≤ n) (p q m : ℕ) (hm : m * (p + q) = n) :
    (Hw s (n - q) * H s p (n - p)) ^ m
      = Hw s n ^ (2 * m) * (Hw s n * Bk s 0 (repL m [q, p]) * (Hw s n)⁻¹) * (Hw s n ^ 2)⁻¹ := by
  have hpq : p + q ≤ n := by
    rcases m with _ | m
    · simp at hm; omega
    · nlinarith
  have cρ : Commute (Hw s n ^ 2) (D s (n - 1)) := Delta_sq_comm_rho h hn
  have cW : ∀ k, k ≤ n → Commute (Hw s n ^ 2) (Hw s k * (D s (n - 1) ^ k)⁻¹) := by
    intro k hk
    refine Commute.mul_right ?_ (cρ.pow_right k).inv_right
    rw [← H_zero s k]; exact Delta_sq_comm_H h hn (by omega)
  have hX : Hw s (n - q) = Hw s n * (Hw s q * (D s (n - 1) ^ q)⁻¹) := Hw_eq_Delta_W h hn (by omega)
  have hY : H s p (n - p) = Hw s n * (Hw s n * (Hw s p * (D s (n - 1) ^ p)⁻¹)) * (Hw s n)⁻¹ := by
    rw [← Hw_eq_Delta_W h hn (by omega), ← H_zero s (n - p), Delta_conj_H h hn (by omega)]
    congr 1; omega
  have hWW : (Hw s q * (D s (n - 1) ^ q)⁻¹) * (Hw s p * (D s (n - 1) ^ p)⁻¹)
      = Bk s 0 [q, p] * (D s (n - 1) ^ [q, p].sum)⁻¹ := by
    have e := rho_pow_conj h q (l := hwL p) (fun x hx => by have := mem_hwL hx; omega)
    rw [Bk_cons, Bk_cons, Bk_nil, H_zero, Nat.zero_add, H_def, ← e]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, pow_add]
    unfold Hw; group
  have hXY : Hw s (n - q) * H s p (n - p)
      = Hw s n * (Hw s n ^ 2 * (Bk s 0 [q, p] * (D s (n - 1) ^ [q, p].sum)⁻¹)) * (Hw s n)⁻¹ := by
    rw [hX, hY, ← hWW]
    have := (cW q (by omega)).eq
    rw [pow_two] at this ⊢
    calc Hw s n * (Hw s q * (D s (n - 1) ^ q)⁻¹)
          * (Hw s n * (Hw s n * (Hw s p * (D s (n - 1) ^ p)⁻¹)) * (Hw s n)⁻¹)
        = Hw s n * ((Hw s q * (D s (n - 1) ^ q)⁻¹) * (Hw s n * Hw s n))
          * (Hw s p * (D s (n - 1) ^ p)⁻¹) * (Hw s n)⁻¹ := by group
      _ = Hw s n * ((Hw s n * Hw s n) * (Hw s q * (D s (n - 1) ^ q)⁻¹))
          * (Hw s p * (D s (n - 1) ^ p)⁻¹) * (Hw s n)⁻¹ := by rw [this]
      _ = _ := by group
  have cE : Commute (Hw s n ^ 2) (Bk s 0 [q, p] * (D s (n - 1) ^ [q, p].sum)⁻¹) :=
    (Delta_sq_comm_Bk h hn (by simp; omega)).mul_right (cρ.pow_right _).inv_right
  rw [hXY, conjPow, cE.mul_pow, block_pow h [q, p] m (by simp; nlinarith)]
  have hsum : m * [q, p].sum = n := by simp; rw [← hm]; ring
  rw [hsum, rho_pow_n h hn, ← pow_mul]
  group

/-- `Δ` reverses a block product. -/
lemma Delta_conj_Bk (h : BR s (n - 1)) (hn : 2 ≤ n) :
    ∀ (u : ℕ) (ws : List ℕ), u + ws.sum ≤ n →
      Hw s n * Bk s u ws * (Hw s n)⁻¹ = Bk s (n - u - ws.sum) ws.reverse := by
  intro u ws
  induction ws generalizing u with
  | nil => intro _; simp
  | cons w ws ih =>
    intro hu
    simp only [List.sum_cons] at hu
    rw [Bk_cons, show Hw s n * (H s u w * Bk s (u + w) ws) * (Hw s n)⁻¹
      = (Hw s n * H s u w * (Hw s n)⁻¹) * (Hw s n * Bk s (u + w) ws * (Hw s n)⁻¹) by group,
      Delta_conj_H h hn (by omega), ih (u + w) (by omega), List.reverse_cons, Bk_append,
      List.sum_reverse, List.sum_cons, Bk_cons, Bk_nil, mul_one]
    rw [show n - u - (w + ws.sum) + ws.sum = n - u - w by omega,
      show n - (u + w) - ws.sum = n - u - (w + ws.sum) by omega]
    apply Commute.eq; symm
    rw [H_def, Bk]; apply commute_wp_wp; intro x hx y hy
    have hx' := mem_blkL hx; simp only [List.mem_map] at hy; obtain ⟨z, hz, rfl⟩ := hy
    have := mem_hwL hz
    simp only [List.sum_reverse] at hx'
    exact h.cm (Or.inl (by omega)) (by omega) (by omega)


theorem caseI (h : BR s (n - 1)) (hn : 2 ≤ n) (p q m : ℕ) (hm : m * (p + q) = n) :
    (Hw s (n - q) * H s p (n - p)) ^ m = (H s p (n - p) * Hw s (n - q)) ^ m := by
  have hpq : p + q ≤ n := by
    rcases m with _ | m
    · simp at hm; omega
    · nlinarith
  have hX : Hw s n * Hw s (n - q) * (Hw s n)⁻¹ = H s q (n - q) := by
    rw [← H_zero s (n - q), Delta_conj_H h hn (by omega)]; congr 1; omega
  have hY : Hw s n * H s p (n - p) * (Hw s n)⁻¹ = Hw s (n - p) := by
    rw [Delta_conj_H h hn (by omega), show n - p - (n - p) = 0 by omega, H_zero]
  have e1 := caseI_pow h hn p q m hm
  have e2 := caseI_pow h hn q p m (by rw [← hm]; ring)
  have hYX : (H s p (n - p) * Hw s (n - q)) ^ m
      = (Hw s n)⁻¹ * (Hw s (n - p) * H s q (n - q)) ^ m * Hw s n := by
    rw [← hX, ← hY, show Hw s n * H s p (n - p) * (Hw s n)⁻¹ * (Hw s n * Hw s (n - q) * (Hw s n)⁻¹)
      = Hw s n * (H s p (n - p) * Hw s (n - q)) * (Hw s n)⁻¹ by group, conjPow]; group
  have hsum : (repL m [q, p]).sum = n := by rw [repL_sum]; simp; rw [← hm]; ring
  have flip1 : Hw s n * Bk s 0 (repL m [q, p]) * (Hw s n)⁻¹ = Bk s 0 (repL m [p, q]) := by
    rw [Delta_conj_Bk h hn 0 _ (by rw [hsum]; omega), hsum, repL_reverse_pair]; simp
  rw [hYX, e1, e2, flip1]
  group

end

end BGL
```

### `BraidCase2.lean`

```lean
import BraidRho

/-!
# Alternating products and case II
-/

namespace BGL

/-- `alt N x y = x y x y ⋯` with `N` factors. -/
def alt {M : Type*} [Monoid M] : ℕ → M → M → M
  | 0, _, _ => 1
  | k + 1, x, y => x * alt k y x

variable {G : Type*} [Group G]

lemma alt_conj (g : G) : ∀ (k : ℕ) (x y : G),
    g * alt k x y * g⁻¹ = alt k (g * x * g⁻¹) (g * y * g⁻¹) := by
  intro k
  induction k with
  | zero => intro x y; simp [alt]
  | succ k ih => intro x y; rw [alt, alt, ← ih]; group

lemma alt_two_mul {M : Type*} [Monoid M] (x y : M) : ∀ m : ℕ, alt (2 * m) x y = (x * y) ^ m := by
  intro m
  induction m with
  | zero => simp [alt]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, alt, alt, ih, pow_succ', mul_assoc]

/-- If `y = g x g⁻¹` and `g²` commutes with `x`, then `alt k x y = (x g)^k g^{-k}`. -/
lemma alt_conj_self (g x : G) (hx : Commute (g ^ 2) x) :
    ∀ k : ℕ, alt k x (g * x * g⁻¹) = (x * g) ^ k * (g ^ k)⁻¹ := by
  have hyx : g * (g * x * g⁻¹) * g⁻¹ = x := by
    have := hx.eq; rw [pow_two] at this
    calc g * (g * x * g⁻¹) * g⁻¹ = (g * g * x) * g⁻¹ * g⁻¹ := by group
      _ = (x * (g * g)) * g⁻¹ * g⁻¹ := by rw [this]
      _ = x := by group
  intro k
  induction k with
  | zero => simp [alt]
  | succ k ih =>
    rw [alt, show alt k (g * x * g⁻¹) x = g * alt k x (g * x * g⁻¹) * g⁻¹ by
      rw [alt_conj, hyx], ih, pow_succ', pow_succ']
    group

section
variable {s : ℕ → G} {n : ℕ}

/-- Case II (in fact for every `N` with `N p = n`): with `X = Δ[1,n-p]`, `Y = Δ[p+1,n]`,
`alt N X Y = alt N Y X`. -/
theorem caseII (h : BR s (n - 1)) (hn : 2 ≤ n) (p N : ℕ) (hN : N * p = n) :
    alt N (Hw s (n - p)) (H s p (n - p)) = alt N (H s p (n - p)) (Hw s (n - p)) := by
  have hp : p ≤ n := by
    rcases N with _ | N
    · simp at hN; omega
    · nlinarith
  have cρ : Commute (Hw s n ^ 2) (D s (n - 1)) := Delta_sq_comm_rho h hn
  have cX : Commute (Hw s n ^ 2) (Hw s (n - p)) := by
    rw [← H_zero s (n - p)]; exact Delta_sq_comm_H h hn (by omega)
  have hY : H s p (n - p) = Hw s n * Hw s (n - p) * (Hw s n)⁻¹ := by
    rw [← H_zero s (n - p), Delta_conj_H h hn (by omega)]; congr 1; omega
  -- the alternating product in terms of `(XΔ)^N`
  have hA := alt_conj_self (Hw s n) (Hw s (n - p)) cX N
  have hXY : Hw s n * H s p (n - p) * (Hw s n)⁻¹ = Hw s (n - p) := by
    have := cX.eq; rw [pow_two] at this
    rw [hY]
    calc Hw s n * (Hw s n * Hw s (n - p) * (Hw s n)⁻¹) * (Hw s n)⁻¹
        = (Hw s n * Hw s n * Hw s (n - p)) * (Hw s n)⁻¹ * (Hw s n)⁻¹ := by group
      _ = (Hw s (n - p) * (Hw s n * Hw s n)) * (Hw s n)⁻¹ * (Hw s n)⁻¹ := by rw [this]
      _ = Hw s (n - p) := by group
  have hB : alt N (H s p (n - p)) (Hw s (n - p))
      = Hw s n * alt N (Hw s (n - p)) (H s p (n - p)) * (Hw s n)⁻¹ := by
    rw [alt_conj, hXY, ← hY]
  rw [hB, hY, hA]
  -- it remains to see that `Δ` commutes with `(XΔ)^N`
  suffices hc : Commute (Hw s n) ((Hw s (n - p) * Hw s n) ^ N) by
    rw [← mul_assoc (Hw s n), hc.eq]; group
  -- `X Δ = Δ (W Δ²) Δ⁻¹` with `W = Δ[1,p] ρ^{-p}`
  set W := Hw s p * (D s (n - 1) ^ p)⁻¹ with hW
  have hX : Hw s (n - p) = Hw s n * W := Hw_eq_Delta_W h hn hp
  have cW : Commute (Hw s n ^ 2) W := by
    refine Commute.mul_right ?_ (cρ.pow_right p).inv_right
    rw [← H_zero s p]; exact Delta_sq_comm_H h hn (by omega)
  have hXD : Hw s (n - p) * Hw s n = Hw s n * (W * Hw s n ^ 2) * (Hw s n)⁻¹ := by
    rw [hX, pow_two]; group
  have hWp : W ^ N = Bk s 0 (repL N [p]) * (Hw s n ^ 2)⁻¹ := by
    have e := block_pow h [p] N (by simp; omega)
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at e
    rw [hN, rho_pow_n h hn] at e
    rw [← e, Bk_cons, Bk_nil, mul_one, H_zero]
  have hflip : Hw s n * Bk s 0 (repL N [p]) * (Hw s n)⁻¹ = Bk s 0 (repL N [p]) := by
    have hsum : (repL N [p]).sum = n := by rw [repL_sum]; simp; exact hN
    rw [Delta_conj_Bk h hn 0 _ (by rw [hsum]; omega), hsum, repL_reverse_single]; simp
  have cB : Commute (Hw s n) (Bk s 0 (repL N [p])) := by
    show Hw s n * Bk s 0 (repL N [p]) = Bk s 0 (repL N [p]) * Hw s n
    calc Hw s n * Bk s 0 (repL N [p]) = (Hw s n * Bk s 0 (repL N [p]) * (Hw s n)⁻¹) * Hw s n := by
          group
      _ = Bk s 0 (repL N [p]) * Hw s n := by rw [hflip]
  rw [hXD, conjPow, cW.symm.mul_pow, hWp, ← pow_mul]
  have c1 : Commute (Hw s n) (Hw s n) := Commute.refl _
  exact (c1.mul_right (((cB.mul_right ((c1.pow_right 2).inv_right)).mul_right
    (c1.pow_right _)))).mul_right c1.inv_right

end

end BGL
```

### `BraidCross.lean`

```lean
import BraidPositiveCore

/-!
# Block crossings

`crossL x y` is the positive permutation braid exchanging a left block of `x` strands with a
right block of `y` strands (starting at strand `0`).  We prove the two-block decomposition
`Δ_{x+y} = Δ_x · Δ[x+1,x+y] · cross(x,y)`, the translation property of `cross(x,y)` on
generators of either block, the composite crossing `cross(x,y+z) = cross(x,y) · cross(x,z)@y`,
the block Yang–Baxter relation and the three-block decomposition.
-/

namespace BGL

variable {G : Type*} [Monoid G]

/-- `crossL x y = ∏_{t<y} (σ_{t+x} ⋯ σ_{t+1})` (0-based: letters `t+x-1, …, t`). -/
def crossL (x : ℕ) : ℕ → List ℕ
  | 0 => []
  | y + 1 => crossL x y ++ (dscL x).map (· + y)

def Cr (s : ℕ → G) (x y : ℕ) : G := wp s (crossL x y)

lemma mem_crossL {x y z : ℕ} (h : z ∈ crossL x y) : z + 2 ≤ x + y := by
  induction y with
  | zero => simp [crossL] at h
  | succ y ih =>
    simp only [crossL, List.mem_append, List.mem_map, mem_dscL] at h
    rcases h with h | ⟨d, hd, rfl⟩
    · have := ih h; omega
    · omega

lemma crossL_add (x y z : ℕ) : crossL x (y + z) = crossL x y ++ (crossL x z).map (· + y) := by
  induction z with
  | zero => simp [crossL]
  | succ z ih =>
    rw [← Nat.add_assoc, crossL, ih, crossL, List.map_append, List.map_map, List.append_assoc]
    congr 2; apply List.map_congr_left; intro a _; simp; omega

lemma Cr_sh (s : ℕ → G) (u x y : ℕ) : Cr (sh s u) x y = wp s ((crossL x y).map (· + u)) := by
  rw [Cr, wp_sh]

section
variable {s : ℕ → G} {K : ℕ}

lemma commute_lists (h : BR s K) {l l' : List ℕ} {a : ℕ}
    (hl : ∀ x ∈ l, x + 2 ≤ a) (hl' : ∀ y ∈ l', a ≤ y ∧ y < K) :
    Commute (wp s l) (wp s l') := by
  apply commute_wp_wp; intro x hx y hy
  have := hl x hx; have := hl' y hy
  exact h.cm (Or.inl (by omega)) (by omega) (by omega)

/-- `Δ_{x+y} = Δ_x · cross(x,y) · Δ_y`. -/
lemma Hw_add_cross' (h : BR s K) (x : ℕ) :
    ∀ y, x + y ≤ K + 1 → Hw s (x + y) = Hw s x * Cr s x y * Hw s y := by
  intro y
  induction y with
  | zero => intro _; simp [Cr, crossL]
  | succ y ih =>
    intro hxy
    rw [← Nat.add_assoc, Hw_succ, ih (by omega), D, show x + y = y + x by omega, dscL_add,
      wp_append, Cr, show Cr s x (y + 1) = wp s (crossL x y ++ (dscL x).map (· + y)) from rfl,
      wp_append, Hw_succ s y, D]
    have hc : Commute (Hw s y) (wp s ((dscL x).map (· + y))) := by
      apply commute_lists h (a := y)
      · intro z hz; exact mem_hwL hz
      · intro z hz; simp only [List.mem_map, mem_dscL] at hz; obtain ⟨d, hd, rfl⟩ := hz; omega
    calc Hw s x * wp s (crossL x y) * Hw s y * (wp s (List.map (· + y) (dscL x)) * wp s (dscL y))
        = Hw s x * wp s (crossL x y) * (Hw s y * wp s (List.map (· + y) (dscL x))) * wp s (dscL y) := by
          simp only [mul_assoc]
      _ = Hw s x * wp s (crossL x y) * (wp s (List.map (· + y) (dscL x)) * Hw s y) * wp s (dscL y) := by
          rw [hc.eq]
      _ = _ := by unfold Hw; simp only [mul_assoc]

lemma commute_Hw_H (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) : Commute (Hw s x) (H s x y) := by
  rw [Hw, H_def]; apply commute_lists h (a := x)
  · intro z hz; exact mem_hwL hz
  · intro z hz; simp only [List.mem_map] at hz; obtain ⟨d, hd, rfl⟩ := hz
    have := mem_hwL hd; omega

lemma Cr_succ (s : ℕ → G) (x y : ℕ) : Cr s x (y + 1) =
    Cr s x y * D (sh s y) x := by
  simp [Cr, crossL, D, wp_sh]

lemma Cr_horiz (h : BR s K) (x y z : ℕ) (hK : x + y + z ≤ K + 1) :
    Cr s (x + y) z = Cr (sh s x) y z * Cr s x z := by
  induction z with
  | zero => simp [Cr, crossL]
  | succ z ih =>
    rw [Cr_succ, Cr_succ, Cr_succ, ih (by omega)]
    have e : D (sh s z) (x + y) = D (sh (sh s x) z) y * D (sh s z) x := by
      rw [D, dscL_add, wp_append, wp_map]
      congr 2
      funext i
      simp only [sh_apply]
      congr 1
      omega
    rw [e]
    have hc : Commute (Cr s x z) (D (sh (sh s x) z) y) := by
      apply commute_wp_wp
      intro a ha b hb
      have := mem_crossL ha
      simp only [mem_dscL] at hb
      simp only [sh_apply]
      exact h.cm (Or.inl (by omega)) (by omega) (by omega)
    simp only [mul_assoc]
    rw [← mul_assoc (Cr s x z), hc.eq, mul_assoc]

lemma Cr_one_left (s : ℕ → G) (y : ℕ) : Cr s 1 y = A s y := by
  induction y with
  | zero => rfl
  | succ y ih => rw [Cr_succ, ih, A_succ]; simp [D_succ]

lemma Cr_one_right (s : ℕ → G) (x : ℕ) : Cr s x 1 = D s x := by
  rw [Cr_succ, sh_zero, show Cr s x 0 = 1 by rfl, one_mul]

lemma s_mul_Cr_left (h : BR s K) {x y i : ℕ} (hK : x + y ≤ K + 1)
    (hi : i + 2 ≤ x) : s i * Cr s x y = Cr s x y * s (i + y) := by
  induction y with
  | zero => simp [Cr, crossL]
  | succ y ih =>
    have e := s_mul_D (h.shift y) (m := x) (i := i) (by omega) (by omega)
    simp only [sh_apply] at e
    rw [Cr_succ, ← mul_assoc, ih (by omega), mul_assoc, e, ← mul_assoc]
    congr 2
    omega

lemma s_mul_Cr_right (h : BR s K) {x y i : ℕ} (hK : x + y ≤ K + 1)
    (hix : x ≤ i) (hi : i + 2 ≤ x + y) : s i * Cr s x y = Cr s x y * s (i - x) := by
  induction x generalizing i with
  | zero =>
    have e : Cr s 0 y = 1 := by
      clear hK hi
      induction y with
      | zero => rfl
      | succ y ih => rw [Cr_succ, ih, D_zero, mul_one]
    simp [e]
  | succ x ih =>
    rw [Cr_horiz h x 1 y hK, Cr_one_left]
    have e := A_mul_s (h.shift x) (m := y) (i := i - (x + 1)) (by omega) (by omega)
    simp only [sh_apply] at e
    rw [show i - (x + 1) + 1 + x = i by omega,
      show i - (x + 1) + x = i - 1 by omega] at e
    rw [← mul_assoc, ← e, mul_assoc, ih (by omega) (by omega) (by omega), ← mul_assoc]
    congr 2
    omega

lemma wp_mul_Cr_left (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) {l : List ℕ}
    (hl : ∀ i ∈ l, i + 2 ≤ x) : wp s l * Cr s x y = Cr s x y * wp s (l.map (· + y)) := by
  rw [wp_map]
  exact wp_slide (fun i hi => s_mul_Cr_left h hK (hl i hi))

lemma wp_mul_Cr_right (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) {l : List ℕ}
    (hl : ∀ i ∈ l, x ≤ i ∧ i + 2 ≤ x + y) : wp s l * Cr s x y = Cr s x y * wp s (l.map (· - x)) := by
  rw [wp_map]
  exact wp_slide (fun i hi => s_mul_Cr_right h hK (hl i hi).1 (hl i hi).2)

lemma H_mul_Cr_right (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) :
    H s x y * Cr s x y = Cr s x y * Hw s y := by
  rw [H_def, wp_mul_Cr_right h hK]
  · rw [Hw, List.map_map]
    conv_rhs => rw [← List.map_id (hwL y)]
    congr 2
    apply List.map_congr_left
    intro i _
    simp
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := mem_hwL hj
    omega

lemma H_mul_Cr_left (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) :
    Hw s x * Cr s x y = Cr s x y * H s y x := by
  rw [Hw, wp_mul_Cr_left h hK (fun _ => mem_hwL), H_def]

/-- Two-block decomposition `Δ_{x+y} = Δ_x Δ[x+1,x+y] cross(x,y)`. -/
lemma Hw_add_cross (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) (_h2 : 2 ≤ x + y) :
    Hw s (x + y) = Hw s x * H s x y * Cr s x y := by
  rw [Hw_add_cross' h x y hK, mul_assoc, ← H_mul_Cr_right h hK, ← mul_assoc]

/-- Block Yang–Baxter relation (cabled braid relation), at offset `0`. -/
lemma Cr_YB (h : BR s K) {x y z : ℕ} (hK : x + y + z ≤ K + 1) (_h2 : 2 ≤ x + (y + z)) :
    Cr s x y * wp s ((crossL x z).map (· + y)) * Cr s y z
      = wp s ((crossL y z).map (· + x)) * Cr s x z * wp s ((crossL x y).map (· + z)) := by
  have e1 : Cr s x y * wp s ((crossL x z).map (· + y)) = Cr s x (y + z) := by
    rw [Cr, Cr, ← wp_append, crossL_add]
  have e2 : Cr s x z * wp s ((crossL x y).map (· + z)) = Cr s x (y + z) := by
    rw [Cr, Cr, ← wp_append, ← crossL_add, Nat.add_comm]
  rw [e1, mul_assoc, e2, wp_mul_Cr_right h (by omega)]
  · congr 1
    rw [Cr, List.map_map]
    conv_lhs => rw [← List.map_id (crossL y z)]
    congr 1; apply List.map_congr_left; intro a _; simp
  · intro i hi; simp only [List.mem_map] at hi; obtain ⟨a, ha, rfl⟩ := hi
    have := mem_crossL ha; omega

end

section
variable {J : Type*} [Group J] {s : ℕ → J} {K : ℕ}

lemma Cr_conj_left (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) (_h2 : 2 ≤ x + y) {l : List ℕ}
    (hl : ∀ i ∈ l, i + 2 ≤ x) : (Cr s x y)⁻¹ * wp s l * Cr s x y = wp s (l.map (· + y)) := by
  rw [mul_assoc, wp_mul_Cr_left h hK hl, ← mul_assoc, inv_mul_cancel, one_mul]

lemma Cr_conj_right (h : BR s K) {x y : ℕ} (hK : x + y ≤ K + 1) (_h2 : 2 ≤ x + y) {l : List ℕ}
    (hl : ∀ i ∈ l, x ≤ i ∧ i + 2 ≤ x + y) : (Cr s x y)⁻¹ * wp s l * Cr s x y = wp s (l.map (· - x)) := by
  rw [mul_assoc, wp_mul_Cr_right h hK hl, ← mul_assoc, inv_mul_cancel, one_mul]

end

end BGL
```

### `BraidPositivePeriodic.lean`

```lean
import BraidCross
import BraidCase2

namespace BGL

variable {M : Type*} [Monoid M] {s : ℕ → M} {n : ℕ}

lemma D_pow_Bk_slide (h : BR s (n - 1)) (k u : ℕ) (ws : List ℕ) (hu : u + ws.sum + k ≤ n) :
    Bk s u ws * D s (n - 1) ^ k = D s (n - 1) ^ k * Bk s (u + k) ws := by
  have slide (j : ℕ) (l : List ℕ) (hl : ∀ i ∈ l, i + j + 2 ≤ n) :
      wp s l * D s (n - 1) ^ j = D s (n - 1) ^ j * wp s (l.map (· + j)) := by
    induction j generalizing l with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih l (fun i hi => by have := hl i hi; omega), mul_assoc]
      have e : wp s (l.map (· + j)) * D s (n - 1) =
          D s (n - 1) * wp s ((l.map (· + j)).map (· + 1)) := by
        rw [wp_map s (· + 1)]
        apply wp_slide
        intro i hi
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
        have := hl x hx
        exact s_mul_D h le_rfl (by omega)
      rw [e, ← mul_assoc, List.map_map]
      rfl
  rw [Bk, Bk, blkL_shift]
  exact slide k _ (fun i hi => by have := mem_blkL hi; omega)

lemma positive_complement (h : BR s (n - 1)) (hn : 2 ≤ n) :
    ∀ k m, m + k = n → Hw s m * D s (n - 1) ^ k = Hw s n * Hw s k := by
  intro k
  induction k with
  | zero => intro m hm; simp at hm; subst hm; simp
  | succ k ih =>
    intro m hm
    let U := wp s ((dscL k).map (· + m))
    have hρ : D s (n - 1) = U * D s m := by
      rw [D, show n - 1 = m + k by omega, dscL_add, wp_append]; rfl
    have hc : Commute (Hw s m) U := by
      apply commute_lists h (a := m)
      · intro x hx; exact mem_hwL hx
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        simp only [mem_dscL] at hz
        omega
    have hU : U * Hw s n = Hw s n * A s k := by
      have e : A s k = wp (reflect s n) ((dscL k).map (· + m)) := by
        rw [A, ← dscL_map_rev, wp_map, wp_map]
        apply wp_congr
        intro x hx
        simp only [mem_dscL] at hx
        simp only [reflect]
        congr 1
        omega
      rw [e]
      apply wp_slide
      intro i hi
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hi
      simp only [mem_dscL] at hz
      have hf := Hw_mul_s h (m := n) (i := n - 2 - (z + m)) (by omega) (by omega)
      rw [show n - 2 - (n - 2 - (z + m)) = z + m by omega] at hf
      exact hf.symm
    calc Hw s m * D s (n - 1) ^ (k + 1)
        = U * (Hw s (m + 1) * D s (n - 1) ^ k) := by
          rw [pow_succ', hρ, ← mul_assoc, ← mul_assoc, hc.eq, Hw_succ]
          simp only [mul_assoc]
      _ = U * (Hw s n * Hw s k) := by rw [ih (m+1) (by omega)]
      _ = Hw s n * Hw s (k + 1) := by
        rw [← mul_assoc, hU, mul_assoc, ← Hw_succ_A h (by omega)]

lemma positive_rho_full (h : BR s (n - 1)) (hn : 2 ≤ n) :
    D s (n - 1) ^ n = Hw s n ^ 2 := by
  simpa [pow_two] using positive_complement h hn n 0 (by simp)

/-- Rotation by the last l strands, with the two internal half twists exposed. -/
lemma rho_rotation (h : BR s (n - 1)) :
    ∀ l x, x + l = n → D s (n - 1) ^ l = H s x l * Cr s x l * Hw s l := by
  intro l
  induction l with
  | zero => intro x _; simp [H, Cr, crossL]
  | succ l ih =>
    intro x hx
    have hsplit : D s (n - 1) = D (sh s x) l * D s x := by
      rw [show n - 1 = x + l by omega, D, dscL_add, wp_append, ← wp_sh]
      rfl
    have hc : Commute (D s x) (H s (x + 1) l) := by
      apply commute_wp_wp
      intro a ha b hb
      simp only [mem_dscL] at ha
      have := mem_hwL hb
      simp only [sh_apply]
      exact h.cm (Or.inl (by omega)) (by omega) (by omega)
    have ht : D (sh s x) l * H s (x + 1) l = H s x (l + 1) := by
      change D (sh s x) l * Hw (sh s (x + 1)) l = Hw (sh s x) (l + 1)
      rw [Hw_succ_right (h.shift x) (by omega), H, sh_sh, Nat.add_comm x 1]
    have hm : D s x * Cr s (x + 1) l = Cr s x (l + 1) * A s l := by
      rw [Nat.add_comm x 1, Cr_horiz h 1 x l (by omega), Cr_one_left, ← mul_assoc,
        ← Cr_one_right s x]
      congr 1
      rw [Cr_sh, Cr, Cr, ← wp_append, ← crossL_add, Nat.one_add]
    calc D s (n - 1) ^ (l + 1)
        = (D (sh s x) l * (D s x * H s (x + 1) l)) * Cr s (x + 1) l * Hw s l := by
          rw [pow_succ', ih (x+1) (by omega), hsplit]
          simp only [mul_assoc]
      _ = H s x (l + 1) * (D s x * Cr s (x + 1) l) * Hw s l := by
        rw [hc.eq, ← mul_assoc (D (sh s x) l), ht]
        simp only [mul_assoc]
      _ = H s x (l + 1) * Cr s x (l + 1) * Hw s (l + 1) := by
        rw [hm, Hw_succ_A h (by omega)]
        simp only [mul_assoc]

lemma rho_overlap (h : BR s (n - 1)) (p q l : ℕ) (hn : p + q + l = n) :
    H s p (q + l) * Hw s (p + l) = Bk s 0 [p, q] * D s (n - 1) ^ l := by
  have hY : H s p (q + l) = H s p q * H s (p + q) l * Cr (sh s p) q l := by
    unfold H
    rw [Hw_add_cross' (h.shift p) q l (by omega), mul_assoc,
      ← H_mul_Cr_right (h.shift p) (by omega), ← mul_assoc, H, sh_sh, Nat.add_comm q p]
  have hX := Hw_add_cross' h p l (by omega)
  have c1 := commute_Hw_H h (x := p) (y := q) (by omega)
  have c2 : Commute (Hw s p) (H s (p + q) l) := by
    apply commute_wp_wp
    intro a ha b hb
    have := mem_hwL ha
    have := mem_hwL hb
    simp only [sh_apply]
    exact h.cm (Or.inl (by omega)) (by omega) (by omega)
  have c3 : Commute (Hw s p) (Cr (sh s p) q l) := by
    apply commute_wp_wp
    intro a ha b hb
    have := mem_hwL ha
    have := mem_crossL hb
    simp only [sh_apply]
    exact h.cm (Or.inl (by omega)) (by omega) (by omega)
  rw [hY, hX, Bk_cons, Nat.zero_add, H_zero, Bk_cons, Bk_nil, mul_one,
    rho_rotation h l (p + q) hn, Cr_horiz h p q l (by omega)]
  calc (H s p q * H s (p + q) l * Cr (sh s p) q l) * (Hw s p * Cr s p l * Hw s l)
      = H s p q * (H s (p + q) l * (Cr (sh s p) q l * Hw s p)) * Cr s p l * Hw s l := by
        simp only [mul_assoc]
    _ = (Hw s p * H s p q) * (H s (p + q) l * (Cr (sh s p) q l * Cr s p l) * Hw s l) := by
      rw [← c3.eq, ← mul_assoc (H s (p + q) l), ← c2.eq]
      simp only [mul_assoc, c1.symm.left_comm]


lemma fullTwist_commutes (h : BR s (n - 1)) {l : List ℕ} (hl : ∀ i ∈ l, i + 2 ≤ n) :
    Commute (Hw s n ^ 2) (wp s l) := by
  apply commute_wp
  intro i hi
  have hi' := hl i hi
  show Hw s n ^ 2 * s i = s i * Hw s n ^ 2
  rw [pow_two, mul_assoc, Hw_mul_s h (by omega) hi', ← mul_assoc,
    Hw_mul_s h (by omega) (by omega), show n - 2 - (n - 2 - i) = i by omega, mul_assoc]

lemma fullTwist_commutes_H (h : BR s (n - 1)) {u w : ℕ} (huw : u + w ≤ n) :
    Commute (Hw s n ^ 2) (H s u w) := by
  rw [H_def]
  apply fullTwist_commutes h
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have := mem_hwL hj
  omega

/-- Move each small block pattern through the surviving run and extract one full twist. -/
lemma positive_block_pow (h : BR s (n - 1)) (hn : 2 ≤ n) (ws : List ℕ) (t : ℕ)
    (ht : (t + 1) * ws.sum ≤ n) :
    (Bk s 0 ws * D s (n - 1) ^ (n - ws.sum)) ^ (t + 1) =
      (Hw s n ^ 2) ^ t * (D s (n - 1) ^ (n - (t + 1) * ws.sum) *
        Bk s (n - (t + 1) * ws.sum) (repL (t + 1) ws)) := by
  have hw : ws.sum ≤ n := by nlinarith
  let rho := D s (n - 1)
  let full := Hw s n ^ 2
  have cB : Commute full (Bk s 0 ws) := by
    apply fullTwist_commutes h
    intro i hi
    have := mem_blkL hi
    omega
  have cR : Commute full rho := by
    apply fullTwist_commutes h
    intro i hi
    simp only [mem_dscL] at hi
    omega
  change (Bk s 0 ws * rho ^ (n - ws.sum)) ^ (t + 1) =
    full ^ t * (rho ^ (n - (t + 1) * ws.sum) * Bk s (n - (t + 1) * ws.sum) (repL (t + 1) ws))
  induction t with
  | zero =>
    simpa [rho, repL, Nat.zero_add] using D_pow_Bk_slide h (n - ws.sum) 0 ws (by omega)
  | succ t ih =>
    have hp : (t + 1) * ws.sum ≤ n := by nlinarith
    let v := n - (t + 1) * ws.sum
    let u := n - (t + 1 + 1) * ws.sum
    have huv : u + ws.sum = v := by
      dsimp [u, v]
      rw [Nat.succ_mul] at ht ⊢
      omega
    have hex : n - ws.sum + v = n + u := by omega
    have e : rho ^ (n - ws.sum) * rho ^ v = full * rho ^ u := by
      rw [← pow_add, hex, pow_add, positive_rho_full h hn]
    have c : Commute (full ^ t) (Bk s 0 ws * rho ^ (n - ws.sum)) :=
      ((cB.mul_right (cR.pow_right _)).pow_left _)
    rw [pow_succ', ih hp]
    change (Bk s 0 ws * rho ^ (n - ws.sum)) *
        (full ^ t * (rho ^ v * Bk s v (repL (t + 1) ws))) =
      full ^ (t + 1) * (rho ^ u * Bk s u (repL (t + 1 + 1) ws))
    calc (Bk s 0 ws * rho ^ (n - ws.sum)) * (full ^ t * (rho ^ v * Bk s v (repL (t + 1) ws)))
        = full ^ t * (Bk s 0 ws * (rho ^ (n - ws.sum) * rho ^ v) * Bk s v (repL (t + 1) ws)) := by
          rw [← mul_assoc, ← c.eq]
          simp only [mul_assoc]
      _ = (full ^ t * full) * ((Bk s 0 ws * rho ^ u) * Bk s v (repL (t + 1) ws)) := by
        rw [e]
        simp only [mul_assoc, cB.symm.left_comm]
      _ = _ := by
        rw [← pow_succ, D_pow_Bk_slide h u 0 ws (by omega), Nat.zero_add,
          mul_assoc (rho ^ u), repL_succ' (t + 1) ws, Bk_append s u ws, huv]

lemma caseI_positive (h : BR s (n - 1)) (hn : 2 ≤ n) (p q m : ℕ)
    (hm : m * (p + q) = n) :
    (Hw s (n - q) * H s p (n - p)) ^ m = (H s p (n - p) * Hw s (n - q)) ^ m := by
  have closed (s' : ℕ → M) (h' : BR s' (n - 1)) (p' q' : ℕ) (hm' : m * (p' + q') = n) :
      (H s' p' (n - p') * Hw s' (n - q')) ^ m =
        (Hw s' n ^ 2) ^ (m - 1) * Bk s' 0 (repL m [p', q']) := by
    rcases m with _ | t
    · simp at hm'; omega
    have hpq : p' + q' ≤ n := by nlinarith
    have ho := rho_overlap h' p' q' (n - (p' + q')) (by omega)
    rw [show q' + (n - (p' + q')) = n - p' by omega,
      show p' + (n - (p' + q')) = n - q' by omega] at ho
    rw [ho]
    have e := positive_block_pow h' hn [p', q'] t (by simp [hm'])
    simpa [hm'] using e
  have hpq : p + q ≤ n := by
    rcases m with _ | t
    · simp at hm; omega
    · nlinarith
  have e := closed (reflect s n) h.reflect q p (by rwa [Nat.add_comm q p])
  have hsum : (repL m [q, p]).sum = n := by rw [repL_sum]; simpa [Nat.add_comm] using hm
  rw [reflect_H h hn (by omega), reflect_Hw h hn (by omega), reflect_full h hn,
    Bk_reflect h hn 0 _ (by omega), hsum, repL_reverse_pair] at e
  rw [show n - q - (n - q) = 0 by omega, H_zero, show n - (n - p) = p by omega,
    Nat.sub_zero, Nat.sub_self] at e
  exact e.trans (closed s h p q hm).symm

lemma caseII_positive (h : BR s (n - 1)) (hn : 2 ≤ n) (p k : ℕ) (hk : 0 < k)
    (hm : (1 + 2 * k) * p = n) :
    alt (1 + 2 * k) (Hw s (n - p)) (H s p (n - p)) =
      alt (1 + 2 * k) (H s p (n - p)) (Hw s (n - p)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hm2 : (t + 1) * (p + p) + p = n := by nlinarith
  have hp : p + p ≤ n := by nlinarith
  have closed (s' : ℕ → M) (h' : BR s' (n - 1)) :
      alt (1 + 2 * (t + 1)) (Hw s' (n - p)) (H s' p (n - p)) =
        (Hw s' n ^ 2) ^ t * (Hw s' n * Bk s' 0 (repL (1 + 2 * (t + 1)) [p])) := by
    rw [Nat.add_comm 1, alt, alt_two_mul]
    have ho := rho_overlap h' p p (n - (p + p)) (by omega)
    rw [show p + (n - (p + p)) = n - p by omega] at ho
    rw [ho]
    have e := positive_block_pow h' hn [p,p] t (by simp; omega)
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at e
    rw [show n - (t + 1) * (p + p) = p by omega] at e
    rw [e]
    have cX : Commute (Hw s' n ^ 2) (Hw s' (n - p)) := by
      rw [← H_zero s' (n - p)]
      exact fullTwist_commutes_H h' (by omega)
    have hpwr := (cX.pow_left t).eq
    rw [← mul_assoc, ← hpwr, mul_assoc, ← mul_assoc (Hw s' (n - p)),
      positive_complement h' hn p (n - p) (by omega), mul_assoc (Hw s' n)]
    congr 2
    have hr (j : ℕ) : repL j [p,p] = repL (2 * j) [p] := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [repL, ih, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, repL, repL, List.append_assoc]
        rfl
    have hrep : repL (2 * (t + 1) + 1) [p] = p :: repL (2 * (t+1)) [p] := by
      rw [repL_succ']
      rfl
    rw [hr, hrep, Bk_cons, H_zero, Nat.zero_add]
  have hs : (repL (1 + 2 * (t + 1)) [p]).sum = n := by rw [repL_sum]; simpa using hm
  have e := closed (reflect s n) h.reflect
  rw [reflect_Hw h hn (by omega), reflect_H h hn (by omega), reflect_full h hn,
    Bk_reflect h hn 0 _ (by omega), hs, repL_reverse_single] at e
  rw [show n - (n - p) = p by omega, show n - p - (n - p) = 0 by omega, H_zero,
    Nat.sub_zero, Nat.sub_self] at e
  exact (closed s h).trans e.symm

end BGL
```

### `BraidFat.lean`

```lean
import BraidCross
import Mathlib.Tactic.IntervalCases

/-!
# Braids on four fat strands

A width pattern `ws = (a, b, c, d)` cuts strands into four consecutive blocks.  A fat word
`w : List ℕ` (letters `0, 1, 2`) is evaluated by `fatL ws w`: letter `i` is the block crossing
of the blocks at positions `i, i+1`, after which the pattern is updated by `sw i`.
We prove that fat words satisfy the braid relations (`mv_F`), how block half twists move
through fat words (`hp_mul_F`), and the four-block decomposition of `Δ`.
-/

namespace BGL

/-- Quadruples. -/
abbrev Q (α : Type*) := α × α × α × α

def sw {α : Type*} : ℕ → Q α → Q α
  | 0, (a, b, c, d) => (b, a, c, d)
  | 1, (a, b, c, d) => (a, c, b, d)
  | 2, (a, b, c, d) => (a, b, d, c)
  | _, q => q

def permQ {α : Type*} : Q α → List ℕ → Q α
  | q, [] => q
  | q, i :: w => permQ (sw i q) w

def crossAt : Q ℕ → ℕ → List ℕ
  | (a, b, _, _), 0 => crossL a b
  | (a, b, c, _), 1 => (crossL b c).map (· + a)
  | (a, b, c, d), 2 => (crossL c d).map (· + (a + b))
  | _, _ => []

def fatL : Q ℕ → List ℕ → List ℕ
  | _, [] => []
  | ws, i :: w => crossAt ws i ++ fatL (sw i ws) w

def qsum : Q ℕ → ℕ
  | (a, b, c, d) => a + b + c + d

def qpos : Q ℕ → Prop
  | (a, b, c, d) => 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d

lemma qsum_sw (i : ℕ) (ws : Q ℕ) : qsum (sw i ws) = qsum ws := by
  obtain ⟨a, b, c, d⟩ := ws
  rcases i with _ | _ | _ | i <;> simp [sw, qsum] <;> omega

lemma qpos_sw (i : ℕ) (ws : Q ℕ) (h : qpos ws) : qpos (sw i ws) := by
  obtain ⟨a, b, c, d⟩ := ws
  rcases i with _ | _ | _ | i <;> simp [sw, qpos] at h ⊢ <;> omega

lemma fatL_append (ws : Q ℕ) (w1 w2 : List ℕ) :
    fatL ws (w1 ++ w2) = fatL ws w1 ++ fatL (permQ ws w1) w2 := by
  induction w1 generalizing ws with
  | nil => rfl
  | cons i w ih => simp [fatL, permQ, ih]

lemma mem_crossAt {ws : Q ℕ} {i x : ℕ} (h : x ∈ crossAt ws i) : x + 2 ≤ qsum ws := by
  obtain ⟨a, b, c, d⟩ := ws
  rcases i with _ | _ | _ | i
  · have := mem_crossL h; simp [qsum]; omega
  · simp only [crossAt, List.mem_map] at h; obtain ⟨y, hy, rfl⟩ := h
    have := mem_crossL hy; simp [qsum]; omega
  · simp only [crossAt, List.mem_map] at h; obtain ⟨y, hy, rfl⟩ := h
    have := mem_crossL hy; simp [qsum]; omega
  · simp [crossAt] at h

lemma mem_fatL {ws : Q ℕ} {w : List ℕ} {x : ℕ} (h : x ∈ fatL ws w) : x + 2 ≤ qsum ws := by
  induction w generalizing ws with
  | nil => simp [fatL] at h
  | cons i w ih =>
    simp only [fatL, List.mem_append] at h
    rcases h with h | h
    · exact mem_crossAt h
    · have := ih h; rwa [qsum_sw] at this

variable {G : Type*} [Monoid G]

def F (s : ℕ → G) (ws : Q ℕ) (w : List ℕ) : G := wp s (fatL ws w)

lemma F_append (s : ℕ → G) (ws : Q ℕ) (w1 w2 : List ℕ) :
    F s ws (w1 ++ w2) = F s ws w1 * F s (permQ ws w1) w2 := by
  simp [F, fatL_append]

lemma wp_map_congr (s : ℕ → G) {l : List ℕ} {f g : ℕ → ℕ} (h : ∀ x ∈ l, f x = g x) :
    wp s (l.map f) = wp s (l.map g) := by rw [List.map_congr_left h]

/-! ## Braid relations for fat words -/

section
variable {s : ℕ → G} {K : ℕ}

lemma F_YB01 (h : BR s K) (ws : Q ℕ) (hp : qpos ws) (hK : qsum ws ≤ K + 1) :
    F s ws [0, 1, 0] = F s ws [1, 0, 1] := by
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qpos, qsum] at hp hK
  have := Cr_YB h (x := a) (y := b) (z := c) (by omega) (by omega)
  simp only [F, fatL, crossAt, sw, List.append_nil, wp_append]
  simp only [Cr, mul_assoc] at this
  exact this

lemma Cr_YB_off (h : BR s K) {u x y z : ℕ} (hK : u + x + y + z ≤ K + 1) (h2 : 2 ≤ x + (y + z)) :
    wp s ((crossL x y).map (· + u)) * wp s ((crossL x z).map (· + (u + y)))
      * wp s ((crossL y z).map (· + u))
      = wp s ((crossL y z).map (· + (u + x))) * wp s ((crossL x z).map (· + u))
        * wp s ((crossL x y).map (· + (u + z))) := by
  have := Cr_YB (h.shift u) (x := x) (y := y) (z := z) (by omega) h2
  simp only [Cr, wp_sh, List.map_map] at this
  have e : ∀ (l : List ℕ) (k : ℕ), List.map ((· + u) ∘ (· + k)) l = l.map (· + (u + k)) := by
    intro l k; apply List.map_congr_left; intro a _; simp; omega
  rw [e, e, e] at this
  exact this

lemma F_YB12 (h : BR s K) (ws : Q ℕ) (hp : qpos ws) (hK : qsum ws ≤ K + 1) :
    F s ws [1, 2, 1] = F s ws [2, 1, 2] := by
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qpos, qsum] at hp hK
  have := Cr_YB_off h (u := a) (x := b) (y := c) (z := d) (by omega) (by omega)
  simp only [F, fatL, crossAt, sw, List.append_nil, wp_append]
  simp only [mul_assoc] at this
  exact this

lemma F_comm02 (h : BR s K) (ws : Q ℕ) (hK : qsum ws ≤ K + 1) :
    F s ws [0, 2] = F s ws [2, 0] := by
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qsum] at hK
  simp only [F, fatL, crossAt, sw, List.append_nil, wp_append]
  rw [show (fun x => x + (b + a)) = (fun x => x + (a + b)) by funext x; omega]
  apply Commute.eq
  apply commute_lists h (a := a + b)
  · intro x hx; exact mem_crossL hx
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    have := mem_crossL hy; omega

/-- One braid move inside a fat word. -/
def mv : ℕ → List ℕ → List ℕ
  | 0, a :: b :: c :: t =>
      if a = c ∧ (b = a + 1 ∨ a = b + 1) then b :: a :: b :: t
      else if a + 2 ≤ b ∨ b + 2 ≤ a then b :: a :: c :: t else a :: b :: c :: t
  | 0, [a, b] => if a + 2 ≤ b ∨ b + 2 ≤ a then [b, a] else [a, b]
  | 0, w => w
  | _ + 1, [] => []
  | k + 1, a :: t => a :: mv k t

def mvs : List ℕ → List ℕ → List ℕ
  | [], w => w
  | k :: ks, w => mvs ks (mv k w)

lemma mem_mv : ∀ (k : ℕ) (w : List ℕ) (x : ℕ), x ∈ mv k w → x ∈ w := by
  intro k
  induction k with
  | zero =>
    intro w x hx
    match w, hx with
    | a :: b :: c :: t, hx =>
      simp only [mv] at hx; split_ifs at hx <;> simp only [List.mem_cons] at hx ⊢ <;> tauto
    | [a, b], hx =>
      simp only [mv] at hx; split_ifs at hx <;> simp only [List.mem_cons] at hx ⊢ <;> tauto
    | [], hx => exact hx
    | [a], hx => exact hx
  | succ k ih =>
    intro w x hx
    match w, hx with
    | [], hx => exact hx
    | a :: t, hx =>
      simp only [mv, List.mem_cons] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (ih t x hx)

lemma F_cons (s : ℕ → G) (ws : Q ℕ) (i : ℕ) (w : List ℕ) :
    F s ws (i :: w) = wp s (crossAt ws i) * F s (sw i ws) w := by simp [F, fatL]

lemma F_three (s : ℕ → G) (ws : Q ℕ) (x y z : ℕ) (t : List ℕ) :
    F s ws (x :: y :: z :: t) = F s ws [x, y, z] * F s (permQ ws [x, y, z]) t := by
  rw [show x :: y :: z :: t = [x, y, z] ++ t from rfl, F_append]

lemma F_two (s : ℕ → G) (ws : Q ℕ) (x y : ℕ) (t : List ℕ) :
    F s ws (x :: y :: t) = F s ws [x, y] * F s (permQ ws [x, y]) t := by
  rw [show x :: y :: t = [x, y] ++ t from rfl, F_append]

lemma mv_F (h : BR s K) : ∀ (k : ℕ) (w : List ℕ) (ws : Q ℕ), (∀ i ∈ w, i ≤ 2) → qpos ws →
    qsum ws ≤ K + 1 → F s ws (mv k w) = F s ws w := by
  intro k
  induction k with
  | zero =>
    intro w ws hw hp hK
    obtain ⟨a', b', c', d'⟩ := ws
    match w, hw with
    | a :: b :: c :: t, hw =>
      have ha : a ≤ 2 := hw a (by simp)
      have hb : b ≤ 2 := hw b (by simp)
      simp only [mv]
      have hc : c ≤ 2 := hw c (by simp)
      split_ifs with h1 h2
      · have : (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1)
            ∨ (a = 2 ∧ b = 1 ∧ c = 2) := by omega
        rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · rw [F_three s _ 1 0 1 t, F_three s _ 0 1 0 t, F_YB01 h _ hp hK]; rfl
        · rw [F_three s _ 2 1 2 t, F_three s _ 1 2 1 t, F_YB12 h _ hp hK]; rfl
        · rw [F_three s _ 0 1 0 t, F_three s _ 1 0 1 t, F_YB01 h _ hp hK]; rfl
        · rw [F_three s _ 1 2 1 t, F_three s _ 2 1 2 t, F_YB12 h _ hp hK]; rfl
      · have : (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [F_two s _ 2 0 (c :: t), F_two s _ 0 2 (c :: t), F_comm02 h _ hK]; rfl
        · rw [F_two s _ 0 2 (c :: t), F_two s _ 2 0 (c :: t), F_comm02 h _ hK]; rfl
      · rfl
    | [a, b], hw =>
      have ha : a ≤ 2 := hw a (by simp)
      have hb : b ≤ 2 := hw b (by simp)
      simp only [mv]
      split_ifs with h2
      · have : (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (F_comm02 h _ hK).symm
        · exact F_comm02 h _ hK
      · rfl
    | [], _ => rfl
    | [a], _ => rfl
  | succ k ih =>
    intro w ws hw hp hK
    match w, hw with
    | [], _ => rfl
    | a :: t, hw =>
      simp only [mv]
      rw [F_cons, F_cons, ih t (sw a ws) (fun i hi => hw i (by simp [hi])) (qpos_sw a ws hp)
        (by rwa [qsum_sw])]

lemma mvs_F (h : BR s K) : ∀ (ks w : List ℕ) (ws : Q ℕ), (∀ i ∈ w, i ≤ 2) → qpos ws →
    qsum ws ≤ K + 1 → F s ws (mvs ks w) = F s ws w := by
  intro ks
  induction ks with
  | nil => intro w ws _ _ _; rfl
  | cons k ks ih =>
    intro w ws hw hp hK
    rw [mvs, ih (mv k w) ws (fun i hi => hw i (mem_mv k w i hi)) hp hK, mv_F h k w ws hw hp hK]

end

/-! ## Block half twists and their transport through fat words -/

def off : Q ℕ → ℕ → ℕ
  | _, 0 => 0
  | (a, _, _, _), 1 => a
  | (a, b, _, _), 2 => a + b
  | (a, b, c, _), _ => a + b + c

def wid : Q ℕ → ℕ → ℕ
  | (a, _, _, _), 0 => a
  | (_, b, _, _), 1 => b
  | (_, _, c, _), 2 => c
  | (_, _, _, d), _ => d

/-- The half twist of the block at position `j`. -/
def hb (s : ℕ → G) (ws : Q ℕ) (j : ℕ) : G := H s (off ws j) (wid ws j)

section
variable {J : Type*} [Group J]

/-- Product of powers of four elements. -/
def P4 (x0 x1 x2 x3 : J) (e : Q ℤ) : J := x0 ^ e.1 * x1 ^ e.2.1 * x2 ^ e.2.2.1 * x3 ^ e.2.2.2

/-- Product of powers of the four block half twists. -/
def hp (s : ℕ → J) (ws : Q ℕ) (e : Q ℤ) : J := P4 (hb s ws 0) (hb s ws 1) (hb s ws 2) (hb s ws 3) e

lemma conjZpow (g x : J) (e : ℤ) : g⁻¹ * x ^ e * g = (g⁻¹ * x * g) ^ e := by
  let φ : J →* J :=
    { toFun := fun y => g⁻¹ * y * g
      map_one' := by group
      map_mul' := by intro a b; group }
  exact (map_zpow φ x e)

lemma conj_P4 (g x0 x1 x2 x3 : J) (e : Q ℤ) :
    g⁻¹ * P4 x0 x1 x2 x3 e * g
      = P4 (g⁻¹ * x0 * g) (g⁻¹ * x1 * g) (g⁻¹ * x2 * g) (g⁻¹ * x3 * g) e := by
  simp only [P4, ← conjZpow]; group

lemma P4_sw0 {y0 y1 y2 y3 : J} (c : Commute y0 y1) (e : Q ℤ) :
    P4 y1 y0 y2 y3 e = P4 y0 y1 y2 y3 (sw 0 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4, sw]; rw [(c.zpow_zpow e1 e0).symm.eq]

lemma P4_sw1 {y0 y1 y2 y3 : J} (c : Commute y1 y2) (e : Q ℤ) :
    P4 y0 y2 y1 y3 e = P4 y0 y1 y2 y3 (sw 1 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4, sw]; rw [mul_assoc (y0 ^ e0), (c.zpow_zpow e2 e1).symm.eq, ← mul_assoc]

lemma P4_sw2 {y0 y1 y2 y3 : J} (c : Commute y2 y3) (e : Q ℤ) :
    P4 y0 y1 y3 y2 e = P4 y0 y1 y2 y3 (sw 2 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4, sw]; rw [mul_assoc (y0 ^ e0 * y1 ^ e1), (c.zpow_zpow e3 e2).symm.eq, ← mul_assoc]

lemma P4_mul {x0 x1 x2 x3 : J} (c01 : Commute x0 x1) (c02 : Commute x0 x2) (c03 : Commute x0 x3)
    (c12 : Commute x1 x2) (c13 : Commute x1 x3) (c23 : Commute x2 x3) (e f : Q ℤ) :
    P4 x0 x1 x2 x3 e * P4 x0 x1 x2 x3 f = P4 x0 x1 x2 x3 (e + f) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  obtain ⟨f0, f1, f2, f3⟩ := f
  simp only [P4, Prod.mk_add_mk, zpow_add, mul_assoc]
  rw [(c03.zpow_zpow f0 e3).symm.left_comm, (c02.zpow_zpow f0 e2).symm.left_comm,
    (c01.zpow_zpow f0 e1).symm.left_comm, (c13.zpow_zpow f1 e3).symm.left_comm,
    (c12.zpow_zpow f1 e2).symm.left_comm, (c23.zpow_zpow f2 e3).symm.left_comm]

lemma P4_rev {y0 y1 y2 y3 : J} (c01 : Commute y0 y1) (c02 : Commute y0 y2) (c03 : Commute y0 y3)
    (c12 : Commute y1 y2) (c13 : Commute y1 y3) (c23 : Commute y2 y3) (e : Q ℤ) :
    P4 y3 y2 y1 y0 e = P4 y0 y1 y2 y3 (e.2.2.2, e.2.2.1, e.2.1, e.1) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  rw [P4_sw0 c23, P4_sw1 c13, P4_sw0 c12, P4_sw2 c03, P4_sw1 c02, P4_sw0 c01]
  rfl

end

section
variable {s : ℕ → G} {K : ℕ}

lemma hb_mem {ws : Q ℕ} {j x : ℕ} (h : x ∈ (hwL (wid ws j)).map (· + off ws j)) :
    off ws j ≤ x ∧ x + 2 ≤ off ws j + wid ws j := by
  simp only [List.mem_map] at h; obtain ⟨y, hy, rfl⟩ := h; have := mem_hwL hy; omega

lemma hb_comm (h : BR s K) (ws : Q ℕ) (hK : qsum ws ≤ K + 1) {i j : ℕ} (hij : i < j) (hj : j ≤ 3) :
    Commute (hb s ws i) (hb s ws j) := by
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qsum] at hK
  rw [hb, hb, H_def, H_def]
  apply commute_lists h (a := off (a, b, c, d) j)
  · intro x hx; have := hb_mem hx
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | _ | j <;>
      simp only [off, wid] at this ⊢ <;> omega
  · intro x hx; have := hb_mem hx
    rcases j with _ | _ | _ | _ | j <;> simp only [off, wid] at this ⊢ <;> omega

end

section
variable {J : Type*} [Group J] {s : ℕ → J} {K : ℕ}

lemma hp_mul (h : BR s K) (ws : Q ℕ) (hK : qsum ws ≤ K + 1) (e f : Q ℤ) :
    hp s ws e * hp s ws f = hp s ws (e + f) :=
  P4_mul (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega))
    (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega))
    (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega)) e f

lemma hp_zero (s : ℕ → J) (ws : Q ℕ) : hp s ws 0 = 1 := by
  simp [hp, P4]

lemma hp_inv (h : BR s K) (ws : Q ℕ) (hK : qsum ws ≤ K + 1) (e : Q ℤ) :
    (hp s ws e)⁻¹ = hp s ws (-e) := by
  rw [inv_eq_iff_mul_eq_one, hp_mul h ws hK]; simp [hp, P4]

/-- Crossing at offset `u` of blocks of widths `x, y`: the left half twist moves right. -/
lemma crossu_left (h : BR s K) {u x y : ℕ} (hK : u + x + y ≤ K + 1) (h2 : 2 ≤ x + y) :
    (wp s ((crossL x y).map (· + u)))⁻¹ * H s u x * wp s ((crossL x y).map (· + u)) = H s (u + y) x := by
  have hs := h.shift u
  have := Cr_conj_left hs (x := x) (y := y) (l := hwL x) (by omega) h2 (fun i hi => mem_hwL hi)
  rw [Cr_sh, wp_sh, wp_sh, List.map_map] at this
  rw [H_def, H_def, this]; apply wp_map_congr; intro z _; simp; omega

lemma crossu_right (h : BR s K) {u x y : ℕ} (hK : u + x + y ≤ K + 1) (h2 : 2 ≤ x + y) :
    (wp s ((crossL x y).map (· + u)))⁻¹ * H s (u + x) y * wp s ((crossL x y).map (· + u)) = H s u y := by
  have hs := h.shift u
  have := Cr_conj_right hs (x := x) (y := y) (l := (hwL y).map (· + x)) (by omega) h2
    (fun i hi => by simp only [List.mem_map] at hi; obtain ⟨z, hz, rfl⟩ := hi
                    have := mem_hwL hz; omega)
  rw [Cr_sh, wp_sh, wp_sh, List.map_map, List.map_map] at this
  rw [H_def, H_def]
  rw [show (hwL y).map (· + (u + x)) = (hwL y).map ((· + u) ∘ (· + x)) by
    apply List.map_congr_left; intro z _; simp; omega, this, List.map_map]
  apply wp_map_congr; intro z _; simp

lemma crossu_out (h : BR s K) {u x y v w : ℕ} (hK : u + x + y ≤ K + 1) (hvK : v + w ≤ K + 1)
    (hout : v + w ≤ u ∨ u + x + y ≤ v) :
    (wp s ((crossL x y).map (· + u)))⁻¹ * H s v w * wp s ((crossL x y).map (· + u)) = H s v w := by
  have : Commute (H s v w) (wp s ((crossL x y).map (· + u))) := by
    rw [H_def]; apply commute_wp_wp; intro i hi j hj
    simp only [List.mem_map] at hi hj
    obtain ⟨a, ha, rfl⟩ := hi; obtain ⟨b, hb, rfl⟩ := hj
    have := mem_hwL ha; have := mem_crossL hb
    exact h.cm (by omega) (by omega) (by omega)
  rw [mul_assoc, this.eq]; group

/-- One fat crossing: `hp(e) · C_i = C_i · hp(sw_i e)` on the updated pattern. -/
lemma hp_mul_cross (h : BR s K) (ws : Q ℕ) (hp' : qpos ws) (hK : qsum ws ≤ K + 1) {i : ℕ}
    (hi : i ≤ 2) (e : Q ℤ) :
    hp s ws e * wp s (crossAt ws i) = wp s (crossAt ws i) * hp s (sw i ws) (sw i e) := by
  suffices hc : (wp s (crossAt ws i))⁻¹ * hp s ws e * wp s (crossAt ws i) = hp s (sw i ws) (sw i e) by
    rw [← hc]; group
  have hK' : qsum (sw i ws) ≤ K + 1 := by rwa [qsum_sw]
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qpos, qsum] at hp' hK hK'
  rw [hp, conj_P4]
  interval_cases i
  · have e0 : crossL a b = (crossL a b).map (· + 0) := by simp only [Nat.add_zero, List.map_id']
    have c01 := hb_comm h (b, a, c, d) hK' (i := 0) (j := 1) (by omega) (by omega)
    simp only [hb, off, wid] at c01
    simp only [crossAt, hb, off, wid]
    rw [e0, show H s 0 a = H s (0 + 0) a by rfl, crossu_left h (by omega) (by omega),
      show H s a b = H s (0 + a) b by rw [Nat.zero_add], crossu_right h (by omega) (by omega),
      crossu_out h (v := a + b) (w := c) (by omega) (by omega) (Or.inr (by omega)),
      crossu_out h (v := a + b + c) (w := d) (by omega) (by omega) (Or.inr (by omega))]
    simp only [Nat.zero_add]
    rw [P4_sw0 c01]
    simp only [hp, hb, sw, off, wid]
    rw [Nat.add_comm b a]
  · have c12 := hb_comm h (a, c, b, d) hK' (i := 1) (j := 2) (by omega) (by omega)
    simp only [hb, off, wid] at c12
    simp only [crossAt, hb, off, wid]
    rw [crossu_out h (v := 0) (w := a) (by omega) (by omega) (Or.inl (by omega)),
      crossu_left h (by omega) (by omega), crossu_right h (by omega) (by omega),
      crossu_out h (v := a + b + c) (w := d) (by omega) (by omega) (Or.inr (by omega))]
    rw [P4_sw1 c12]
    simp only [hp, hb, sw, off, wid]
    rw [show a + c + b = a + b + c by omega]
  · have c23 := hb_comm h (a, b, d, c) hK' (i := 2) (j := 3) (by omega) (by omega)
    simp only [hb, off, wid] at c23
    simp only [crossAt, hb, off, wid]
    rw [crossu_out h (v := 0) (w := a) (by omega) (by omega) (Or.inl (by omega)),
      crossu_out h (v := a) (w := b) (by omega) (by omega) (Or.inl (by omega)),
      crossu_left h (by omega) (by omega), crossu_right h (by omega) (by omega)]
    rw [P4_sw2 c23]
    simp only [hp, hb, sw, off, wid]

lemma hp_mul_F (h : BR s K) : ∀ (w : List ℕ) (ws : Q ℕ) (e : Q ℤ), (∀ i ∈ w, i ≤ 2) → qpos ws →
    qsum ws ≤ K + 1 → hp s ws e * F s ws w = F s ws w * hp s (permQ ws w) (permQ e w) := by
  intro w
  induction w with
  | nil => intro ws e _ _ _; simp [F, fatL, permQ]
  | cons i w ih =>
    intro ws e hw hp' hK
    rw [F_cons, ← mul_assoc, hp_mul_cross h ws hp' hK (hw i (by simp)), mul_assoc,
      ih (sw i ws) (sw i e) (fun j hj => hw j (by simp [hj])) (qpos_sw i ws hp') (by rwa [qsum_sw]),
      ← mul_assoc]
    rfl

end

/-- Product of powers of four elements. -/
def P4N (x0 x1 x2 x3 : G) (e : Q ℕ) : G := x0 ^ e.1 * x1 ^ e.2.1 * x2 ^ e.2.2.1 * x3 ^ e.2.2.2

/-- Product of powers of the four block half twists. -/
def hpN (s : ℕ → G) (ws : Q ℕ) (e : Q ℕ) : G := P4N (hb s ws 0) (hb s ws 1) (hb s ws 2) (hb s ws 3) e

lemma P4N_sw0 {y0 y1 y2 y3 : G} (c : Commute y0 y1) (e : Q ℕ) :
    P4N y1 y0 y2 y3 e = P4N y0 y1 y2 y3 (sw 0 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4N, sw]; rw [(c.pow_pow e1 e0).symm.eq]

lemma P4N_sw1 {y0 y1 y2 y3 : G} (c : Commute y1 y2) (e : Q ℕ) :
    P4N y0 y2 y1 y3 e = P4N y0 y1 y2 y3 (sw 1 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4N, sw]; rw [mul_assoc (y0 ^ e0), (c.pow_pow e2 e1).symm.eq, ← mul_assoc]

lemma P4N_sw2 {y0 y1 y2 y3 : G} (c : Commute y2 y3) (e : Q ℕ) :
    P4N y0 y1 y3 y2 e = P4N y0 y1 y2 y3 (sw 2 e) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  simp only [P4N, sw]; rw [mul_assoc (y0 ^ e0 * y1 ^ e1), (c.pow_pow e3 e2).symm.eq, ← mul_assoc]

lemma P4N_mul {x0 x1 x2 x3 : G} (c01 : Commute x0 x1) (c02 : Commute x0 x2) (c03 : Commute x0 x3)
    (c12 : Commute x1 x2) (c13 : Commute x1 x3) (c23 : Commute x2 x3) (e f : Q ℕ) :
    P4N x0 x1 x2 x3 e * P4N x0 x1 x2 x3 f = P4N x0 x1 x2 x3 (e + f) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  obtain ⟨f0, f1, f2, f3⟩ := f
  simp only [P4N, Prod.mk_add_mk, pow_add, mul_assoc]
  rw [(c03.pow_pow f0 e3).symm.left_comm, (c02.pow_pow f0 e2).symm.left_comm,
    (c01.pow_pow f0 e1).symm.left_comm, (c13.pow_pow f1 e3).symm.left_comm,
    (c12.pow_pow f1 e2).symm.left_comm, (c23.pow_pow f2 e3).symm.left_comm]

lemma P4N_rev {y0 y1 y2 y3 : G} (c01 : Commute y0 y1) (c02 : Commute y0 y2) (c03 : Commute y0 y3)
    (c12 : Commute y1 y2) (c13 : Commute y1 y3) (c23 : Commute y2 y3) (e : Q ℕ) :
    P4N y3 y2 y1 y0 e = P4N y0 y1 y2 y3 (e.2.2.2, e.2.2.1, e.2.1, e.1) := by
  obtain ⟨e0, e1, e2, e3⟩ := e
  rw [P4N_sw0 c23, P4N_sw1 c13, P4N_sw0 c12, P4N_sw2 c03, P4N_sw1 c02, P4N_sw0 c01]
  rfl


section
variable {s : ℕ → G} {K : ℕ}

lemma hpN_mul (h : BR s K) (ws : Q ℕ) (hK : qsum ws ≤ K + 1) (e f : Q ℕ) :
    hpN s ws e * hpN s ws f = hpN s ws (e + f) :=
  P4N_mul (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega))
    (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega))
    (hb_comm h ws hK (by omega) (by omega)) (hb_comm h ws hK (by omega) (by omega)) e f

lemma hpN_zero (s : ℕ → G) (ws : Q ℕ) : hpN s ws 0 = 1 := by
  simp [hpN, P4N]

lemma crossu_left_pos (h : BR s K) {u x y : ℕ} (hK : u + x + y ≤ K + 1) :
    H s u x * wp s ((crossL x y).map (· + u)) =
      wp s ((crossL x y).map (· + u)) * H s (u + y) x := by
  have e := H_mul_Cr_left (h.shift u) (x := x) (y := y) (by omega)
  rw [Cr_sh, H, sh_sh, Nat.add_comm y u] at e
  exact e

lemma crossu_right_pos (h : BR s K) {u x y : ℕ} (hK : u + x + y ≤ K + 1) :
    H s (u + x) y * wp s ((crossL x y).map (· + u)) =
      wp s ((crossL x y).map (· + u)) * H s u y := by
  have e := H_mul_Cr_right (h.shift u) (x := x) (y := y) (by omega)
  rw [Cr_sh, H, sh_sh, Nat.add_comm x u] at e
  exact e

lemma crossu_out_pos (h : BR s K) {u x y v w : ℕ} (hK : u + x + y ≤ K + 1) (hvK : v + w ≤ K + 1)
    (hout : v + w ≤ u ∨ u + x + y ≤ v) :
    H s v w * wp s ((crossL x y).map (· + u)) =
      wp s ((crossL x y).map (· + u)) * H s v w := by
  rw [H_def]
  apply Commute.eq
  apply commute_wp_wp
  intro i hi j hj
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hj
  have := mem_hwL ha
  have := mem_crossL hb
  exact h.cm (by omega) (by omega) (by omega)

private lemma slide_pow {g x y : G} (h : x * g = g * y) (e : ℕ) :
    x ^ e * g = g * y ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]

lemma P4N_slide {g x0 x1 x2 x3 y0 y1 y2 y3 : G}
    (h0 : x0 * g = g * y0) (h1 : x1 * g = g * y1)
    (h2 : x2 * g = g * y2) (h3 : x3 * g = g * y3) (e : Q ℕ) :
    P4N x0 x1 x2 x3 e * g = g * P4N y0 y1 y2 y3 e := by
  simp only [P4N, mul_assoc]
  rw [slide_pow h3, ← mul_assoc (x2 ^ _), slide_pow h2, mul_assoc g,
    ← mul_assoc (x1 ^ _), slide_pow h1, mul_assoc g,
    ← mul_assoc (x0 ^ _), slide_pow h0]
  simp only [mul_assoc]

lemma hpN_mul_cross (h : BR s K) (ws : Q ℕ) (_hp : qpos ws) (hK : qsum ws ≤ K + 1) {i : ℕ}
    (hi : i ≤ 2) (e : Q ℕ) :
    hpN s ws e * wp s (crossAt ws i) = wp s (crossAt ws i) * hpN s (sw i ws) (sw i e) := by
  have hK' : qsum (sw i ws) ≤ K + 1 := by rwa [qsum_sw]
  obtain ⟨a, b, c, d⟩ := ws
  simp only [qsum] at hK hK'
  simp only [hpN, hb, off, wid]
  interval_cases i
  · simp only [crossAt, sw]
    have e0 : crossL a b = (crossL a b).map (· + 0) := by simp only [Nat.add_zero, List.map_id']
    have c01 := hb_comm h (b, a, c, d) hK' (i := 0) (j := 1) (by omega) (by omega)
    simp only [hb, off, wid] at c01
    have e1 := crossu_left_pos h (u := 0) (x := a) (y := b) (by omega)
    have e2 := crossu_right_pos h (u := 0) (x := a) (y := b) (by omega)
    simp only [Nat.zero_add] at e1 e2
    rw [e0, P4N_slide e1 e2
      (crossu_out_pos h (v := a + b) (w := c) (by omega) (by omega) (Or.inr (by omega)))
      (crossu_out_pos h (v := a + b + c) (w := d) (by omega) (by omega) (Or.inr (by omega))),
      P4N_sw0 c01, Nat.add_comm b a]
    rfl
  · have c12 := hb_comm h (a, c, b, d) hK' (i := 1) (j := 2) (by omega) (by omega)
    simp only [hb, off, wid] at c12
    simp only [crossAt, sw]
    rw [P4N_slide (crossu_out_pos h (v := 0) (w := a) (by omega) (by omega) (Or.inl (by omega)))
      (crossu_left_pos h (by omega)) (crossu_right_pos h (by omega))
      (crossu_out_pos h (v := a + b + c) (w := d) (by omega) (by omega) (Or.inr (by omega))),
      P4N_sw1 c12, show a + c + b = a + b + c by omega]
    rfl
  · have c23 := hb_comm h (a, b, d, c) hK' (i := 2) (j := 3) (by omega) (by omega)
    simp only [hb, off, wid] at c23
    simp only [crossAt, sw]
    rw [P4N_slide (crossu_out_pos h (v := 0) (w := a) (by omega) (by omega) (Or.inl (by omega)))
      (crossu_out_pos h (v := a) (w := b) (by omega) (by omega) (Or.inl (by omega)))
      (crossu_left_pos h (by omega)) (crossu_right_pos h (by omega)), P4N_sw2 c23]
    rfl

lemma hpN_mul_F (h : BR s K) : ∀ (w : List ℕ) (ws : Q ℕ) (e : Q ℕ), (∀ i ∈ w, i ≤ 2) → qpos ws →
    qsum ws ≤ K + 1 → hpN s ws e * F s ws w = F s ws w * hpN s (permQ ws w) (permQ e w) := by
  intro w
  induction w with
  | nil => intro ws e _ _ _; simp [F, fatL, permQ]
  | cons i w ih =>
    intro ws e hw hp' hK
    rw [F_cons, ← mul_assoc, hpN_mul_cross h ws hp' hK (hw i (by simp)), mul_assoc,
      ih (sw i ws) (sw i e) (fun j hj => hw j (by simp [hj])) (qpos_sw i ws hp') (by rwa [qsum_sw]),
      ← mul_assoc]
    rfl


end

end BGL
```

### `BraidCase3.lean`

```lean
import BraidFat
import BraidCase2

/-!
# Case III: blocks of widths `(p, p, r, p)`

With `X = Δ[1,2p]`, `Y = Δ[p+1,n]`, `n = 3p + r`:
`X Y = (Δ[1,p]² Δ[p+1,2p] Δ[2p+1,2p+r] Δ[2p+r+1,n]) · C(γ)` with `γ = σ₁σ₃σ₂σ₃` on four fat
strands; `C(γ)³ = C(Δ₄²)` by seven braid moves; hence
`(XY)³ = Δ² Δ[1,p]² Δ[p+1,2p]² Δ[2p+1,n-p] Δ[n-p+1,n]²`, which commutes with `X`.
-/

namespace BGL

variable {G : Type*} [Group G]

lemma commute_P4 {g x0 x1 x2 x3 : G} (c0 : Commute g x0) (c1 : Commute g x1) (c2 : Commute g x2)
    (c3 : Commute g x3) (e : Q ℤ) : Commute g (P4 x0 x1 x2 x3 e) :=
  (((c0.zpow_right _).mul_right (c1.zpow_right _)).mul_right (c2.zpow_right _)).mul_right
    (c3.zpow_right _)

section
variable {s : ℕ → G} {K : ℕ}

omit [Group G] in
lemma sh_sh' {α : Type*} (s : ℕ → α) (a b c : ℕ) (hc : c = b + a) : sh (sh s a) b = sh s c := by
  rw [sh_sh, hc]

/-- Four-block decomposition: `Δ = (Δ_a Δ_b Δ_c Δ_d) · C(σ₃σ₂σ₃σ₁σ₂σ₃)`. -/
lemma Hw_four (h : BR s K) (a b c d : ℕ) (hq : qpos (a, b, c, d)) (hK : qsum (a, b, c, d) ≤ K + 1) :
    Hw s (qsum (a, b, c, d)) = hp s (a, b, c, d) (1, 1, 1, 1) * F s (a, b, c, d) [2, 1, 2, 0, 1, 2] := by
  simp only [qpos, qsum] at hq hK
  have h1 := Hw_add_cross h (x := a) (y := b + (c + d)) (by omega) (by omega)
  have h2 := Hw_add_cross (h.shift a) (x := b) (y := c + d) (by omega) (by omega)
  have h3 := Hw_add_cross ((h.shift a).shift b) (x := c) (y := d) (by omega) (by omega)
  have p1 : Cr s a (b + (c + d))
      = wp s (crossL a d) * wp s ((crossL a c).map (· + d)) * wp s ((crossL a b).map (· + (d + c))) := by
    rw [Cr, show b + (c + d) = d + c + b by omega, crossL_add, crossL_add, wp_append, wp_append]
  have p2 : Cr (sh s a) b (c + d)
      = wp s ((crossL b d).map (· + a)) * wp s ((crossL b c).map (· + (a + d))) := by
    rw [Cr_sh, show c + d = d + c by omega, crossL_add, List.map_append, wp_append, List.map_map]
    congr 1; apply wp_map_congr; intro x _; simp; omega
  have p3 : Cr (sh (sh s a) b) c d = wp s ((crossL c d).map (· + (a + b))) := by
    rw [sh_sh' s a b (a + b) (by omega), Cr_sh]
  have p4 : H (sh (sh s a) b) c d = H s (a + b + c) d := by
    rw [H, H, sh_sh, sh_sh]; congr 2; omega
  have p5 : Hw (sh (sh s a) b) c = H s (a + b) c := by
    rw [H, sh_sh' s a b (a + b) (by omega)]
  show Hw s (a + b + c + d) = _
  rw [show a + b + c + d = a + (b + (c + d)) by omega, h1, H, h2, H, h3, p1, p2, p3, p4, p5,
    show Hw (sh s a) b = H s a b from rfl]
  simp only [hp, P4, hb, off, wid, F, fatL, crossAt, sw, wp_append, zpow_one, H_zero, List.append_nil]
  group

/-- `Δ` reverses the block pattern. -/
lemma Delta_conj_hp {n : ℕ} (h : BR s (n - 1)) (hn : 2 ≤ n) (a b c d : ℕ)
    (hsum : qsum (a, b, c, d) = n) (e : Q ℤ) :
    Hw s n * hp s (d, c, b, a) e * (Hw s n)⁻¹ = hp s (a, b, c, d) (e.2.2.2, e.2.2.1, e.2.1, e.1) := by
  simp only [qsum] at hsum
  have := conj_P4 (Hw s n)⁻¹ (hb s (d, c, b, a) 0) (hb s (d, c, b, a) 1) (hb s (d, c, b, a) 2)
    (hb s (d, c, b, a) 3) e
  simp only [inv_inv] at this
  rw [hp, this]
  simp only [hb, off, wid]
  rw [Delta_conj_H h hn (by omega), Delta_conj_H h hn (by omega), Delta_conj_H h hn (by omega),
    Delta_conj_H h hn (by omega)]
  have hK : qsum (a, b, c, d) ≤ n - 1 + 1 := by simp only [qsum]; omega
  have cc := fun i j (hij : i < j) (hj : j ≤ 3) => hb_comm h (a, b, c, d) hK hij hj
  rw [show n - 0 - d = a + b + c by omega, show n - d - c = a + b by omega,
    show n - (d + c) - b = a by omega, show n - (d + c + b) - a = 0 by omega]
  have := P4_rev (cc 0 1 (by omega) (by omega)) (cc 0 2 (by omega) (by omega))
    (cc 0 3 (by omega) (by omega)) (cc 1 2 (by omega) (by omega)) (cc 1 3 (by omega) (by omega))
    (cc 2 3 (by omega) (by omega)) e
  simp only [hb, off, wid] at this
  rw [this, hp]; simp only [hb, off, wid]

end

/-- The seven braid moves taking `γ³` to `Δ₄²` (`γ = σ₁σ₃σ₂σ₃`, `Δ₄ = σ₃σ₂σ₃σ₁σ₂σ₃`). -/
lemma chain_ok : mvs [0, 3, 1, 5, 3, 2, 8] (([0, 2, 1, 2] ++ [0, 2, 1, 2]) ++ [0, 2, 1, 2])
    = [2, 1, 2, 0, 1, 2] ++ [2, 1, 2, 0, 1, 2] := by decide

lemma cube_shift {F : G} {P : Q ℤ → G} (T : Q ℤ → Q ℤ) (hm : ∀ e f, P e * P f = P (e + f))
    (hk : ∀ e, P e * F = F * P (T e)) (e E : Q ℤ) (hE : T (T e) + T e + e = E) :
    (F * P e) ^ 3 = F ^ 3 * P E := by
  calc (F * P e) ^ 3 = F * (P e * F) * (P e * F) * P e := by
        rw [pow_succ, pow_succ, pow_one]; group
    _ = F * (F * P (T e)) * (F * P (T e)) * P e := by rw [hk e]
    _ = F * F * (P (T e) * F) * P (T e) * P e := by group
    _ = F * F * (F * P (T (T e))) * P (T e) * P e := by rw [hk (T e)]
    _ = F ^ 3 * (P (T (T e)) * P (T e) * P e) := by rw [pow_succ, pow_succ, pow_one]; group
    _ = F ^ 3 * P E := by rw [hm, hm, hE]

section
variable {s : ℕ → G} {n : ℕ}

theorem caseIII (h : BR s (n - 1)) (p r : ℕ) (hp1 : 1 ≤ p) (hr : 1 ≤ r) (hn : n = 3 * p + r) :
    alt 6 (Hw s (2 * p)) (H s p (n - p)) = alt 6 (H s p (n - p)) (Hw s (2 * p)) := by
  have hn2 : 2 ≤ n := by omega
  set ws : Q ℕ := (p, p, r, p) with hws
  have hpos : qpos ws := by simp only [hws, qpos]; omega
  have hsum : qsum ws = n := by simp only [hws, qsum]; omega
  have hK : qsum ws ≤ n - 1 + 1 := by omega
  -- X and Y as block twists times fat words
  have hX : Hw s (2 * p) = hp s ws (1, 1, 0, 0) * F s ws [0] := by
    rw [show 2 * p = p + p by omega, Hw_add_cross h (by omega) (by omega)]
    simp only [hws, hp, P4, hb, off, wid, F, fatL, crossAt, List.append_nil, zpow_one, zpow_zero,
      mul_one, H_zero, Cr]
  have hY : H s p (n - p) = hp s ws (0, 1, 1, 1) * F s ws [2, 1, 2] := by
    have hs := h.shift p
    have e1 := Hw_add_cross hs (x := p) (y := r + p) (by omega) (by omega)
    have e2 := Hw_add_cross (hs.shift p) (x := r) (y := p) (by omega) (by omega)
    rw [H, show n - p = p + (r + p) by omega, e1, H, e2]
    rw [sh_sh' s p p (p + p) rfl, Cr_sh, Cr_sh]
    simp only [hws, hp, P4, hb, off, wid, F, fatL, crossAt, sw, List.append_nil, zpow_one, zpow_zero,
      one_mul, wp_append]
    rw [show r + p = p + r by omega, crossL_add, List.map_append, wp_append, List.map_map]
    have e3 : wp s ((crossL p r).map ((· + p) ∘ (· + p))) = wp s ((crossL p r).map (· + (p + p))) :=
      wp_map_congr s (fun x _ => by simp; omega)
    have e4 : H (sh s (p + p)) r p = H s (p + p + r) p := by
      rw [H, H, sh_sh]; congr 2; omega
    rw [e3, e4, show Hw (sh s p) p = H s p p from rfl, show Hw (sh s (p + p)) r = H s (p + p) r from rfl]
    group
  have hγ : permQ ws [0, 2, 1, 2] = ws := rfl
  have key : ∀ e : Q ℤ, hp s ws e * F s ws [0, 2, 1, 2] = F s ws [0, 2, 1, 2] * hp s ws (permQ e [0, 2, 1, 2]) := by
    intro e
    have := hp_mul_F h [0, 2, 1, 2] ws e (by decide) hpos hK
    rwa [hγ] at this
  have hXY : Hw s (2 * p) * H s p (n - p) = hp s ws (2, 1, 1, 1) * F s ws [0, 2, 1, 2] := by
    have t0 := hp_mul_F h [0] ws (1, 0, 1, 1) (by decide) hpos hK
    have : permQ ws [0] = ws := rfl
    rw [this, show permQ ((1, 0, 1, 1) : Q ℤ) [0] = (0, 1, 1, 1) from rfl] at t0
    rw [hX, hY, show ((2, 1, 1, 1) : Q ℤ) = (1, 1, 0, 0) + (1, 0, 1, 1) by decide, ← hp_mul h ws hK,
      show [0, 2, 1, 2] = [0] ++ [2, 1, 2] from rfl, F_append, this]
    calc hp s ws (1, 1, 0, 0) * F s ws [0] * (hp s ws (0, 1, 1, 1) * F s ws [2, 1, 2])
        = hp s ws (1, 1, 0, 0) * (F s ws [0] * hp s ws (0, 1, 1, 1)) * F s ws [2, 1, 2] := by
          group
      _ = hp s ws (1, 1, 0, 0) * (hp s ws (1, 0, 1, 1) * F s ws [0]) * F s ws [2, 1, 2] := by rw [t0]
      _ = _ := by group
  -- the cube of the fat word
  have hF3 : F s ws [0, 2, 1, 2] ^ 3 = hp s ws (-2, -2, -2, -2) * Hw s n ^ 2 := by
    have e1 : F s ws [0, 2, 1, 2] ^ 3
        = F s ws (([0, 2, 1, 2] ++ [0, 2, 1, 2]) ++ [0, 2, 1, 2]) := by
      rw [F_append, F_append, show permQ ws ([0, 2, 1, 2] ++ [0, 2, 1, 2]) = ws from rfl, hγ,
        pow_succ, pow_succ, pow_one]
    rw [e1, ← mvs_F h [0, 3, 1, 5, 3, 2, 8] (([0, 2, 1, 2] ++ [0, 2, 1, 2]) ++ [0, 2, 1, 2]) ws
      (by decide) hpos hK, chain_ok, F_append]
    have hrev : permQ ws [2, 1, 2, 0, 1, 2] = (p, r, p, p) := rfl
    rw [hrev]
    have d1 := Hw_four h p p r p hpos hK
    have d2 := Hw_four h p r p p (by simp only [qpos]; omega) (by simp only [qsum]; omega)
    have hs2 : qsum (p, r, p, p) = n := by simp only [qsum]; omega
    rw [← hws, hsum] at d1
    rw [hs2] at d2
    have f1 : F s ws [2, 1, 2, 0, 1, 2] = (hp s ws (1, 1, 1, 1))⁻¹ * Hw s n := by rw [d1]; group
    have f2 : F s (p, r, p, p) [2, 1, 2, 0, 1, 2] = (hp s (p, r, p, p) (1, 1, 1, 1))⁻¹ * Hw s n := by
      rw [d2]; group
    have fl : Hw s n * hp s (p, r, p, p) (1, 1, 1, 1) * (Hw s n)⁻¹ = hp s ws (1, 1, 1, 1) :=
      Delta_conj_hp h hn2 p p r p (by simp only [qsum]; omega) (1, 1, 1, 1)
    rw [f1, f2, show ((-2, -2, -2, -2) : Q ℤ) = -(1, 1, 1, 1) + -(1, 1, 1, 1) by decide,
      ← hp_mul h ws hK, ← hp_inv h ws hK]
    calc (hp s ws (1, 1, 1, 1))⁻¹ * Hw s n * ((hp s (p, r, p, p) (1, 1, 1, 1))⁻¹ * Hw s n)
        = (hp s ws (1, 1, 1, 1))⁻¹ * (Hw s n * hp s (p, r, p, p) (1, 1, 1, 1) * (Hw s n)⁻¹)⁻¹
          * (Hw s n * Hw s n) := by group
      _ = (hp s ws (1, 1, 1, 1))⁻¹ * (hp s ws (1, 1, 1, 1))⁻¹ * Hw s n ^ 2 := by
          rw [fl, pow_two]
  have cD : ∀ e : Q ℤ, Commute (Hw s n ^ 2) (hp s ws e) := by
    intro e
    simp only [hws, hp, hb, off, wid]
    exact commute_P4 (Delta_sq_comm_H h hn2 (by omega)) (Delta_sq_comm_H h hn2 (by omega))
      (Delta_sq_comm_H h hn2 (by omega)) (Delta_sq_comm_H h hn2 (by omega)) e
  have hcube : (Hw s (2 * p) * H s p (n - p)) ^ 3 = Hw s n ^ 2 * hp s ws (2, 2, 1, 2) := by
    rw [hXY, key (2, 1, 1, 1),
      cube_shift (fun e => permQ e [0, 2, 1, 2]) (hp_mul h ws hK) key _ (4, 4, 3, 4) (by decide), hF3,
      ← (cD _).eq, mul_assoc, hp_mul h ws hK,
      show ((-2, -2, -2, -2) : Q ℤ) + (4, 4, 3, 4) = (2, 2, 1, 2) by decide]
  -- X commutes with (XY)³
  have cX : Commute (Hw s (2 * p)) ((Hw s (2 * p) * H s p (n - p)) ^ 3) := by
    rw [hcube]
    refine Commute.mul_right ?_ ?_
    · rw [← H_zero s (2 * p)]; exact (Delta_sq_comm_H h hn2 (by omega)).symm
    · rw [hX]
      refine Commute.mul_left ?_ ?_
      · show hp s ws (1, 1, 0, 0) * hp s ws (2, 2, 1, 2) = hp s ws (2, 2, 1, 2) * hp s ws (1, 1, 0, 0)
        rw [hp_mul h ws hK, hp_mul h ws hK,
          show ((1, 1, 0, 0) : Q ℤ) + (2, 2, 1, 2) = (2, 2, 1, 2) + (1, 1, 0, 0) by decide]
      · have t := hp_mul_F h [0] ws (2, 2, 1, 2) (by decide) hpos hK
        exact t.symm
  rw [show (6 : ℕ) = 2 * 3 from rfl, alt_two_mul, alt_two_mul]
  have hyx : H s p (n - p) * Hw s (2 * p)
      = (Hw s (2 * p))⁻¹ * (Hw s (2 * p) * H s p (n - p)) * Hw s (2 * p) := by group
  have cp := conjPow (Hw s (2 * p))⁻¹ (Hw s (2 * p) * H s p (n - p)) 3
  simp only [inv_inv] at cp
  rw [hyx, cp, mul_assoc, ← cX.eq]; group

end

end BGL
```

### `BraidPositiveCase3.lean`

```lean
import BraidCase3
import BraidPositivePeriodic

namespace BGL

variable {G : Type*} [Monoid G]

section
variable {s : ℕ → G} {K : ℕ}

/-- Four-block decomposition: `Δ = (Δ_a Δ_b Δ_c Δ_d) · C(σ₃σ₂σ₃σ₁σ₂σ₃)`. -/
lemma Hw_four_pos (h : BR s K) (a b c d : ℕ) (hq : qpos (a, b, c, d)) (hK : qsum (a, b, c, d) ≤ K + 1) :
    Hw s (qsum (a, b, c, d)) = hpN s (a, b, c, d) (1, 1, 1, 1) * F s (a, b, c, d) [2, 1, 2, 0, 1, 2] := by
  simp only [qpos, qsum] at hq hK
  have h1 := Hw_add_cross h (x := a) (y := b + (c + d)) (by omega) (by omega)
  have h2 := Hw_add_cross (h.shift a) (x := b) (y := c + d) (by omega) (by omega)
  have h3 := Hw_add_cross ((h.shift a).shift b) (x := c) (y := d) (by omega) (by omega)
  have p1 : Cr s a (b + (c + d))
      = wp s (crossL a d) * wp s ((crossL a c).map (· + d)) * wp s ((crossL a b).map (· + (d + c))) := by
    rw [Cr, show b + (c + d) = d + c + b by omega, crossL_add, crossL_add, wp_append, wp_append]
  have p2 : Cr (sh s a) b (c + d)
      = wp s ((crossL b d).map (· + a)) * wp s ((crossL b c).map (· + (a + d))) := by
    rw [Cr_sh, show c + d = d + c by omega, crossL_add, List.map_append, wp_append, List.map_map]
    congr 1; apply wp_map_congr; intro x _; simp; omega
  have p3 : Cr (sh (sh s a) b) c d = wp s ((crossL c d).map (· + (a + b))) := by
    rw [sh_sh' s a b (a + b) (by omega), Cr_sh]
  have p4 : H (sh (sh s a) b) c d = H s (a + b + c) d := by
    rw [H, H, sh_sh, sh_sh]; congr 2; omega
  have p5 : Hw (sh (sh s a) b) c = H s (a + b) c := by
    rw [H, sh_sh' s a b (a + b) (by omega)]
  show Hw s (a + b + c + d) = _
  rw [show a + b + c + d = a + (b + (c + d)) by omega, h1, H, h2, H, h3, p1, p2, p3, p4, p5,
    show Hw (sh s a) b = H s a b from rfl]
  simp only [hpN, P4N, hb, off, wid, F, fatL, crossAt, sw, wp_append, pow_one, H_zero, List.append_nil]
  simp only [mul_assoc]

end

lemma cube_shift_pos {F : G} {P : Q ℕ → G} (T : Q ℕ → Q ℕ) (hm : ∀ e f, P e * P f = P (e + f))
    (hk : ∀ e, P e * F = F * P (T e)) (e E : Q ℕ) (hE : T (T e) + T e + e = E) :
    (F * P e) ^ 3 = F ^ 3 * P E := by
  calc (F * P e) ^ 3 = F * (P e * F) * (P e * F) * P e := by
        rw [pow_succ, pow_succ, pow_one]; group
    _ = F * (F * P (T e)) * (F * P (T e)) * P e := by rw [hk e]
    _ = F * F * (P (T e) * F) * P (T e) * P e := by simp only [mul_assoc]
    _ = F * F * (F * P (T (T e))) * P (T e) * P e := by rw [hk (T e)]
    _ = F ^ 3 * (P (T (T e)) * P (T e) * P e) := by rw [pow_succ, pow_succ, pow_one]; group
    _ = F ^ 3 * P E := by rw [hm, hm, hE]

section
variable {s : ℕ → G} {n : ℕ}

lemma caseIII_positive_closed (h : BR s (n - 1)) (p r : ℕ) (hp1 : 1 ≤ p) (hr : 1 ≤ r) (hn : n = 3 * p + r) :
    (Hw s (2 * p) * H s p (n - p)) ^ 3 = Hw s n ^ 2 * hpN s (p, p, r, p) (2, 2, 1, 2) := by
  have hn2 : 2 ≤ n := by omega
  set ws : Q ℕ := (p, p, r, p) with hws
  have hpos : qpos ws := by simp only [hws, qpos]; omega
  have hsum : qsum ws = n := by simp only [hws, qsum]; omega
  have hK : qsum ws ≤ n - 1 + 1 := by omega
  -- X and Y as block twists times fat words
  have hX : Hw s (2 * p) = hpN s ws (1, 1, 0, 0) * F s ws [0] := by
    rw [show 2 * p = p + p by omega, Hw_add_cross h (by omega) (by omega)]
    simp only [hws, hpN, P4N, hb, off, wid, F, fatL, crossAt, List.append_nil, pow_one, pow_zero,
      mul_one, H_zero, Cr]
  have hY : H s p (n - p) = hpN s ws (0, 1, 1, 1) * F s ws [2, 1, 2] := by
    have hs := h.shift p
    have e1 := Hw_add_cross hs (x := p) (y := r + p) (by omega) (by omega)
    have e2 := Hw_add_cross (hs.shift p) (x := r) (y := p) (by omega) (by omega)
    rw [H, show n - p = p + (r + p) by omega, e1, H, e2]
    rw [sh_sh' s p p (p + p) rfl, Cr_sh, Cr_sh]
    simp only [hws, hpN, P4N, hb, off, wid, F, fatL, crossAt, sw, List.append_nil, pow_one, pow_zero,
      one_mul, wp_append]
    rw [show r + p = p + r by omega, crossL_add, List.map_append, wp_append, List.map_map]
    have e3 : wp s ((crossL p r).map ((· + p) ∘ (· + p))) = wp s ((crossL p r).map (· + (p + p))) :=
      wp_map_congr s (fun x _ => by simp; omega)
    have e4 : H (sh s (p + p)) r p = H s (p + p + r) p := by
      rw [H, H, sh_sh]; congr 2; omega
    rw [e3, e4, show Hw (sh s p) p = H s p p from rfl, show Hw (sh s (p + p)) r = H s (p + p) r from rfl]
    simp only [mul_assoc]
  have hγ : permQ ws [0, 2, 1, 2] = ws := rfl
  have key : ∀ e : Q ℕ, hpN s ws e * F s ws [0, 2, 1, 2] = F s ws [0, 2, 1, 2] * hpN s ws (permQ e [0, 2, 1, 2]) := by
    intro e
    have := hpN_mul_F h [0, 2, 1, 2] ws e (by decide) hpos hK
    rwa [hγ] at this
  have hXY : Hw s (2 * p) * H s p (n - p) = hpN s ws (2, 1, 1, 1) * F s ws [0, 2, 1, 2] := by
    have t0 := hpN_mul_F h [0] ws (1, 0, 1, 1) (by decide) hpos hK
    have : permQ ws [0] = ws := rfl
    rw [this, show permQ ((1, 0, 1, 1) : Q ℕ) [0] = (0, 1, 1, 1) from rfl] at t0
    rw [hX, hY, show ((2, 1, 1, 1) : Q ℕ) = (1, 1, 0, 0) + (1, 0, 1, 1) by decide, ← hpN_mul h ws hK,
      show [0, 2, 1, 2] = [0] ++ [2, 1, 2] from rfl, F_append, this]
    calc hpN s ws (1, 1, 0, 0) * F s ws [0] * (hpN s ws (0, 1, 1, 1) * F s ws [2, 1, 2])
        = hpN s ws (1, 1, 0, 0) * (F s ws [0] * hpN s ws (0, 1, 1, 1)) * F s ws [2, 1, 2] := by
          simp only [mul_assoc]
      _ = hpN s ws (1, 1, 0, 0) * (hpN s ws (1, 0, 1, 1) * F s ws [0]) * F s ws [2, 1, 2] := by rw [t0]
      _ = _ := by simp only [mul_assoc]
  have hF3 : F s ws [0, 2, 1, 2] ^ 3 =
      F s ws [2, 1, 2, 0, 1, 2] * F s (p, r, p, p) [2, 1, 2, 0, 1, 2] := by
    have e : F s ws [0, 2, 1, 2] ^ 3 =
        F s ws (([0, 2, 1, 2] ++ [0, 2, 1, 2]) ++ [0, 2, 1, 2]) := by
      rw [F_append, F_append, show permQ ws ([0, 2, 1, 2] ++ [0, 2, 1, 2]) = ws from rfl,
        hγ, pow_succ, pow_succ, pow_one]
    rw [e, ← mvs_F h [0, 3, 1, 5, 3, 2, 8] (([0, 2, 1, 2] ++ [0, 2, 1, 2]) ++ [0, 2, 1, 2]) ws
      (by decide) hpos hK, chain_ok, F_append]
    rfl
  have hFull : Hw s n ^ 2 = hpN s ws (2, 2, 2, 2) * F s ws [0, 2, 1, 2] ^ 3 := by
    have d1 := Hw_four_pos h p p r p hpos hK
    have hK' : qsum (p, r, p, p) ≤ n - 1 + 1 := by simp only [qsum]; omega
    have d2 := Hw_four_pos h p r p p (by simp only [qpos]; omega) hK'
    rw [← hws, hsum] at d1
    rw [show qsum (p, r, p, p) = n by simp only [qsum]; omega] at d2
    have e := hpN_mul_F h [2, 1, 2, 0, 1, 2] ws (1, 1, 1, 1) (by decide) hpos hK
    change hpN s ws (1, 1, 1, 1) * F s ws [2, 1, 2, 0, 1, 2] =
      F s ws [2, 1, 2, 0, 1, 2] * hpN s (p, r, p, p) (1, 1, 1, 1) at e
    rw [pow_two]
    nth_rewrite 1 [d1]
    rw [d2, hF3, mul_assoc (hpN s ws (1, 1, 1, 1)),
      ← mul_assoc (F s ws [2, 1, 2, 0, 1, 2]), ← e, mul_assoc (hpN s ws (1, 1, 1, 1))]
    rw [← mul_assoc (hpN s ws (1, 1, 1, 1)) (hpN s ws (1, 1, 1, 1)), hpN_mul h ws hK]
    rfl
  have cF : Commute (hpN s ws (2, 2, 2, 2)) (F s ws [0, 2, 1, 2]) :=
    key (2, 2, 2, 2)
  rw [hXY, key (2, 1, 1, 1),
    cube_shift_pos (fun e => permQ e [0, 2, 1, 2]) (hpN_mul h ws hK) key _ (4, 4, 3, 4) (by decide),
    hFull, (cF.pow_right 3).eq, mul_assoc, hpN_mul h ws hK]
  rfl

private lemma hpN_unop (h : BR s (n - 1)) (ws : Q ℕ) (hn : qsum ws ≤ n - 1 + 1) (e : Q ℕ) :
    MulOpposite.unop (hpN (fun i => MulOpposite.op (s i)) ws e) = hpN s ws e := by
  have bound (i : ℕ) : off ws i + wid ws i ≤ n - 1 + 1 := by
    obtain ⟨a,b,c,d⟩ := ws
    rcases i with _ | _ | _ | i <;> simp only [off, wid, qsum] at * <;> omega
  have ht (i : ℕ) : MulOpposite.unop (hb (fun i => MulOpposite.op (s i)) ws i) = hb s ws i :=
    H_op h (bound i)
  simp only [hpN, P4N, MulOpposite.unop_mul, MulOpposite.unop_pow, ht]
  have c (i j : ℕ) (hij : i < j) (hj : j ≤ 3) := hb_comm h ws hn hij hj
  have er := P4N_rev (c 0 1 (by omega) (by omega)) (c 0 2 (by omega) (by omega))
    (c 0 3 (by omega) (by omega)) (c 1 2 (by omega) (by omega)) (c 1 3 (by omega) (by omega))
    (c 2 3 (by omega) (by omega)) (e.2.2.2, e.2.2.1, e.2.1, e.1)
  simpa only [P4N, mul_assoc] using er

theorem caseIII_positive (h : BR s (n - 1)) (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hn : n = 3 * p + r) :
    alt 6 (Hw s (2 * p)) (H s p (n - p)) = alt 6 (H s p (n - p)) (Hw s (2 * p)) := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, alt_two_mul, alt_two_mul]
  have hK : qsum (p, p, r, p) ≤ n - 1 + 1 := by simp only [qsum]; omega
  have ho := congrArg MulOpposite.unop (caseIII_positive_closed h.op p r hp hr hn)
  simp only [MulOpposite.unop_pow, MulOpposite.unop_mul, Hw_op h (m := 2 * p) (by omega),
    Hw_op h (m := n) (by omega), H_op h (u := p) (w := n - p) (by omega), hpN_unop h _ hK] at ho
  have hc : Commute (Hw s n ^ 2) (hpN s (p, p, r, p) (2, 2, 1, 2)) := by
    simp only [hpN, P4N, hb, off, wid]
    exact (((fullTwist_commutes_H h (by omega)).pow_right _).mul_right
      ((fullTwist_commutes_H h (by omega)).pow_right _)).mul_right
      ((fullTwist_commutes_H h (by omega)).pow_right _) |>.mul_right
      ((fullTwist_commutes_H h (by omega)).pow_right _)
  rw [caseIII_positive_closed h p r hp hr hn, ho, hc.eq]

end

end BGL
```

### `BraidStatement.lean`

```lean
import BraidCase3
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.PresentedMonoid.Basic

/-!
# MathDB 375588: Berenstein–Greenstein–Li, Conjecture 6.35 (= Conjecture 5.85 of arXiv:2405.18821)

Source objects, transcribed literally:

* `Br_n`: generators `σ_1, …, σ_{n-1}` (index `k : Fin (n-1)` stands for `σ_{k+1}`), relations
  `σ_i σ_j = σ_j σ_i` for `|i - j| ≥ 2` and `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}`.
  `BraidGroup n` is the group with this presentation, `BrPlus n` the monoid (the source's `Br⁺_n`).
* `T_{w∘^{[u,v-1]}}`, the positive lift of the longest element of the parabolic subgroup generated by
  `s_u, …, s_{v-1}`, written with the reduced word
  `w∘^{[u,v-1]} = ∏_{k=u}^{v-1} (s_k s_{k-1} ⋯ s_u)`: this is `halfTwist n u v`
  (`halfTwistP n u v` in the monoid). So `T_{w∘^{[1,a]}} = halfTwist n 1 (a+1)` and
  `T_{w∘^{[b,n-1]}} = halfTwist n b n`.
* `Br⁺(I₂(N)) = ⟨T̂₁, T̂₂ | alt_N(T̂₁,T̂₂) = alt_N(T̂₂,T̂₁)⟩` with `alt_N(x,y) = x y x ⋯` (`N` factors).
-/

namespace BGL

/-- The braid relations of `Br_n` as relators. -/
def braidRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ i j : Fin (n - 1),
      (i.val + 1 = j.val ∧ r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i
          * (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∨
      (i.val + 2 ≤ j.val ∧ r = FreeGroup.of i * FreeGroup.of j * (FreeGroup.of j * FreeGroup.of i)⁻¹)}

/-- The braid group `Br_n` on `n` strands. -/
abbrev BraidGroup (n : ℕ) := PresentedGroup (braidRels n)

/-- The braid relations of `Br⁺_n` as pairs of positive words. -/
def braidRelsPlus (n : ℕ) : FreeMonoid (Fin (n - 1)) → FreeMonoid (Fin (n - 1)) → Prop :=
  fun x y => ∃ i j : Fin (n - 1),
    (i.val + 1 = j.val ∧ x = FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i ∧
        y = FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j) ∨
    (i.val + 2 ≤ j.val ∧ x = FreeMonoid.of i * FreeMonoid.of j ∧
        y = FreeMonoid.of j * FreeMonoid.of i)

/-- The positive braid monoid `Br⁺_n`. -/
abbrev BrPlus (n : ℕ) := PresentedMonoid (braidRelsPlus n)

/-- `σ_i` (`1 ≤ i ≤ n-1`); other indices give `1` and are never used. -/
def σ (n i : ℕ) : BraidGroup n :=
  if h : 1 ≤ i ∧ i < n then PresentedGroup.of (⟨i - 1, by omega⟩ : Fin (n - 1)) else 1

def σp (n i : ℕ) : BrPlus n :=
  if h : 1 ≤ i ∧ i < n then PresentedMonoid.of _ (⟨i - 1, by omega⟩ : Fin (n - 1)) else 1

/-- `g_k g_{k-1} ⋯ g_u`. -/
def descProd {M : Type*} [Monoid M] (g : ℕ → M) (u k : ℕ) : M :=
  ((List.range (k + 1 - u)).map (fun t => g (k - t))).prod

/-- `∏_{k=u}^{v-1} (g_k g_{k-1} ⋯ g_u)`. -/
def halfTwistG {M : Type*} [Monoid M] (g : ℕ → M) (u v : ℕ) : M :=
  ((List.range (v - u)).map (fun t => descProd g u (u + t))).prod

/-- `T_{w∘^{[u,v-1]}}` in `Br_n`: the half twist `Δ[u,v]` on strands `u, …, v`. -/
def halfTwist (n u v : ℕ) : BraidGroup n := halfTwistG (σ n) u v

/-- `T_{w∘^{[u,v-1]}}` in `Br⁺_n`. -/
def halfTwistP (n u v : ℕ) : BrPlus n := halfTwistG (σp n) u v

/-- The hypotheses of Conjecture 6.35, transcribed literally:
`1 ≤ b ≤ a < n - 1`, `a > 1`, and one of
(1) `N = 2n/(n+b-a-2) ∈ 2ℤ_{>0}`; (2) `a + b = n` and `N = n/(b-1) ∈ 1 + 2ℤ_{>0}`;
(3) `a + 1 = 2(b-1)`, `a + b < n` and `N = 6`. -/
def Hyp (n a b N : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ a ∧ a < n - 1 ∧ 1 < a ∧
  ((2 * n = N * (n + b - a - 2) ∧ 0 < N ∧ Even N) ∨
   (a + b = n ∧ n = N * (b - 1) ∧ ∃ k : ℕ, 0 < k ∧ N = 1 + 2 * k) ∨
   (a + 1 = 2 * (b - 1) ∧ a + b < n ∧ N = 6))

/-! ## Bridge to the generic development -/

lemma dscL_eq_range (m : ℕ) : dscL m = (List.range m).map (fun t => m - 1 - t) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [dscL, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    simp only [List.cons.injEq]
    refine ⟨by omega, ?_⟩
    apply List.map_congr_left; intro t ht; simp at ht; simp; omega

variable {G : Type*} [Monoid G]

lemma halfTwistG_eq (g : ℕ → G) (u : ℕ) :
    ∀ d, halfTwistG g u (u + d) = wp (fun i => g (i + u)) (hwL (d + 1)) := by
  intro d
  induction d with
  | zero => simp [halfTwistG, hwL, dscL]
  | succ d ih =>
    have e : u + (d + 1) - u = d + 1 := by omega
    have e' : u + d - u = d := by omega
    have hh : ((List.range d).map (fun t => descProd g u (u + t))).prod = halfTwistG g u (u + d) := by
      rw [halfTwistG, e']
    show ((List.range (u + (d + 1) - u)).map (fun t => descProd g u (u + t))).prod = _
    rw [e, List.range_succ, List.map_append, List.prod_append, hh, ih,
      show hwL (d + 1 + 1) = hwL (d + 1) ++ dscL (d + 1) from rfl, wp_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    congr 1
    rw [wp, dscL_eq_range, List.map_map, descProd, show u + d + 1 - u = d + 1 by omega]
    congr 1; apply List.map_congr_left; intro t ht; simp at ht; simp; congr 1; omega

lemma map_alt {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N) :
    ∀ (k : ℕ) (x y : M), φ (alt k x y) = alt k (φ x) (φ y) := by
  intro k
  induction k with
  | zero => intro x y; simp [alt]
  | succ k ih => intro x y; rw [alt, alt, map_mul, ih]

lemma map_halfTwistG {M N : Type*} [Monoid M] [Monoid N] (φ : M →* N) (g : ℕ → M) (u v : ℕ) :
    φ (halfTwistG g u v) = halfTwistG (fun i => φ (g i)) u v := by
  simp [halfTwistG, descProd, map_list_prod, List.map_map, Function.comp_def]

/-- The generators of `Br_n` in the generic (0-based) form. -/
def sgen (n : ℕ) : ℕ → BraidGroup n := fun i => σ n (i + 1)

lemma sgen_eq (n i : ℕ) (hi : i < n - 1) : sgen n i = PresentedGroup.of (⟨i, hi⟩ : Fin (n - 1)) := by
  unfold sgen σ
  split_ifs with h0
  · congr 1
  · exfalso; omega

lemma BR_sgen (n : ℕ) : BR (sgen n) (n - 1) where
  braid i hi := by
    rw [sgen_eq n i (by omega), sgen_eq n (i + 1) hi]
    have := PresentedGroup.one_of_mem (rels := braidRels n)
      (x := FreeGroup.of (⟨i, by omega⟩ : Fin (n - 1)) * FreeGroup.of ⟨i + 1, hi⟩ * FreeGroup.of ⟨i, by omega⟩
        * (FreeGroup.of ⟨i + 1, hi⟩ * FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i + 1, hi⟩)⁻¹)
      ⟨⟨i, by omega⟩, ⟨i + 1, hi⟩, Or.inl ⟨rfl, rfl⟩⟩
    simp only [map_mul, map_inv] at this
    exact mul_inv_eq_one.mp this
  comm i j hij hj := by
    rw [sgen_eq n i (by omega), sgen_eq n j hj]
    have := PresentedGroup.one_of_mem (rels := braidRels n)
      (x := FreeGroup.of (⟨i, by omega⟩ : Fin (n - 1)) * FreeGroup.of ⟨j, hj⟩
        * (FreeGroup.of ⟨j, hj⟩ * FreeGroup.of ⟨i, by omega⟩)⁻¹)
      ⟨⟨i, by omega⟩, ⟨j, hj⟩, Or.inr ⟨hij, rfl⟩⟩
    simp only [map_mul, map_inv] at this
    exact mul_inv_eq_one.mp this

lemma halfTwist_eq_H (n u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v) :
    halfTwist n u v = H (sgen n) (u - 1) (v - u + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  rw [halfTwist, halfTwistG_eq, H, Hw, show u + d - u + 1 = d + 1 by omega]
  apply wp_congr; intro x _; simp only [sgen, sh_apply]; congr 1; omega

/-! ## The theorem -/

/-- **Conjecture 6.35 of Berenstein–Greenstein–Li, in the braid group `Br_n`.** -/
theorem conj_6_35_group (n a b N : ℕ) (hyp : Hyp n a b N) :
    alt N (halfTwist n 1 (a + 1)) (halfTwist n b n) = alt N (halfTwist n b n) (halfTwist n 1 (a + 1)) := by
  obtain ⟨hb, hba, han, ha, hcase⟩ := hyp
  have h := BR_sgen n
  have hn : 2 ≤ n := by omega
  set p := b - 1 with hp
  set q := n - 1 - a with hq
  have hX : halfTwist n 1 (a + 1) = Hw (sgen n) (n - q) := by
    rw [halfTwist_eq_H n 1 (a + 1) le_rfl (by omega), show 1 - 1 = 0 from rfl, H_zero]
    congr 1; omega
  have hY : halfTwist n b n = H (sgen n) p (n - p) := by
    rw [halfTwist_eq_H n b n hb (by omega)]; congr 1; omega
  rw [hX, hY]
  rcases hcase with ⟨h1, _, ⟨m, hm⟩⟩ | ⟨h2, h2', _⟩ | ⟨h3, h3', rfl⟩
  · -- case (1): `N = 2m`, `m (p + q) = n`
    have hmn : m * (p + q) = n := by
      have : n + b - a - 2 = p + q := by omega
      rw [this, hm] at h1; nlinarith
    rw [hm, ← two_mul, alt_two_mul, alt_two_mul]
    exact caseI h hn p q m hmn
  · -- case (2): `p = q`, `N p = n`
    have hpq : n - q = n - p := by omega
    rw [hpq]
    exact caseII h hn p N (by rw [h2'])
  · -- case (3): `a + 1 = 2p`, `r = n - 3p ≥ 1`
    have hpq : n - q = 2 * p := by omega
    rw [hpq]
    exact caseIII h p (n - 3 * p) (by omega) (by omega) (by omega)

/-- The induced homomorphism from the Artin group of type `I₂(N)`. -/
def dihedralRels (N : ℕ) : Set (FreeGroup (Fin 2)) :=
  {alt N (FreeGroup.of 0) (FreeGroup.of 1) * (alt N (FreeGroup.of 1) (FreeGroup.of 0))⁻¹}

theorem conj_6_35_hom (n a b N : ℕ) (hyp : Hyp n a b N) :
    ∃ φ : PresentedGroup (dihedralRels N) →* BraidGroup n,
      φ (PresentedGroup.of 0) = halfTwist n 1 (a + 1) ∧ φ (PresentedGroup.of 1) = halfTwist n b n := by
  let f : Fin 2 → BraidGroup n := fun i => if i = 0 then halfTwist n 1 (a + 1) else halfTwist n b n
  have hrel : ∀ r ∈ dihedralRels N, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [dihedralRels, Set.mem_singleton_iff] at hr
    subst hr
    rw [map_mul, map_inv, map_alt, map_alt, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      mul_inv_eq_one]
    exact conj_6_35_group n a b N hyp
  refine ⟨PresentedGroup.toGroup hrel, ?_, ?_⟩
  · rw [PresentedGroup.toGroup.of]; simp [f]
  · rw [PresentedGroup.toGroup.of]; simp [f]

/-! ## The monoid statement, conditional on Garside's embedding theorem -/

/-- The canonical map `Br⁺_n → Br_n`. -/
def plusToGroup (n : ℕ) : BrPlus n →* BraidGroup n :=
  PresentedMonoid.lift (fun i => PresentedGroup.of i) (by
    intro x y hxy
    obtain ⟨i, j, ⟨hij, rfl, rfl⟩ | ⟨hij, rfl, rfl⟩⟩ := hxy
    · simp only [map_mul, FreeMonoid.lift_eval_of]
      have := PresentedGroup.one_of_mem (rels := braidRels n)
        (x := FreeGroup.of i * FreeGroup.of j * FreeGroup.of i
          * (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ⟨i, j, Or.inl ⟨hij, rfl⟩⟩
      simp only [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this
    · simp only [map_mul, FreeMonoid.lift_eval_of]
      have := PresentedGroup.one_of_mem (rels := braidRels n)
        (x := FreeGroup.of i * FreeGroup.of j * (FreeGroup.of j * FreeGroup.of i)⁻¹)
        ⟨i, j, Or.inr ⟨hij, rfl⟩⟩
      simp only [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this)

lemma plusToGroup_σp (n i : ℕ) : plusToGroup n (σp n i) = σ n i := by
  unfold σp σ
  split_ifs
  · rfl
  · exact map_one _

lemma plusToGroup_halfTwistP (n u v : ℕ) : plusToGroup n (halfTwistP n u v) = halfTwist n u v := by
  rw [halfTwistP, map_halfTwistG]; simp only [plusToGroup_σp]; rfl

/-- **Conjecture 6.35 as printed (in `Br⁺_n`)**, assuming Garside's theorem that `Br⁺_n → Br_n` is
injective (Garside 1969); that theorem is a hypothesis here, not proved in Lean. -/
theorem conj_6_35_monoid_of_garside (n a b N : ℕ) (hyp : Hyp n a b N)
    (garside : Function.Injective (plusToGroup n)) :
    alt N (halfTwistP n 1 (a + 1)) (halfTwistP n b n) = alt N (halfTwistP n b n) (halfTwistP n 1 (a + 1)) := by
  apply garside
  rw [map_alt, map_alt, plusToGroup_halfTwistP, plusToGroup_halfTwistP]
  exact conj_6_35_group n a b N hyp

end BGL
```

### `BraidMonoid.lean`

```lean
import BraidStatement
import BraidPositiveCase3

namespace BGL

/-- The generators of the positive braid monoid, in zero-based form. -/
def pgen (n : ℕ) : ℕ → BrPlus n := fun i => σp n (i + 1)

lemma pgen_eq (n i : ℕ) (hi : i < n - 1) :
    pgen n i = PresentedMonoid.of (braidRelsPlus n) (⟨i, hi⟩ : Fin (n - 1)) := by
  unfold pgen σp
  split_ifs
  · congr 1
  · omega

lemma BR_pgen (n : ℕ) : BR (pgen n) (n - 1) where
  braid i hi := by
    rw [pgen_eq n i (by omega), pgen_eq n (i + 1) hi]
    let a : Fin (n - 1) := ⟨i, by omega⟩
    let b : Fin (n - 1) := ⟨i + 1, hi⟩
    have rel : braidRelsPlus n (FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of a)
        (FreeMonoid.of b * FreeMonoid.of a * FreeMonoid.of b) :=
      ⟨a, b, Or.inl ⟨rfl, rfl, rfl⟩⟩
    simpa only [map_mul, PresentedMonoid.of, a, b] using PresentedMonoid.mk_eq_mk_of_rel rel
  comm i j hij hj := by
    rw [pgen_eq n i (by omega), pgen_eq n j hj]
    let a : Fin (n - 1) := ⟨i, by omega⟩
    let b : Fin (n - 1) := ⟨j, hj⟩
    have rel : braidRelsPlus n (FreeMonoid.of a * FreeMonoid.of b)
        (FreeMonoid.of b * FreeMonoid.of a) :=
      ⟨a, b, Or.inr ⟨hij, rfl, rfl⟩⟩
    simpa only [map_mul, PresentedMonoid.of, a, b] using PresentedMonoid.mk_eq_mk_of_rel rel

lemma halfTwistP_eq_H (n u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v) :
    halfTwistP n u v = H (pgen n) (u - 1) (v - u + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  rw [halfTwistP, halfTwistG_eq, H, Hw, show u + d - u + 1 = d + 1 by omega]
  apply wp_congr
  intro x _
  simp only [pgen, sh_apply]
  congr 1
  omega

/-- Conjecture 6.35 in the presented positive braid monoid, for all three cases. -/
theorem conj_6_35_monoid (n a b N : ℕ) (hyp : Hyp n a b N) :
    alt N (halfTwistP n 1 (a + 1)) (halfTwistP n b n) =
      alt N (halfTwistP n b n) (halfTwistP n 1 (a + 1)) := by
  obtain ⟨hb, hba, han, ha, hcase⟩ := hyp
  have h := BR_pgen n
  have hn : 2 ≤ n := by omega
  set p := b - 1 with hp
  set q := n - 1 - a with hq
  have hX : halfTwistP n 1 (a + 1) = Hw (pgen n) (n - q) := by
    rw [halfTwistP_eq_H n 1 (a + 1) le_rfl (by omega), show 1 - 1 = 0 from rfl, H_zero]
    congr 1
    omega
  have hY : halfTwistP n b n = H (pgen n) p (n - p) := by
    rw [halfTwistP_eq_H n b n hb (by omega)]
    congr 1
    omega
  rw [hX, hY]
  rcases hcase with ⟨h1, _, ⟨m, hm⟩⟩ | ⟨h2, h2', k, hk, rfl⟩ | ⟨h3, h3', rfl⟩
  · have hmn : m * (p + q) = n := by
      have : n + b - a - 2 = p + q := by omega
      rw [this, hm] at h1
      nlinarith
    rw [hm, ← two_mul, alt_two_mul, alt_two_mul]
    exact caseI_positive h hn p q m hmn
  · rw [show n - q = n - p by omega]
    exact caseII_positive h hn p k hk h2'.symm
  · rw [show n - q = 2 * p by omega]
    exact caseIII_positive h p (n - 3 * p) (by omega) (by omega) (by omega)

/-- The single relation of the positive dihedral Artin presentation. -/
def dihedralRelsPlus (N : ℕ) (x y : FreeMonoid (Fin 2)) : Prop :=
  x = alt N (FreeMonoid.of 0) (FreeMonoid.of 1) ∧
    y = alt N (FreeMonoid.of 1) (FreeMonoid.of 0)

/-- Positive Artin monoid of type I₂(N). -/
abbrev DihedralPlus (N : ℕ) := PresentedMonoid (dihedralRelsPlus N)

/-- The homomorphism from the positive dihedral Artin presentation with the prescribed images. -/
theorem conj_6_35_monoid_hom (n a b N : ℕ) (hyp : Hyp n a b N) :
    ∃ φ : DihedralPlus N →* BrPlus n,
      φ (PresentedMonoid.of (dihedralRelsPlus N) 0) = halfTwistP n 1 (a + 1) ∧
      φ (PresentedMonoid.of (dihedralRelsPlus N) 1) = halfTwistP n b n := by
  let f : Fin 2 → BrPlus n := fun i =>
    if i = 0 then halfTwistP n 1 (a + 1) else halfTwistP n b n
  have hrel : ∀ x y, dihedralRelsPlus N x y → FreeMonoid.lift f x = FreeMonoid.lift f y := by
    intro x y hxy
    obtain ⟨rfl, rfl⟩ := hxy
    simp only [map_alt, FreeMonoid.lift_eval_of, f]
    simpa using conj_6_35_monoid n a b N hyp
  refine ⟨PresentedMonoid.lift f hrel, ?_, ?_⟩ <;> rw [PresentedMonoid.lift_of] <;> simp [f]

end BGL
```

### `BraidNonVacuity.lean`

```lean
import BraidStatement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Non-vacuity

1. The hypotheses `Hyp n a b N` hold for infinitely many `(n, a, b, N)` in each of the three
   cases (explicit families).
2. For small instances of each case, the permutation representation `Br_n → S_n`
   (`σ_i ↦ (i i+1)`) is a group homomorphism (relations checked by `decide`), and the kernel
   computes that the relation of length `N - 1` FAILS in `Br_n`, while the relation of length `N`
   holds in `S_n` (consistent with the theorem).  So the generators are not degenerate and the
   proved relation is not a formal consequence of a shorter one.
-/

namespace BGL

/-! ## The hypotheses are satisfiable -/

theorem hyp_case1_family (m : ℕ) (hm : 2 ≤ m) : Hyp (2 * m) m 2 4 := by
  refine ⟨by omega, by omega, by omega, by omega, Or.inl ⟨?_, by omega, ⟨2, rfl⟩⟩⟩
  rw [show 2 * m + 2 - m - 2 = m by omega]; ring

theorem hyp_case2_family (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    Hyp ((2 * k + 1) * p) (2 * k * p - 1) (p + 1) (2 * k + 1) := by
  have h1 : 2 * p ≤ 2 * k * p := by nlinarith
  refine ⟨by omega, by omega, ?_, by omega, Or.inr (Or.inl ⟨?_, ?_, ⟨k, hk, by ring⟩⟩)⟩
  · have : (2 * k + 1) * p = 2 * k * p + p := by ring
    omega
  · have : (2 * k + 1) * p = 2 * k * p + p := by ring
    omega
  · simp

theorem hyp_case3_family (p r : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r) :
    Hyp (3 * p + r) (2 * p - 1) (p + 1) 6 := by
  refine ⟨by omega, by omega, by omega, by omega, Or.inr (Or.inr ⟨by omega, by omega, rfl⟩)⟩

/-! ## The permutation representation -/

/-- `σ_i ↦ (i, i+1)` (0-based `k ↦ (k, k+1)`). -/
def permGen (n : ℕ) (k : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩

def RelsOK (n : ℕ) : Prop :=
  ∀ i j : Fin (n - 1),
    (i.val + 1 = j.val → permGen n i * permGen n j * permGen n i = permGen n j * permGen n i * permGen n j) ∧
    (i.val + 2 ≤ j.val → permGen n i * permGen n j = permGen n j * permGen n i)

lemma relsOK_lift (n : ℕ) (h : RelsOK n) : ∀ r ∈ braidRels n, FreeGroup.lift (permGen n) r = 1 := by
  intro r ⟨i, j, hr⟩
  rcases hr with ⟨hij, rfl⟩ | ⟨hij, rfl⟩
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]; exact (h i j).1 hij
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [mul_inv_eq_one]; exact (h i j).2 hij

/-- The permutation representation `Br_n → S_n`. -/
def permRep (n : ℕ) (h : RelsOK n) : BraidGroup n →* Equiv.Perm (Fin n) :=
  PresentedGroup.toGroup (relsOK_lift n h)

/-- `σ_i ↦ (i, i+1)` as a function of `i : ℕ` (1-based). -/
def permSigma (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : 1 ≤ i ∧ i < n then Equiv.swap ⟨i - 1, by omega⟩ ⟨i, by omega⟩ else 1

lemma permRep_σ (n : ℕ) (h : RelsOK n) (i : ℕ) : permRep n h (σ n i) = permSigma n i := by
  unfold σ permSigma
  split_ifs with hi
  · rw [permRep, PresentedGroup.toGroup.of]; unfold permGen
    congr 1; rw [Fin.ext_iff]; simp; omega
  · exact map_one _

lemma permRep_halfTwist (n : ℕ) (h : RelsOK n) (u v : ℕ) :
    permRep n h (halfTwist n u v) = halfTwistG (permSigma n) u v := by
  rw [halfTwist, map_halfTwistG]; simp only [permRep_σ]

lemma permRep_alt (n : ℕ) (h : RelsOK n) (N u v u' v' : ℕ) :
    permRep n h (alt N (halfTwist n u v) (halfTwist n u' v'))
      = alt N (halfTwistG (permSigma n) u v) (halfTwistG (permSigma n) u' v') := by
  rw [map_alt, permRep_halfTwist, permRep_halfTwist]

theorem relsOK4 : RelsOK 4 := by unfold RelsOK; decide
theorem relsOK6 : RelsOK 6 := by unfold RelsOK; decide
theorem relsOK7 : RelsOK 7 := by unfold RelsOK; decide

/-- Non-triviality certificate: if the images of `alt k X Y` and `alt k Y X` in `S_n` differ,
then the relation of length `k` fails in `Br_n`. -/
lemma alt_ne_of_perm (n : ℕ) (h : RelsOK n) (k u v u' v' : ℕ)
    (hne : alt k (halfTwistG (permSigma n) u v) (halfTwistG (permSigma n) u' v')
      ≠ alt k (halfTwistG (permSigma n) u' v') (halfTwistG (permSigma n) u v)) :
    alt k (halfTwist n u v) (halfTwist n u' v') ≠ alt k (halfTwist n u' v') (halfTwist n u v) := by
  intro heq
  apply hne
  rw [← permRep_alt n h, ← permRep_alt n h, heq]

/-! ## The half-twist words map to the reversals of their intervals

`hwL m` has `m(m-1)/2` letters, and its image in `S_n` is the reversal of `[u, v]`, which has
`m(m-1)/2` inversions (`m = v - u + 1`); so the word is a reduced expression of `w∘^{[u,v-1]}`.
The length count is proved for all `m`; the image is checked by the kernel for all
`1 ≤ u ≤ v ≤ n ≤ 7`. -/

lemma hwL_length (m : ℕ) : 2 * (hwL m).length = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hd : ∀ k, (dscL k).length = k := by
      intro k; induction k with
      | zero => rfl
      | succ k ihk => simp [dscL, ihk]
    rw [hwL, List.length_append, hd, Nat.mul_add, ih]
    rcases m with _ | m
    · rfl
    · simp only [Nat.add_sub_cancel]; ring

/-- Reversal of the strands `u, …, v` (1-based), on 0-based points. -/
def revFun (u v : ℕ) (x : ℕ) : ℕ := if u ≤ x + 1 ∧ x + 1 ≤ v then u + v - 2 - x else x

theorem halfTwist_image_reversal :
    (∀ u v : Fin 5, 1 ≤ u.val → u.val ≤ v.val →
      ∀ x : Fin 4, ((halfTwistG (permSigma 4) u v) x).val = revFun u v x.val) ∧
    (∀ u v : Fin 7, 1 ≤ u.val → u.val ≤ v.val →
      ∀ x : Fin 6, ((halfTwistG (permSigma 6) u v) x).val = revFun u v x.val) ∧
    (∀ u v : Fin 8, 1 ≤ u.val → u.val ≤ v.val →
      ∀ x : Fin 7, ((halfTwistG (permSigma 7) u v) x).val = revFun u v x.val) := by
  decide +kernel

/-! ## Small instances of each case -/

/-- Case (1), `n = 4, a = 2, b = 2, N = 4`. -/
theorem instance_case1 :
    Hyp 4 2 2 4 ∧
    alt 4 (halfTwist 4 1 3) (halfTwist 4 2 4) = alt 4 (halfTwist 4 2 4) (halfTwist 4 1 3) ∧
    alt 3 (halfTwist 4 1 3) (halfTwist 4 2 4) ≠ alt 3 (halfTwist 4 2 4) (halfTwist 4 1 3) ∧
    alt 4 (halfTwistG (permSigma 4) 1 3) (halfTwistG (permSigma 4) 2 4)
      = alt 4 (halfTwistG (permSigma 4) 2 4) (halfTwistG (permSigma 4) 1 3) := by
  have hy : Hyp 4 2 2 4 := hyp_case1_family 2 le_rfl
  exact ⟨hy, conj_6_35_group 4 2 2 4 hy, alt_ne_of_perm 4 relsOK4 3 1 3 2 4 (by decide +kernel), by decide +kernel⟩

/-- Case (1) with `b = 1`: `n = 4, a = 2, b = 1, N = 8`. -/
theorem instance_case1b :
    Hyp 4 2 1 8 ∧
    alt 8 (halfTwist 4 1 3) (halfTwist 4 1 4) = alt 8 (halfTwist 4 1 4) (halfTwist 4 1 3) ∧
    alt 7 (halfTwist 4 1 3) (halfTwist 4 1 4) ≠ alt 7 (halfTwist 4 1 4) (halfTwist 4 1 3) := by
  have hy : Hyp 4 2 1 8 :=
    ⟨by omega, by omega, by omega, by omega, Or.inl ⟨by norm_num, by norm_num, ⟨4, rfl⟩⟩⟩
  exact ⟨hy, conj_6_35_group 4 2 1 8 hy, alt_ne_of_perm 4 relsOK4 7 1 3 1 4 (by decide +kernel)⟩

/-- Case (2), `n = 6, a = 3, b = 3, N = 3`. -/
theorem instance_case2 :
    Hyp 6 3 3 3 ∧
    alt 3 (halfTwist 6 1 4) (halfTwist 6 3 6) = alt 3 (halfTwist 6 3 6) (halfTwist 6 1 4) ∧
    alt 2 (halfTwist 6 1 4) (halfTwist 6 3 6) ≠ alt 2 (halfTwist 6 3 6) (halfTwist 6 1 4) ∧
    alt 3 (halfTwistG (permSigma 6) 1 4) (halfTwistG (permSigma 6) 3 6)
      = alt 3 (halfTwistG (permSigma 6) 3 6) (halfTwistG (permSigma 6) 1 4) := by
  have hy : Hyp 6 3 3 3 := hyp_case2_family 2 1 le_rfl le_rfl
  exact ⟨hy, conj_6_35_group 6 3 3 3 hy, alt_ne_of_perm 6 relsOK6 2 1 4 3 6 (by decide +kernel), by decide +kernel⟩

/-- Case (3), `n = 7, a = 3, b = 3, N = 6`. -/
theorem instance_case3 :
    Hyp 7 3 3 6 ∧
    alt 6 (halfTwist 7 1 4) (halfTwist 7 3 7) = alt 6 (halfTwist 7 3 7) (halfTwist 7 1 4) ∧
    alt 5 (halfTwist 7 1 4) (halfTwist 7 3 7) ≠ alt 5 (halfTwist 7 3 7) (halfTwist 7 1 4) ∧
    alt 6 (halfTwistG (permSigma 7) 1 4) (halfTwistG (permSigma 7) 3 7)
      = alt 6 (halfTwistG (permSigma 7) 3 7) (halfTwistG (permSigma 7) 1 4) := by
  have hy : Hyp 7 3 3 6 := hyp_case3_family 2 1 le_rfl le_rfl
  exact ⟨hy, conj_6_35_group 7 3 3 6 hy, alt_ne_of_perm 7 relsOK7 5 1 4 3 7 (by decide +kernel), by decide +kernel⟩

end BGL
```

### `BraidMain.lean`

```lean
import BraidNonVacuity
import BraidMonoid

/-! # Endpoints of the MathDB 375588 formalization, with their axioms -/

open BGL

#check @BGL.braidRels
#check @BGL.BraidGroup
#check @BGL.σ
#check @BGL.descProd
#check @BGL.halfTwistG
#check @BGL.halfTwist
#check @BGL.alt
#print BGL.Hyp
#check @BGL.conj_6_35_group
#check @BGL.conj_6_35_hom
#check @BGL.plusToGroup
#check @BGL.halfTwistP
#check @BGL.conj_6_35_monoid_of_garside
#check @BGL.hyp_case1_family
#check @BGL.hyp_case2_family
#check @BGL.hyp_case3_family
#check @BGL.hwL_length
#check @BGL.halfTwist_image_reversal
#check @BGL.instance_case1
#check @BGL.instance_case1b
#check @BGL.instance_case2
#check @BGL.instance_case3

#print axioms BGL.conj_6_35_group
#print axioms BGL.conj_6_35_hom
#print axioms BGL.conj_6_35_monoid_of_garside
#print axioms BGL.caseI
#print axioms BGL.caseII
#print axioms BGL.caseIII
#print axioms BGL.hyp_case1_family
#print axioms BGL.hyp_case2_family
#print axioms BGL.hyp_case3_family
#print axioms BGL.hwL_length
#print axioms BGL.halfTwist_image_reversal
#print axioms BGL.instance_case1
#print axioms BGL.instance_case1b
#print axioms BGL.instance_case2
#print axioms BGL.instance_case3

#check @BGL.braidRelsPlus
#check @BGL.BrPlus
#check @BGL.dihedralRelsPlus
#check @BGL.DihedralPlus
#check @BGL.caseI_positive
#check @BGL.caseII_positive
#check @BGL.caseIII_positive
#check @BGL.conj_6_35_monoid
set_option pp.funBinderTypes true in
#check @BGL.conj_6_35_monoid_hom

#print axioms BGL.caseI_positive
#print axioms BGL.caseII_positive
#print axioms BGL.caseIII_positive
#print axioms BGL.conj_6_35_monoid
#print axioms BGL.conj_6_35_monoid_hom
```

