# Lean source appendix (MathDB 337947)

Modules in import order, byte-identical to `src/`. Compile each with the pinned Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 in this order.

### `KEStatement.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic

/-!
# The statement of Conjecture 4.6 of Brosowsky–Chepuri–Mason (arXiv:1712.05037)

Definitions copied verbatim from the required endpoint of the review.
-/

open Matrix

namespace KEss

/-- minor with row set I and column set J (sorted embeddings) -/
noncomputable def minor {n} (M : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n))
    (h : I.card = J.card) : ℝ :=
  (M.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h.symm)).det

def interval {n} (a ℓ : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + ℓ)

def KEssential {n} (k : ℕ) (I J : Finset (Fin n)) (h : I.card = J.card) : Prop :=
  I.card ≤ k ∧ ∃ M : Matrix (Fin n) (Fin n) ℝ, minor M I J h ≤ 0 ∧
    ∀ (I' J' : Finset (Fin n)) (h' : I'.card = J'.card), I'.card ≤ k → (I', J') ≠ (I, J) →
      0 < minor M I' J' h'

/-- The interval `[a, a+ℓ)` inside `Fin n` has `ℓ` elements when `a + ℓ ≤ n`. -/
theorem card_interval {n a ℓ : ℕ} (h : a + ℓ ≤ n) : (interval (n := n) a ℓ).card = ℓ := by
  have hmap : (interval (n := n) a ℓ).map Fin.valEmbedding = Finset.Ico a (a + ℓ) := by
    ext x
    simp only [Finset.mem_map, interval, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
  omega

/-- Sanity check: a `0 × 0` minor equals `1`. -/
theorem minor_empty {n} (M : Matrix (Fin n) (Fin n) ℝ) :
    minor M ∅ ∅ rfl = 1 := by
  unfold minor
  have : IsEmpty (Fin (∅ : Finset (Fin n)).card) := by rw [Finset.card_empty]; infer_instance
  exact Matrix.det_isEmpty

end KEss
```

### `KEExpand.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.ContinuousOn

/-!
# Expansion of the determinant of a rectangular product over functions

`det (M * N) = ∑_{p : Fin ℓ → Fin m} (∏ i, N (p i) i) * det (M.submatrix id p)`;
this replaces the subset form of the Cauchy–Binet formula.  We also record the
weight lemmas used to identify the lowest-order terms, and an abstract
"leading coefficient positive ⇒ eventually positive" lemma.
-/

open Matrix Finset Filter Topology

namespace KEss

section Expand

variable {R : Type*} [CommRing R]

theorem det_mul_expand {ℓ m : ℕ} (M : Matrix (Fin ℓ) (Fin m) R) (N : Matrix (Fin m) (Fin ℓ) R) :
    (M * N).det = ∑ p : Fin ℓ → Fin m, (∏ i, N (p i) i) * (M.submatrix id p).det := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero_of_not_injective {ℓ m : ℕ} (M : Matrix (Fin ℓ) (Fin m) R)
    {p : Fin ℓ → Fin m} (hp : ¬ Function.Injective p) : (M.submatrix id p).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hp
    obtain ⟨i, j, h, hne⟩ := hp
    exact ⟨i, j, h, hne⟩
  exact det_zero_of_column_eq hne (fun k => by simp [hij])

theorem sum_comp_eq_det_mul_det {ℓ m : ℕ} (M : Matrix (Fin ℓ) (Fin m) R)
    (N : Matrix (Fin m) (Fin ℓ) R) (ι : Fin ℓ → Fin m) :
    ∑ q : Fin ℓ → Fin ℓ, (∏ i, N (ι (q i)) i) * (M.submatrix id (ι ∘ q)).det =
      (M.submatrix id ι).det * (N.submatrix ι id).det := by
  rw [← det_mul, det_mul_expand]
  rfl

theorem det_mul_diag_mul {ℓ m : ℕ} (M : Matrix (Fin ℓ) (Fin m) R) (G : Matrix (Fin m) (Fin ℓ) R)
    (t : R) (w : Fin m → ℕ) :
    (M * (diagonal (fun d => t ^ w d) * G)).det =
      ∑ p : Fin ℓ → Fin m, t ^ (∑ i, w (p i)) * ((∏ i, G (p i) i) * (M.submatrix id p).det) := by
  rw [det_mul_expand]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [diagonal_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- The lowest-order part of the expansion is a sum over the functions that factor
through one fixed injection `ι`. -/
theorem sum_filter_eq_sum_comp {ℓ m : ℕ} (c : (Fin ℓ → Fin m) → R)
    (W : (Fin ℓ → Fin m) → ℕ) (s : ℕ) (ι : Fin ℓ → Fin m) (hι : Function.Injective ι)
    (h : ∀ p, c p ≠ 0 → (W p ≤ s ↔ ∃ q, p = ι ∘ q)) :
    ∑ p ∈ univ.filter (fun p => W p ≤ s), c p = ∑ q : Fin ℓ → Fin ℓ, c (ι ∘ q) := by
  have hinj : Function.Injective (fun q : Fin ℓ → Fin ℓ => ι ∘ q) :=
    fun q₁ q₂ hq => funext fun i => hι (congrFun hq i)
  rw [← Finset.sum_image (f := c) (fun q₁ _ q₂ _ hq => hinj hq),
    ← Finset.univ_inter (Finset.image _ _), ← Finset.sum_ite_mem, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : c p = 0
  · simp [hc]
  · have hp := h p hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_cases hw : W p ≤ s
    · obtain ⟨q, hq⟩ := hp.1 hw
      rw [ite_eq_left hw, ite_eq_left ⟨q, hq.symm⟩]
    · have : ¬ ∃ q, ι ∘ q = p := fun ⟨q, hq⟩ => hw (hp.2 ⟨q, hq.symm⟩)
      rw [ite_eq_right hw, ite_eq_right this]

/-- Same, for two injections whose images are never both hit by a contributing function. -/
theorem sum_filter_eq_sum_comp_two {ℓ m : ℕ} (c : (Fin ℓ → Fin m) → R)
    (W : (Fin ℓ → Fin m) → ℕ) (s : ℕ) (ι₁ ι₂ : Fin ℓ → Fin m)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (h : ∀ p, c p ≠ 0 → (W p ≤ s ↔ (∃ q, p = ι₁ ∘ q) ∨ ∃ q, p = ι₂ ∘ q))
    (hdisj : ∀ p, c p ≠ 0 → (∃ q, p = ι₁ ∘ q) → ¬ ∃ q, p = ι₂ ∘ q) :
    ∑ p ∈ univ.filter (fun p => W p ≤ s), c p =
      ∑ q : Fin ℓ → Fin ℓ, c (ι₁ ∘ q) + ∑ q : Fin ℓ → Fin ℓ, c (ι₂ ∘ q) := by
  have key : ∀ ι : Fin ℓ → Fin m, Function.Injective ι →
      ∑ q : Fin ℓ → Fin ℓ, c (ι ∘ q) = ∑ p, if ∃ q, p = ι ∘ q then c p else 0 := by
    intro ι hι
    have hinj : Function.Injective (fun q : Fin ℓ → Fin ℓ => ι ∘ q) :=
      fun q₁ q₂ hq => funext fun i => hι (congrFun hq i)
    rw [← Finset.sum_image (f := c) (fun q₁ _ q₂ _ hq => hinj hq),
      ← Finset.univ_inter (Finset.image _ _), ← Finset.sum_ite_mem]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_cases hq : ∃ q, p = ι ∘ q
    · obtain ⟨q, hq'⟩ := hq
      rw [ite_eq_left ⟨q, hq'.symm⟩, ite_eq_left ⟨q, hq'⟩]
    · have : ¬ ∃ q, ι ∘ q = p := fun ⟨q, h'⟩ => hq ⟨q, h'.symm⟩
      rw [ite_eq_right this, ite_eq_right hq]
  rw [key ι₁ hι₁, key ι₂ hι₂, ← Finset.sum_add_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hc : c p = 0
  · simp [hc]
  · have hp := h p hc
    have hd := hdisj p hc
    by_cases h1 : ∃ q, p = ι₁ ∘ q
    · rw [ite_eq_left (hp.2 (Or.inl h1)), ite_eq_left h1, ite_eq_right (hd h1), add_zero]
    · by_cases h2 : ∃ q, p = ι₂ ∘ q
      · rw [ite_eq_left (hp.2 (Or.inr h2)), ite_eq_right h1, ite_eq_left h2, zero_add]
      · have : ¬ W p ≤ s := fun hw => (hp.1 hw).elim h1 h2
        rw [ite_eq_right this, ite_eq_right h1, ite_eq_right h2, add_zero]

end Expand

section Weights

theorem sum_le_sum_of_injective (w : ℕ → ℕ) (hw : Monotone w) :
    ∀ (ℓ : ℕ) (p : Fin ℓ → ℕ), Function.Injective p → ∑ i : Fin ℓ, w i ≤ ∑ i, w (p i)
  | 0, _, _ => by simp
  | ℓ + 1, p, hp => by
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max p
    have hge : ℓ ≤ p i₀ := by
      have hsub : Finset.univ.image p ⊆ Finset.range (p i₀ + 1) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (hi₀ i))
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin,
        Finset.card_range] at this
      omega
    have ih := sum_le_sum_of_injective w hw ℓ (fun j => p (i₀.succAbove j))
      (hp.comp Fin.succAbove_right_injective)
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ i₀]
    simp only [Fin.val_castSucc, Fin.val_last]
    have := hw hge
    omega

theorem lt_of_sum_min_le (r : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ r) (p : Fin ℓ → ℕ)
    (hp : Function.Injective p)
    (hW : ∑ i, min (p i) r ≤ ∑ i : Fin ℓ, min (i : ℕ) r) : ∀ i, p i < ℓ := by
  cases ℓ with
  | zero => intro i; exact i.elim0
  | succ ℓ =>
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max p
    have ih := sum_le_sum_of_injective (fun x => min x r) (fun a b h => min_le_min_right r h) ℓ
      (fun j => p (i₀.succAbove j)) (hp.comp Fin.succAbove_right_injective)
    rw [Fin.sum_univ_succAbove _ i₀, Fin.sum_univ_castSucc] at hW
    simp only [Fin.val_castSucc, Fin.val_last] at hW
    intro i
    have := hi₀ i
    omega

/-- An injection `Fin (r+1) → Fin (r+2)` misses exactly one value. -/
theorem exists_image_eq_erase {r : ℕ} (p : Fin (r + 1) → Fin (r + 2))
    (hp : Function.Injective p) : ∃ v, Finset.univ.image p = Finset.univ.erase v := by
  have hcard : (Finset.univ.image p)ᶜ.card = 1 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hp]
    simp
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hcard
  refine ⟨v, ?_⟩
  ext x
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro hx hxv
    subst hxv
    have : x ∈ (Finset.univ.image p)ᶜ := hv ▸ Finset.mem_singleton_self x
    exact (Finset.mem_compl.1 this) hx
  · intro hxv
    by_contra hx
    have : x ∈ (Finset.univ.image p)ᶜ := Finset.mem_compl.2 hx
    rw [hv] at this
    exact hxv (Finset.mem_singleton.1 this)

end Weights

section Eventually

/-- If the coefficients `c p` of `t ^ W p` vanish below degree `s` and the degree-`s`
coefficient is positive, the sum is positive for all small `t > 0`. -/
theorem eventually_pos_of_leading {ι : Type*} [Fintype ι] (W : ι → ℕ) (c : ι → ℝ) (s : ℕ)
    (hW : ∀ p, c p ≠ 0 → s ≤ W p) (hL : 0 < ∑ p ∈ univ.filter (fun p => W p ≤ s), c p) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ p, t ^ W p * c p := by
  set g : ℝ → ℝ := fun t => ∑ p, t ^ (W p - s) * c p with hg
  have hcont : Continuous g := by
    simp only [hg]
    fun_prop
  have hg0 : g 0 = ∑ p ∈ univ.filter (fun p => W p ≤ s), c p := by
    simp only [hg, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : W p ≤ s
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have : W p - s ≠ 0 := by omega
      simp [h, zero_pow this]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < g t :=
    (hcont.tendsto 0).eventually (lt_mem_nhds (hg0 ▸ hL))
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := nhdsWithin_le_nhds hev
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [h1, h2] with t ht1 ht2
  have : ∑ p, t ^ W p * c p = t ^ s * g t := by
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : c p = 0
    · simp [hc]
    · rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (hW p hc)]
  rw [this]
  exact mul_pos (pow_pos ht2 s) ht1

end Eventually

end KEss
```

### `KEDivDiff.lean`

```lean
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Divided differences on integer nodes

`dd S f = ∑_{y ∈ S} f y / ∏_{z ∈ S \ {y}} (y - z)` (the barycentric formula (2) of the proof).
We prove: it is the top coefficient of the Lagrange interpolant; the two-point recurrence;
the refinement identity (5); and identity (9):
`det [x^0, …, x^{r-1}, f(x)] = det (Vandermonde x) * dd`.
-/

open Finset Polynomial Matrix

namespace KEss

/-- The divided difference of `f` on the finite node set `S ⊆ ℤ` (barycentric formula). -/
noncomputable def dd (S : Finset ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ y ∈ S, f y / ∏ z ∈ S.erase y, ((y : ℝ) - z)

theorem injOn_intCast (S : Finset ℤ) : Set.InjOn (fun z : ℤ => (z : ℝ)) S :=
  fun _ _ _ _ h => Int.cast_injective h

theorem dd_eq_coeff (S : Finset ℤ) (f : ℤ → ℝ) :
    dd S f = (Lagrange.interpolate S (fun z : ℤ => (z : ℝ)) f).coeff (S.card - 1) := by
  rw [Lagrange.coeff_eq_sum (injOn_intCast S)
    (Lagrange.degree_interpolate_lt _ (injOn_intCast S))]
  unfold dd
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Lagrange.eval_interpolate_at_node _ (injOn_intCast S) hy]

theorem dd_poly (S : Finset ℤ) (P : ℝ[X]) (hP : P.degree < S.card) :
    dd S (fun z => P.eval (z : ℝ)) = P.coeff (S.card - 1) := by
  rw [Lagrange.coeff_eq_sum (injOn_intCast S) hP]
  rfl

theorem dd_congr (S : Finset ℤ) {f g : ℤ → ℝ} (h : ∀ y ∈ S, f y = g y) : dd S f = dd S g := by
  unfold dd
  exact Finset.sum_congr rfl fun y hy => by rw [h y hy]

theorem dd_eq_zero_of_eq_zero (S : Finset ℤ) {f : ℤ → ℝ} (h : ∀ y ∈ S, f y = 0) : dd S f = 0 := by
  unfold dd
  exact Finset.sum_eq_zero fun y hy => by rw [h y hy, zero_div]

/-- The two-point recurrence for divided differences. -/
theorem dd_recurrence (S : Finset ℤ) (f : ℤ → ℝ) {i j : ℤ} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    ((i : ℝ) - j) * dd S f = dd (S.erase j) f - dd (S.erase i) f := by
  have hcard : 2 ≤ S.card := by
    have : ({i, j} : Finset ℤ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hij] at h2
  obtain ⟨N, hN⟩ : ∃ N, S.card = N + 2 := ⟨S.card - 2, by omega⟩
  have hcj : (S.erase j).card = N + 1 := by rw [Finset.card_erase_of_mem hj]; omega
  have hci : (S.erase i).card = N + 1 := by rw [Finset.card_erase_of_mem hi]; omega
  have hij' : (i : ℝ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
  set Pj := Lagrange.interpolate (S.erase j) (fun z : ℤ => (z : ℝ)) f
  set Pi := Lagrange.interpolate (S.erase i) (fun z : ℤ => (z : ℝ)) f
  have hPj : Pj.coeff (N + 1) = 0 := by
    apply coeff_eq_zero_of_degree_lt
    have := Lagrange.degree_interpolate_lt f (injOn_intCast (S.erase j))
    rwa [hcj] at this
  have hPi : Pi.coeff (N + 1) = 0 := by
    apply coeff_eq_zero_of_degree_lt
    have := Lagrange.degree_interpolate_lt f (injOn_intCast (S.erase i))
    rwa [hci] at this
  rw [dd_eq_coeff S, dd_eq_coeff (S.erase j), dd_eq_coeff (S.erase i), hcj, hci, hN,
    Lagrange.interpolate_eq_add_interpolate_erase _ (injOn_intCast S) hi hj hij]
  simp only [Lagrange.basisDivisor]
  have e1 : (Pj * (C ((i : ℝ) - j)⁻¹ * (X - C (j : ℝ)))).coeff (N + 1) =
      ((i : ℝ) - j)⁻¹ * Pj.coeff N := by
    rw [show Pj * (C ((i : ℝ) - j)⁻¹ * (X - C (j : ℝ))) =
        C ((i : ℝ) - j)⁻¹ * (Pj * (X - C (j : ℝ))) by ring, coeff_C_mul, coeff_mul_X_sub_C, hPj]
    ring
  have e2 : (Pi * (C ((j : ℝ) - i)⁻¹ * (X - C (i : ℝ)))).coeff (N + 1) =
      ((j : ℝ) - i)⁻¹ * Pi.coeff N := by
    rw [show Pi * (C ((j : ℝ) - i)⁻¹ * (X - C (i : ℝ))) =
        C ((j : ℝ) - i)⁻¹ * (Pi * (X - C (i : ℝ))) by ring, coeff_C_mul, coeff_mul_X_sub_C, hPi]
    ring
  have hN2 : N + 2 - 1 = N + 1 := by omega
  have hN1 : N + 1 - 1 = N := by omega
  rw [hN2, hN1, coeff_add, e1, e2]
  have hji : (j : ℝ) - i = -((i : ℝ) - j) := by ring
  rw [hji, inv_neg]
  field_simp
  ring

/-- The refinement identity (5): inserting a missing interior node `z`. -/
theorem dd_refine (S : Finset ℤ) (f : ℤ → ℝ) {x0 xr z : ℤ} (h0 : x0 ∈ S) (hr : xr ∈ S)
    (hz : z ∉ S) (h0z : x0 < z) (hzr : z < xr) :
    ((xr : ℝ) - x0) * dd S f =
      ((z : ℝ) - x0) * dd ((insert z S).erase xr) f +
        ((xr : ℝ) - z) * dd ((insert z S).erase x0) f := by
  have hzY : z ∈ insert z S := Finset.mem_insert_self z S
  have hrY : xr ∈ insert z S := Finset.mem_insert_of_mem hr
  have h0Y : x0 ∈ insert z S := Finset.mem_insert_of_mem h0
  have e1 := dd_recurrence (insert z S) f hrY hzY (by omega)
  have e2 := dd_recurrence (insert z S) f hzY h0Y (by omega)
  rw [Finset.erase_insert hz] at e1 e2
  linear_combination (-((z : ℝ) - x0)) * e1 + ((xr : ℝ) - z) * e2

/-- The matrix with columns `x^0, …, x^{r-1}, g`. -/
def genVand {r : ℕ} (x g : Fin (r + 1) → ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  Matrix.of fun i d => if (d : ℕ) < r then x i ^ (d : ℕ) else g i

/-- Identity (9). -/
theorem det_genVand {r : ℕ} (v : Fin (r + 1) → ℤ) (hv : Function.Injective v) (f : ℤ → ℝ) :
    (genVand (fun i => (v i : ℝ)) (fun i => f (v i))).det =
      (vandermonde (fun i => (v i : ℝ))).det * dd (univ.image v) f := by
  set S := univ.image v with hS
  have hcard : S.card = r + 1 := by
    rw [hS, Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  set P := Lagrange.interpolate S (fun z : ℤ => (z : ℝ)) f with hP
  have hdeg : P.degree < S.card := Lagrange.degree_interpolate_lt _ (injOn_intCast S)
  have hnat : P.natDegree < r + 1 := by
    by_cases h0 : P = 0
    · rw [h0, natDegree_zero]; omega
    · rw [natDegree_lt_iff_degree_lt h0, ← hcard]; exact hdeg
  have heval : ∀ i, P.eval (v i : ℝ) = f (v i) := fun i =>
    Lagrange.eval_interpolate_at_node _ (injOn_intCast S)
      (Finset.mem_image_of_mem v (Finset.mem_univ i))
  set U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    Matrix.of fun e d => if (d : ℕ) < r then (if e = d then 1 else 0) else P.coeff e with hU
  have hfac : genVand (fun i => (v i : ℝ)) (fun i => f (v i)) =
      vandermonde (fun i => (v i : ℝ)) * U := by
    ext i d
    simp only [genVand, hU, Matrix.of_apply, Matrix.mul_apply, vandermonde_apply]
    by_cases hd : (d : ℕ) < r
    · simp only [hd, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [hd, ↓reduceIte]
      rw [← heval i, eval_eq_sum_range' hnat]
      rw [← Fin.sum_univ_eq_sum_range (fun e => P.coeff e * (v i : ℝ) ^ e)]
      exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  have hUt : U.IsUpperTriangular := by
    intro e d hde
    simp only [hU, Matrix.of_apply]
    have : (d : ℕ) < r := by
      have := e.isLt
      have : (d : ℕ) < e := hde
      omega
    rw [ite_eq_left this, ite_eq_right (show e ≠ d from ne_of_gt hde)]
  have hdetU : U.det = P.coeff r := by
    rw [det_of_isUpperTriangular hUt, Fin.prod_univ_castSucc]
    simp only [hU, Matrix.of_apply, Fin.val_castSucc, Fin.val_last, Fin.is_lt,
      lt_irrefl, ↓reduceIte, Finset.prod_const_one, one_mul]
  rw [hfac, det_mul, hdetU, dd_eq_coeff, hcard]
  rfl

theorem det_vandermonde_pos {ℓ : ℕ} (x : Fin ℓ → ℝ) (hx : StrictMono x) :
    0 < (vandermonde x).det := by
  rw [det_vandermonde]
  exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
    sub_pos.2 (hx (Finset.mem_Ioi.1 hj))

end KEss
```

### `KESpline.lean`

```lean
import KEDivDiff
import Mathlib.Data.Int.Interval

/-!
# The discrete spline with exactly one zero divided difference (Lemma 1)

`spline a r` is `r!` times the function `u_a` of (1) in the proof:
`(x-a)(x-a-1)⋯(x-a-r+1)` left of `a`, zero on `[a, a+r]`, and
`(x-a-1)⋯(x-a-r)` right of `a+r`.  We prove: for every `(r+1)`-element node set
`S ⊆ ℤ`, `dd S (spline a r) ≥ 0`, with equality only when `S = [a, a+r]`.
-/

open Finset Polynomial

namespace KEss

/-- `r!` times the discrete binomial spline `u_a` of (1). -/
def spline (a : ℤ) (r : ℕ) (x : ℤ) : ℤ :=
  if x < a then ∏ h ∈ range r, (x - a - h)
  else if x ≤ a + r then 0 else ∏ h ∈ range r, (x - a - 1 - h)

/-- The real-valued spline. -/
noncomputable def u (a : ℤ) (r : ℕ) (x : ℤ) : ℝ := (spline a r x : ℝ)

theorem spline_eq_zero {a : ℤ} {r : ℕ} {x : ℤ} (h1 : a ≤ x) (h2 : x ≤ a + r) :
    spline a r x = 0 := by
  unfold spline
  rw [ite_eq_right (not_lt.2 h1), ite_eq_left h2]

theorem spline_eq_left {a : ℤ} {r : ℕ} {x : ℤ} (h : x < a + r) :
    spline a r x = ∏ h ∈ range r, (x - a - h) := by
  unfold spline
  by_cases hx : x < a
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx, ite_eq_left h.le]
    symm
    apply Finset.prod_eq_zero (i := (x - a).toNat)
    · rw [mem_range]
      omega
    · omega

theorem spline_eq_right {a : ℤ} {r : ℕ} {x : ℤ} (h : a < x) :
    spline a r x = ∏ h ∈ range r, (x - a - 1 - h) := by
  unfold spline
  rw [ite_eq_right (not_lt.2 h.le)]
  by_cases hx : x ≤ a + r
  · rw [ite_eq_left hx]
    symm
    apply Finset.prod_eq_zero (i := (x - a - 1).toNat)
    · rw [mem_range]
      omega
    · omega
  · rw [ite_eq_right hx]

/-- The divided difference of a monic product of `r` linear factors on `r+1` nodes is `1`. -/
theorem dd_prod_window (S : Finset ℤ) (r : ℕ) (hS : S.card = r + 1) (c : ℝ) :
    dd S (fun y => ∏ h ∈ range r, ((y : ℝ) - c - h)) = 1 := by
  set P : ℝ[X] := ∏ h ∈ range r, (X - C (c + h)) with hP
  have hmon : P.Monic := monic_prod_X_sub_C (fun h : ℕ => c + h) (range r)
  have hnat : P.natDegree = r := by
    rw [hP, natDegree_finsetProd_X_sub_C_eq_card, card_range]
  have hdeg : P.degree < S.card := by
    rw [hS]
    refine (degree_le_natDegree).trans_lt ?_
    rw [hnat]
    exact_mod_cast Nat.lt_succ_self r
  have hfun : ∀ y ∈ S, (∏ h ∈ range r, ((y : ℝ) - c - h)) = P.eval (y : ℝ) := by
    intro y _
    rw [hP, eval_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    simp only [eval_sub, eval_X, eval_C]
    ring
  rw [dd_congr S hfun, dd_poly S P hdeg, hS, Nat.add_sub_cancel, ← hnat]
  exact hmon.coeff_natDegree

theorem card_Icc_window (m : ℤ) (r : ℕ) : (Icc m (m + r)).card = r + 1 := by
  rw [Int.card_Icc]
  omega

theorem dd_spline_window_target (a : ℤ) (r : ℕ) : dd (Icc a (a + r)) (u a r) = 0 := by
  apply dd_eq_zero_of_eq_zero
  intro y hy
  rw [mem_Icc] at hy
  simp [u, spline_eq_zero hy.1 hy.2]

theorem dd_spline_window (a m : ℤ) (r : ℕ) (hm : m ≠ a) : dd (Icc m (m + r)) (u a r) = 1 := by
  rcases lt_or_gt_of_ne hm with hlt | hgt
  · rw [← dd_prod_window (Icc m (m + r)) r (card_Icc_window m r) (a : ℝ)]
    apply dd_congr
    intro y hy
    rw [mem_Icc] at hy
    rw [u, spline_eq_left (by omega)]
    push_cast
    rfl
  · rw [← dd_prod_window (Icc m (m + r)) r (card_Icc_window m r) ((a : ℝ) + 1)]
    apply dd_congr
    intro y hy
    rw [mem_Icc] at hy
    rw [u, spline_eq_right (by omega)]
    push_cast
    refine Finset.prod_congr rfl fun h _ => ?_
    ring

/-- Lemma 1, by induction on the spread of the node set. -/
theorem dd_spline_pos_aux (a : ℤ) (r : ℕ) (d : ℕ) :
    ∀ S : Finset ℤ, S.card = r + 1 → (∀ x ∈ S, ∀ y ∈ S, y - x ≤ d) →
      0 ≤ dd S (u a r) ∧ (S ≠ Icc a (a + r) → 0 < dd S (u a r)) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hS hd
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  set m := S.min' hne with hm
  set M := S.max' hne with hM
  have hmS : m ∈ S := Finset.min'_mem S hne
  have hMS : M ∈ S := Finset.max'_mem S hne
  have hmx : ∀ x ∈ S, m ≤ x := fun x hx => Finset.min'_le S x hx
  have hxM : ∀ x ∈ S, x ≤ M := fun x hx => Finset.le_max' S x hx
  by_cases hw : S = Icc m (m + r)
  · by_cases hma : m = a
    · rw [hw, hma, dd_spline_window_target]
      exact ⟨le_refl 0, fun h => absurd rfl h⟩
    · rw [hw, dd_spline_window a m r hma]
      exact ⟨zero_le_one, fun _ => zero_lt_one⟩
  · have hMr : m + r < M := by
      by_contra hcon
      push Not at hcon
      apply hw
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [mem_Icc]
        exact ⟨hmx x hx, (hxM x hx).trans hcon⟩
      · rw [card_Icc_window, hS]
    obtain ⟨z, hzI, hzS⟩ : ∃ z ∈ Icc m M, z ∉ S := by
      by_contra hcon
      push Not at hcon
      have := Finset.card_le_card (show Icc m M ⊆ S from hcon)
      rw [Int.card_Icc, hS] at this
      omega
    rw [mem_Icc] at hzI
    have hmz : m < z := lt_of_le_of_ne hzI.1 (fun h => hzS (h ▸ hmS))
    have hzM : z < M := lt_of_le_of_ne hzI.2 (fun h => hzS (h.symm ▸ hMS))
    have hcardY : (insert z S).card = r + 2 := by
      rw [Finset.card_insert_of_notMem hzS, hS]
    have hL : ((insert z S).erase M).card = r + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hMS), hcardY]
      rfl
    have hR : ((insert z S).erase m).card = r + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hmS), hcardY]
      rfl
    have hdM : M - m ≤ d := hd m hmS M hMS
    have hd' : (M - m - 1).toNat < d := by omega
    have memL : ∀ x ∈ (insert z S).erase M, m ≤ x ∧ x ≤ M - 1 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_insert] at hx
      obtain ⟨hxM', hx'⟩ := hx
      rcases hx' with rfl | hx'
      · omega
      · have := hmx x hx'
        have := hxM x hx'
        omega
    have memR : ∀ x ∈ (insert z S).erase m, m + 1 ≤ x ∧ x ≤ M := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_insert] at hx
      obtain ⟨hxm', hx'⟩ := hx
      rcases hx' with rfl | hx'
      · omega
      · have := hmx x hx'
        have := hxM x hx'
        omega
    obtain ⟨hL0, hL1⟩ := ih _ hd' _ hL (fun x hx y hy => by
      have := memL x hx
      have := memL y hy
      omega)
    obtain ⟨hR0, hR1⟩ := ih _ hd' _ hR (fun x hx y hy => by
      have := memR x hx
      have := memR y hy
      omega)
    have href := dd_refine S (u a r) hmS hMS hzS hmz hzM
    have hMm : (0 : ℝ) < (M : ℝ) - m := by
      have : (m : ℝ) < M := by exact_mod_cast (show m < M by omega)
      linarith
    have hzm : (0 : ℝ) < (z : ℝ) - m := by
      have : (m : ℝ) < z := by exact_mod_cast hmz
      linarith
    have hMz : (0 : ℝ) < (M : ℝ) - z := by
      have : (z : ℝ) < M := by exact_mod_cast hzM
      linarith
    have key : 0 < ((M : ℝ) - m) * dd S (u a r) := by
      rw [href]
      by_cases hma : m < a
      · have hLne : (insert z S).erase M ≠ Icc a (a + r) := by
          intro h
          have : m ∈ (insert z S).erase M :=
            Finset.mem_erase.2 ⟨by omega, Finset.mem_insert_of_mem hmS⟩
          rw [h, mem_Icc] at this
          omega
        exact add_pos_of_pos_of_nonneg (mul_pos hzm (hL1 hLne)) (mul_nonneg hMz.le hR0)
      · have hRne : (insert z S).erase m ≠ Icc a (a + r) := by
          intro h
          have : M ∈ (insert z S).erase m :=
            Finset.mem_erase.2 ⟨by omega, Finset.mem_insert_of_mem hMS⟩
          rw [h, mem_Icc] at this
          omega
        exact add_pos_of_nonneg_of_pos (mul_nonneg hzm.le hL0) (mul_pos hMz (hR1 hRne))
    have hpos : 0 < dd S (u a r) := pos_of_mul_pos_right key hMm.le
    exact ⟨hpos.le, fun _ => hpos⟩

/-- **Lemma 1.** -/
theorem dd_spline_pos (a : ℤ) (r : ℕ) (S : Finset ℤ) (hS : S.card = r + 1) :
    0 ≤ dd S (u a r) ∧ (S ≠ Icc a (a + r) → 0 < dd S (u a r)) := by
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  apply dd_spline_pos_aux a r (S.max' hne - S.min' hne).toNat S hS
  intro x hx y hy
  have := Finset.min'_le S x hx
  have := Finset.le_max' S y hy
  omega

end KEss
```

### `KELeading.lean`

```lean
import KEExpand
import KESpline

/-!
# The matrix `A(t)` and the lowest-order term of each of its minors (Lemma 2)

Features are indexed by `Fin (r+2)` with weights `min d r`.
Row features: `x^d` (`d < r`), `u_a(x)` (`d = r`), `x^r` (`d = r+1`).
Column features: `y^d` (`d < r`), `y^r` (`d = r`), `u_b(y)` (`d = r+1`).
-/

open Matrix Finset Filter Topology

namespace KEss

/-- The integer node of a row or column index (0-based). -/
def node {n : ℕ} (i : Fin n) : ℤ := (i : ℕ)

/-- The weight `min d r` of feature `d`. -/
def wt (r : ℕ) (d : Fin (r + 2)) : ℕ := min (d : ℕ) r

/-- Row features. -/
noncomputable def rowF (n r : ℕ) (a : ℤ) : Matrix (Fin n) (Fin (r + 2)) ℝ :=
  Matrix.of fun i d => if (d : ℕ) < r then (node i : ℝ) ^ (d : ℕ)
    else if (d : ℕ) = r then u a r (node i) else (node i : ℝ) ^ r

/-- Column features. -/
noncomputable def colG (n r : ℕ) (b : ℤ) : Matrix (Fin (r + 2)) (Fin n) ℝ :=
  Matrix.of fun d j => if (d : ℕ) < r then (node j : ℝ) ^ (d : ℕ)
    else if (d : ℕ) = r then (node j : ℝ) ^ r else u b r (node j)

/-- The matrix (6) of the proof: `A(t)_{ij} = ∑_d t^{min d r} F_d(i) G_d(j)`. -/
noncomputable def mat (n r : ℕ) (a b : ℤ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  rowF n r a * (diagonal (fun d => t ^ wt r d) * colG n r b)

variable {n r : ℕ} {a b : ℤ}

/-- The coefficient of `t ^ W p` in the expansion of a minor. -/
noncomputable def coef {ℓ : ℕ} (eI eJ : Fin ℓ → Fin n) (p : Fin ℓ → Fin (r + 2)) : ℝ :=
  (∏ i, ((colG n r b).submatrix id eJ) (p i) i) *
    (((rowF n r a).submatrix eI id).submatrix id p).det

/-- The total weight of `p`. -/
def W {ℓ : ℕ} (p : Fin ℓ → Fin (r + 2)) : ℕ := ∑ i, wt r (p i)

theorem det_submatrix_mat {ℓ : ℕ} (eI eJ : Fin ℓ → Fin n) (t : ℝ) :
    ((mat n r a b t).submatrix eI eJ).det =
      ∑ p : Fin ℓ → Fin (r + 2), t ^ W p * coef (a := a) (b := b) eI eJ p := by
  rw [mat, Matrix.submatrix_mul _ _ eI id eJ Function.bijective_id,
    Matrix.submatrix_mul _ _ id id eJ Function.bijective_id, Matrix.submatrix_id_id,
    det_mul_diag_mul]
  rfl

theorem injective_of_coef_ne_zero {ℓ : ℕ} (eI eJ : Fin ℓ → Fin n) {p : Fin ℓ → Fin (r + 2)}
    (h : coef (a := a) (b := b) eI eJ p ≠ 0) : Function.Injective p := by
  by_contra hp
  apply h
  rw [coef, det_submatrix_eq_zero_of_not_injective _ hp, mul_zero]

theorem sum_val_le_W {ℓ : ℕ} (hℓ : ℓ ≤ r + 1) {p : Fin ℓ → Fin (r + 2)}
    (hp : Function.Injective p) : ∑ i : Fin ℓ, (i : ℕ) ≤ W p := by
  have h1 := sum_le_sum_of_injective (fun x => min x r) (fun _ _ h => min_le_min_right r h) ℓ
    (fun i => (p i : ℕ)) (Fin.val_injective.comp hp)
  have h2 : ∑ i : Fin ℓ, min (i : ℕ) r = ∑ i : Fin ℓ, (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => min_eq_left (by have := i.isLt; omega)
  rw [h2] at h1
  exact h1

theorem W_comp {ℓ : ℕ} (ι : Fin ℓ → Fin (r + 2)) (hι : ∀ i, wt r (ι i) = i)
    {q : Fin ℓ → Fin ℓ} (hq : Function.Injective q) : W (ι ∘ q) = ∑ i : Fin ℓ, (i : ℕ) := by
  unfold W
  simp only [Function.comp, hι]
  exact Equiv.sum_comp (Equiv.ofBijective q (Finite.injective_iff_bijective.1 hq))
    (fun i : Fin ℓ => (i : ℕ))

theorem wt_succAbove (v : Fin (r + 2)) (hv : r ≤ (v : ℕ)) (i : Fin (r + 1)) :
    wt r (v.succAbove i) = i := by
  unfold wt
  rcases lt_or_ge (Fin.castSucc i) v with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
    have := i.isLt
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
    have h' : (v : ℕ) ≤ i := h
    have := i.isLt
    omega

theorem val_succAbove_last (d : Fin (r + 1)) : ((Fin.last (r + 1)).succAbove d : ℕ) = d := by
  rw [Fin.succAbove_last, Fin.val_castSucc]

theorem val_succAbove_mid (d : Fin (r + 1)) :
    ((⟨r, by omega⟩ : Fin (r + 2)).succAbove d : ℕ) = if (d : ℕ) < r then (d : ℕ) else r + 1 := by
  rcases lt_or_ge (Fin.castSucc d) (⟨r, by omega⟩ : Fin (r + 2)) with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
    have h' : (d : ℕ) < r := h
    rw [ite_eq_left h']
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
    have h' : r ≤ (d : ℕ) := h
    have := d.isLt
    rw [ite_eq_right (by omega)]
    omega

theorem sum_coef_comp {ℓ : ℕ} (eI eJ : Fin ℓ → Fin n) (ι : Fin ℓ → Fin (r + 2)) :
    ∑ q : Fin ℓ → Fin ℓ, coef (a := a) (b := b) eI eJ (ι ∘ q) =
      (((rowF n r a).submatrix eI id).submatrix id ι).det *
        (((colG n r b).submatrix id eJ).submatrix ι id).det := by
  unfold coef
  exact sum_comp_eq_det_mul_det _ _ _

/-- Real nodes of an index map. -/
noncomputable def xs {ℓ : ℕ} (e : Fin ℓ → Fin n) : Fin ℓ → ℝ := fun i => (node (e i) : ℝ)

theorem xs_strictMono {ℓ : ℕ} {e : Fin ℓ → Fin n} (he : StrictMono e) : StrictMono (xs e) := by
  intro i j hij
  have : (e i : ℕ) < e j := he hij
  simp only [xs, node]
  exact_mod_cast this

theorem node_injective {ℓ : ℕ} {e : Fin ℓ → Fin n} (he : StrictMono e) :
    Function.Injective (fun i => node (e i)) := by
  intro i j hij
  apply he.injective
  apply Fin.val_injective
  simpa [node] using hij

/-- **Lemma 2, orders `ℓ ≤ r`**: the lowest-order coefficient is `V(I) V(J)`. -/
theorem leading_low {ℓ : ℕ} (hℓ : ℓ ≤ r) (eI eJ : Fin ℓ → Fin n) :
    ∑ p ∈ univ.filter (fun p : Fin ℓ → Fin (r + 2) => W p ≤ ∑ i : Fin ℓ, (i : ℕ)),
        coef (a := a) (b := b) eI eJ p =
      (vandermonde (xs eI)).det * (vandermonde (xs eJ)).det := by
  have hcast : ∀ i : Fin ℓ, wt r (Fin.castLE (by omega : ℓ ≤ r + 2) i) = i := by
    intro i
    simp only [wt, Fin.val_castLE]
    have := i.isLt
    omega
  rw [sum_filter_eq_sum_comp _ W _ (Fin.castLE (by omega : ℓ ≤ r + 2)) (Fin.castLE_injective _)]
  · rw [sum_coef_comp]
    have h1 : ((rowF n r a).submatrix eI id).submatrix id (Fin.castLE (by omega : ℓ ≤ r + 2)) =
        vandermonde (xs eI) := by
      ext i d
      have hd : (d : ℕ) < r := by have := d.isLt; omega
      simp [rowF, xs, vandermonde_apply, hd]
    have h2 : ((colG n r b).submatrix id eJ).submatrix (Fin.castLE (by omega : ℓ ≤ r + 2)) id =
        (vandermonde (xs eJ)).transpose := by
      ext d j
      have hd : (d : ℕ) < r := by have := d.isLt; omega
      simp [colG, xs, vandermonde_apply, hd]
    rw [h1, h2, det_transpose]
  · intro p hc
    have hp := injective_of_coef_ne_zero eI eJ hc
    constructor
    · intro hW
      have hlt := lt_of_sum_min_le r hℓ (fun i => (p i : ℕ)) (Fin.val_injective.comp hp) (by
        have h2 : ∑ i : Fin ℓ, min (i : ℕ) r = ∑ i : Fin ℓ, (i : ℕ) :=
          Finset.sum_congr rfl fun i _ => min_eq_left (by have := i.isLt; omega)
        rw [h2]
        exact hW)
      exact ⟨fun i => ⟨p i, hlt i⟩, funext fun i => Fin.ext rfl⟩
    · rintro ⟨q, rfl⟩
      exact (W_comp _ hcast (Function.Injective.of_comp hp)).le

/-- **Lemma 2, order `k = r+1`**: the lowest-order coefficient is
`V(I) V(J) (D_I(u_a) + D_J(u_b))`. -/
theorem leading_top (eI eJ : Fin (r + 1) → Fin n) (hI : StrictMono eI) (hJ : StrictMono eJ) :
    ∑ p ∈ univ.filter (fun p : Fin (r + 1) → Fin (r + 2) => W p ≤ ∑ i : Fin (r + 1), (i : ℕ)),
        coef (a := a) (b := b) eI eJ p =
      (vandermonde (xs eI)).det * (vandermonde (xs eJ)).det *
        (dd (univ.image fun i => node (eI i)) (u a r) +
          dd (univ.image fun j => node (eJ j)) (u b r)) := by
  set ι₁ : Fin (r + 1) → Fin (r + 2) := (Fin.last (r + 1)).succAbove with hι₁
  set ι₂ : Fin (r + 1) → Fin (r + 2) := (⟨r, by omega⟩ : Fin (r + 2)).succAbove with hι₂
  have hw₁ : ∀ i, wt r (ι₁ i) = i := wt_succAbove _ (by simp)
  have hw₂ : ∀ i, wt r (ι₂ i) = i := wt_succAbove _ (by simp)
  -- the total weight of all features
  have htot : ∑ d : Fin (r + 2), wt r d = ∑ i : Fin (r + 1), (i : ℕ) + r := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        simp only [wt, Fin.val_castSucc]
        have := i.isLt
        omega
    · simp [wt]
  have hWimg : ∀ p : Fin (r + 1) → Fin (r + 2), Function.Injective p → ∀ v,
      univ.image p = univ.erase v → wt r v + W p = ∑ i : Fin (r + 1), (i : ℕ) + r := by
    intro p hp v hv
    rw [← htot, ← Finset.add_sum_erase univ (wt r) (Finset.mem_univ v), ← hv,
      Finset.sum_image (fun x _ y _ h => hp h)]
    rfl
  rw [sum_filter_eq_sum_comp_two _ W _ ι₁ ι₂ (Fin.succAbove_right_injective)
    (Fin.succAbove_right_injective)]
  · rw [sum_coef_comp, sum_coef_comp]
    have h11 : ((rowF n r a).submatrix eI id).submatrix id ι₁ =
        genVand (fun i => (node (eI i) : ℝ)) (fun i => u a r (node (eI i))) := by
      ext i d
      simp only [submatrix_apply, id, rowF, genVand, Matrix.of_apply, hι₁, val_succAbove_last]
      by_cases hd : (d : ℕ) < r
      · rw [ite_eq_left hd, ite_eq_left hd]
      · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_left (by have := d.isLt; omega)]
    have h12 : ((colG n r b).submatrix id eJ).submatrix ι₁ id =
        (vandermonde (xs eJ)).transpose := by
      ext d j
      simp only [submatrix_apply, id, colG, Matrix.of_apply, hι₁, val_succAbove_last,
        transpose_apply, vandermonde_apply, xs]
      by_cases hd : (d : ℕ) < r
      · rw [ite_eq_left hd]
      · have : (d : ℕ) = r := by have := d.isLt; omega
        rw [ite_eq_right hd, ite_eq_left this, this]
    have h21 : ((rowF n r a).submatrix eI id).submatrix id ι₂ = vandermonde (xs eI) := by
      ext i d
      simp only [submatrix_apply, id, rowF, Matrix.of_apply, hι₂, val_succAbove_mid,
        vandermonde_apply, xs]
      by_cases hd : (d : ℕ) < r
      · rw [ite_eq_left hd, ite_eq_left hd]
      · have : (d : ℕ) = r := by have := d.isLt; omega
        rw [ite_eq_right hd, ite_eq_right (by omega), ite_eq_right (by omega), this]
    have h22 : ((colG n r b).submatrix id eJ).submatrix ι₂ id =
        (genVand (fun j => (node (eJ j) : ℝ)) (fun j => u b r (node (eJ j)))).transpose := by
      ext d j
      simp only [submatrix_apply, id, colG, genVand, Matrix.of_apply, hι₂, val_succAbove_mid,
        transpose_apply]
      by_cases hd : (d : ℕ) < r
      · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hd]
      · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [h11, h12, h21, h22, det_transpose, det_transpose,
      det_genVand (fun i => node (eI i)) (node_injective hI) (u a r),
      det_genVand (fun j => node (eJ j)) (node_injective hJ) (u b r)]
    change (vandermonde (xs eI)).det * _ * (vandermonde (xs eJ)).det +
      (vandermonde (xs eI)).det * ((vandermonde (xs eJ)).det * _) = _
    ring
  · intro p hc
    have hp := injective_of_coef_ne_zero eI eJ hc
    obtain ⟨v, hv⟩ := exists_image_eq_erase p hp
    have htv := hWimg p hp v hv
    constructor
    · intro hW
      have hrv : r ≤ (v : ℕ) := by
        have : r ≤ wt r v := by omega
        simp only [wt] at this
        omega
      have hpv : ∀ i, p i ≠ v := by
        intro i hi
        have : p i ∈ univ.image p := Finset.mem_image_of_mem p (Finset.mem_univ i)
        rw [hv, hi] at this
        exact (Finset.notMem_erase v univ) this
      have hq : ∀ i, ∃ z, v.succAbove z = p i := fun i => Fin.exists_succAbove_eq (hpv i)
      choose q hq using hq
      have hpq : p = v.succAbove ∘ q := funext fun i => (hq i).symm
      by_cases hvl : (v : ℕ) = r + 1
      · left
        have : v = Fin.last (r + 1) := Fin.ext (by simp [hvl])
        exact ⟨q, by rw [hpq, this]⟩
      · right
        have : v = ⟨r, by omega⟩ := Fin.ext (by simp only; have := v.isLt; omega)
        exact ⟨q, by rw [hpq, this]⟩
    · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact (W_comp _ hw₁ (Function.Injective.of_comp hp)).le
      · exact (W_comp _ hw₂ (Function.Injective.of_comp hp)).le
  · rintro p hc ⟨q₁, rfl⟩ ⟨q₂, hq₂⟩
    have hp := injective_of_coef_ne_zero eI eJ hc
    obtain ⟨v, hv⟩ := exists_image_eq_erase _ hp
    have hnot : ∀ (w : Fin (r + 2)) (ι : Fin (r + 1) → Fin (r + 2)) (q : Fin (r + 1) → Fin (r + 1)),
        ι ∘ q = ι₁ ∘ q₁ → (∀ z, ι z ≠ w) → w = v := by
      intro w ι q hιq hw
      by_contra hwv
      have : w ∈ univ.erase v := Finset.mem_erase.2 ⟨hwv, Finset.mem_univ w⟩
      rw [← hv] at this
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 this
      have := congrFun hιq i
      simp only [Function.comp] at this
      exact hw (q i) (this.trans hi)
    have e1 := hnot (Fin.last (r + 1)) ι₁ q₁ rfl (fun z => Fin.succAbove_ne _ z)
    have e2 := hnot ⟨r, by omega⟩ ι₂ q₂ hq₂.symm (fun z => Fin.succAbove_ne _ z)
    have h3 : ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = r := congrArg Fin.val (e1.trans e2.symm)
    rw [Fin.val_last] at h3
    omega

end KEss
```

### `KEMain.lean`

```lean
import KEStatement
import KELeading

/-!
# Solid `k`-minors are `k`-essential (Brosowsky–Chepuri–Mason, Conjecture 4.6)

The witness is `mat n r a b t` (the matrix (6) of the proof, `k = r + 1`) for one
small `t > 0`, chosen by a finite intersection of neighbourhood filters.
-/

open Matrix Finset Filter Topology

namespace KEss

variable {n r : ℕ}

/-- The distinguished solid minor of `A(t)` vanishes for every `t` (its block has rank `≤ r`). -/
theorem target_det_zero {a b : ℤ} {ℓ : ℕ} (hℓ : ℓ = r + 1) (eI eJ : Fin ℓ → Fin n)
    (hI : ∀ i, a ≤ node (eI i) ∧ node (eI i) ≤ a + r)
    (hJ : ∀ j, b ≤ node (eJ j) ∧ node (eJ j) ≤ b + r) (t : ℝ) :
    ((mat n r a b t).submatrix eI eJ).det = 0 := by
  subst hℓ
  rw [det_submatrix_mat]
  refine Finset.sum_eq_zero fun p _ => ?_
  suffices h : coef (a := a) (b := b) eI eJ p = 0 by rw [h, mul_zero]
  by_cases hp : Function.Injective p
  · obtain ⟨v, hv⟩ := exists_image_eq_erase p hp
    by_cases hvr : (v : ℕ) = r
    · have hmem : Fin.last (r + 1) ∈ univ.image p := by
        rw [hv]
        refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩
        have h' := congrArg Fin.val h
        rw [Fin.val_last] at h'
        omega
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
      unfold coef
      rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_mul]
      simp only [submatrix_apply, id, colG, Matrix.of_apply, hi, Fin.val_last]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), u,
        spline_eq_zero (hJ i).1 (hJ i).2, Int.cast_zero]
    · have hmem : (⟨r, by omega⟩ : Fin (r + 2)) ∈ univ.image p := by
        rw [hv]
        refine Finset.mem_erase.2 ⟨fun h => hvr ?_, Finset.mem_univ _⟩
        have h' := congrArg Fin.val h
        simp only at h'
        omega
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hmem
      unfold coef
      rw [det_eq_zero_of_column_eq_zero i, mul_zero]
      intro k
      simp only [submatrix_apply, id, rowF, Matrix.of_apply, hi]
      rw [ite_eq_right (lt_irrefl r), ite_eq_left trivial, u,
        spline_eq_zero (hI k).1 (hI k).2, Int.cast_zero]
  · unfold coef
    rw [det_submatrix_eq_zero_of_not_injective _ hp, mul_zero]

/-- Every non-target minor of order `≤ r + 1` of `A(t)` is positive for all small `t > 0`. -/
theorem core_eventually_pos {a b : ℤ} {ℓ : ℕ} (hℓ : ℓ ≤ r + 1) (eI eJ : Fin ℓ → Fin n)
    (hI : StrictMono eI) (hJ : StrictMono eJ)
    (hne : ∀ _ : ℓ = r + 1, ¬ (univ.image (fun i => node (eI i)) = Icc a (a + r) ∧
      univ.image (fun j => node (eJ j)) = Icc b (b + r))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ((mat n r a b t).submatrix eI eJ).det := by
  have hexp : ∀ t : ℝ, ((mat n r a b t).submatrix eI eJ).det =
      ∑ p : Fin ℓ → Fin (r + 2), t ^ W p * coef (a := a) (b := b) eI eJ p :=
    fun t => det_submatrix_mat eI eJ t
  simp only [hexp]
  apply eventually_pos_of_leading W (coef (a := a) (b := b) eI eJ) (∑ i : Fin ℓ, (i : ℕ))
  · intro p hc
    exact sum_val_le_W hℓ (injective_of_coef_ne_zero eI eJ hc)
  · rcases Nat.lt_or_ge ℓ (r + 1) with hlt | hge
    · rw [leading_low (by omega)]
      exact mul_pos (det_vandermonde_pos _ (xs_strictMono hI))
        (det_vandermonde_pos _ (xs_strictMono hJ))
    · have hℓ' : ℓ = r + 1 := by omega
      have hne' := hne hℓ'
      subst hℓ'
      rw [leading_top eI eJ hI hJ]
      have hcI : (univ.image fun i => node (eI i)).card = r + 1 := by
        rw [Finset.card_image_of_injective _ (node_injective hI), Finset.card_univ,
          Fintype.card_fin]
      have hcJ : (univ.image fun j => node (eJ j)).card = r + 1 := by
        rw [Finset.card_image_of_injective _ (node_injective hJ), Finset.card_univ,
          Fintype.card_fin]
      obtain ⟨hI0, hI1⟩ := dd_spline_pos a r _ hcI
      obtain ⟨hJ0, hJ1⟩ := dd_spline_pos b r _ hcJ
      have hsum : 0 < dd (univ.image fun i => node (eI i)) (u a r) +
          dd (univ.image fun j => node (eJ j)) (u b r) := by
        by_cases h1 : (univ.image fun i => node (eI i)) = Icc a (a + r)
        · exact add_pos_of_nonneg_of_pos hI0 (hJ1 fun h2 => hne' ⟨h1, h2⟩)
        · exact add_pos_of_pos_of_nonneg (hI1 h1) hJ0
      exact mul_pos (mul_pos (det_vandermonde_pos _ (xs_strictMono hI))
        (det_vandermonde_pos _ (xs_strictMono hJ))) hsum

/-- Bridge: a row set whose integer nodes form `[c, c+r]` is the interval of the statement. -/
theorem eq_interval_of_image (I : Finset (Fin n)) {ℓ : ℕ} (hk : I.card = ℓ) (c : ℕ)
    (h : univ.image (fun i => node (I.orderEmbOfFin hk i)) = Icc (c : ℤ) (c + r)) :
    I = interval c (r + 1) := by
  ext x
  have key : x ∈ I ↔ node x ∈ univ.image (fun i => node (I.orderEmbOfFin hk i)) := by
    constructor
    · intro hx
      have : x ∈ Set.range (I.orderEmbOfFin hk) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨i, hi⟩ := this
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, by rw [hi]⟩
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hx
      have : I.orderEmbOfFin hk i = x := by
        apply Fin.val_injective
        simpa [node] using hi
      rw [← this]
      exact Finset.orderEmbOfFin_mem I hk i
  rw [key, h, Finset.mem_Icc]
  simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and, node]
  omega

theorem node_bounds_of_mem_interval {c : ℕ} {x : Fin n} (hx : x ∈ interval c (r + 1)) :
    (c : ℤ) ≤ node x ∧ node x ≤ (c : ℤ) + r := by
  simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [node]
  omega

theorem minor_eventually_pos (a b : ℕ) (I J : Finset (Fin n)) (h : I.card = J.card)
    (hk : I.card ≤ r + 1) (hne : (I, J) ≠ (interval a (r + 1), interval b (r + 1))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < minor (mat n r a b t) I J h := by
  unfold minor
  apply core_eventually_pos hk _ _ (I.orderEmbOfFin rfl).strictMono
    (J.orderEmbOfFin h.symm).strictMono
  rintro _ ⟨h1, h2⟩
  apply hne
  rw [eq_interval_of_image I rfl a h1, eq_interval_of_image J h.symm b h2]

/-- **Conjecture 4.6 of Brosowsky–Chepuri–Mason (arXiv:1712.05037): solid `k`-minors are
`k`-essential.**  The endpoint required by the review, verbatim. -/
theorem solid_minors_k_essential (n k a b : ℕ) (hk : 1 ≤ k) (ha : a + k ≤ n) (hb : b + k ≤ n) :
    ∃ h, KEssential (n := n) k (interval a k) (interval b k) h := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  have hIc := card_interval (n := n) ha
  have hJc := card_interval (n := n) hb
  refine ⟨hIc.trans hJc.symm, hIc.le, ?_⟩
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ pq : Finset (Fin n) × Finset (Fin n),
      ∀ h' : pq.1.card = pq.2.card, pq.1.card ≤ r + 1 →
        pq ≠ (interval a (r + 1), interval b (r + 1)) →
          0 < minor (mat n r a b t) pq.1 pq.2 h' := by
    rw [Filter.eventually_all]
    rintro ⟨I', J'⟩
    by_cases hc : ∃ h' : I'.card = J'.card, I'.card ≤ r + 1 ∧
        (I', J') ≠ (interval a (r + 1), interval b (r + 1))
    · obtain ⟨h', h1, h2⟩ := hc
      filter_upwards [minor_eventually_pos a b I' J' h' h1 h2] with t ht h'' _ _
      exact ht
    · exact Filter.Eventually.of_forall fun t h' h1 h2 => absurd ⟨h', h1, h2⟩ hc
  obtain ⟨t, ht⟩ := hev.exists
  refine ⟨mat n r a b t, ?_, fun I' J' h' h1 h2 => ht (I', J') h' h1 h2⟩
  unfold minor
  rw [target_det_zero hIc _ _
    (fun i => node_bounds_of_mem_interval (Finset.orderEmbOfFin_mem _ _ i))
    (fun j => node_bounds_of_mem_interval (Finset.orderEmbOfFin_mem _ _ j)) t]

end KEss

#print axioms KEss.solid_minors_k_essential
#check @KEss.solid_minors_k_essential
#print KEss.KEssential
#print KEss.minor
#print KEss.interval
#print axioms KEss.minor_eventually_pos
#print axioms KEss.target_det_zero
#print axioms KEss.dd_spline_pos
#print axioms KEss.leading_top
#print axioms KEss.det_genVand
```

