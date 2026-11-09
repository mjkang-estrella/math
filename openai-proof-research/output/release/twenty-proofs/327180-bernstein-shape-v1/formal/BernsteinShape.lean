import Mathlib

open Finset
open scoped ComplexConjugate

namespace BernsteinShape

noncomputable def basis (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

noncomputable def phi (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (basis n k x) ^ 2

lemma character_conj {N : ℕ} [NeZero N] (a : ZMod N) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma character_orthogonality {N : ℕ} [NeZero N] (k l : Fin N) :
    ∑ j : ZMod N, ZMod.stdAddChar (j * ((k : ℕ) : ZMod N)) *
      conj (ZMod.stdAddChar (j * ((l : ℕ) : ZMod N))) = if k = l then (N : ℂ) else 0 := by
  simp_rw [character_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  have h : ((k : ℕ) : ZMod N) - ((l : ℕ) : ZMod N) = 0 ↔ k = l := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    simp only [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt, Fin.val_inj]
  simp only [h, ZMod.card, Nat.cast_ite, Nat.cast_zero]

lemma finite_parseval {N : ℕ} [NeZero N] (a : Fin N → ℝ) :
    ∑ j : ZMod N, ‖∑ k : Fin N, (a k : ℂ) *
      ZMod.stdAddChar (j * ((k : ℕ) : ZMod N))‖ ^ 2 =
        (N : ℝ) * ∑ k : Fin N, (a k) ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Complex.conj_ofReal,
    sum_mul, mul_sum]
  calc
    _ = ∑ k : Fin N, ∑ l : Fin N, ∑ j : ZMod N,
          (a k : ℂ) * ZMod.stdAddChar (j * ((k : ℕ) : ZMod N)) *
          ((a l : ℂ) * conj (ZMod.stdAddChar (j * ((l : ℕ) : ZMod N)))) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      rw [sum_comm]
    _ = ∑ k : Fin N, ∑ l : Fin N,
          ((a k : ℂ) * (a l : ℂ)) * (if k = l then (N : ℂ) else 0) := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro l hl
      rw [← character_orthogonality k l, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
      apply sum_congr rfl
      intro k hk
      ring

lemma character_nat_mul {N : ℕ} [NeZero N] (j : ZMod N) (k : ℕ) :
    ZMod.stdAddChar (j * (k : ZMod N)) = ZMod.stdAddChar j ^ k := by
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

lemma binomial_fourier (n : ℕ) (x : ℝ) (j : ZMod (n + 1)) :
    ∑ k : Fin (n + 1), (basis n k x : ℂ) *
      ZMod.stdAddChar (j * ((k : ℕ) : ZMod (n + 1))) =
        ((x : ℂ) * ZMod.stdAddChar j + (1 - x)) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (basis n k x : ℂ) *
    ZMod.stdAddChar (j * (k : ZMod (n + 1)))) (n + 1), add_pow]
  apply sum_congr rfl
  intro k hk
  rw [character_nat_mul]
  simp only [basis, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one, mul_pow]
  ring

theorem finite_average_identity (n : ℕ) (x : ℝ) :
    phi n x = (n + 1 : ℝ)⁻¹ * ∑ j : ZMod (n + 1),
      ‖(x : ℂ) * ZMod.stdAddChar j + (1 - x)‖ ^ (2 * n) := by
  have h := finite_parseval (fun k : Fin (n + 1) => basis n k x)
  simp_rw [binomial_fourier, norm_pow, ← pow_mul, mul_comm n 2] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => basis n k x ^ 2) (n + 1)] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  change _ = (n + 1 : ℝ) * phi n x at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

lemma convex_norm_affine_power (z : ℂ) (m : ℕ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => ‖(x : ℂ) * z + (1 - x)‖ ^ m) := by
  have h := (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℂ → ℝ)).comp_affineMap
    (AffineMap.lineMap (1 : ℂ) z)
  have hn : ConvexOn ℝ Set.univ (fun x : ℝ => ‖(x : ℂ) * z + (1 - x)‖) := by
    change ConvexOn ℝ Set.univ (fun x : ℝ => ‖x • (z - 1) + 1‖) at h
    convert h using 1
    funext x
    simp only [Complex.real_smul]
    congr 1
    ring
  exact hn.pow (fun _ _ => norm_nonneg _) m

theorem convexOn_univ (n : ℕ) : ConvexOn ℝ Set.univ (phi n) := by
  have hs : ConvexOn ℝ Set.univ (fun x : ℝ => ∑ j : ZMod (n + 1),
      ‖(x : ℂ) * ZMod.stdAddChar j + (1 - x)‖ ^ (2 * n)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, mul_sum, ← sum_add_distrib]
    exact sum_le_sum (fun j _ =>
      (convex_norm_affine_power (ZMod.stdAddChar j) (2 * n)).2 hx hy ha hb hab)
  have h := hs.smul (c := (n + 1 : ℝ)⁻¹) (by positivity)
  simpa only [smul_eq_mul, ← finite_average_identity] using h

theorem convexOn_Icc (n : ℕ) : ConvexOn ℝ (Set.Icc 0 1) (phi n) :=
  (convexOn_univ n).subset (Set.subset_univ _) (convex_Icc _ _)

theorem phi_eq_expanded (n : ℕ) (x : ℝ) :
    phi n x = ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) ^ 2 * x ^ (2 * k) * (1 - x) ^ (2 * (n - k)) := by
  unfold phi basis
  apply sum_congr rfl
  intro k hk
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  simp only [mul_comm 2]

theorem bernstein_square_sum_convex (n : ℕ) :
    ConvexOn ℝ (Set.Icc 0 1) (fun x : ℝ => ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) ^ 2 * x ^ (2 * k) * (1 - x) ^ (2 * (n - k))) := by
  simpa only [← phi_eq_expanded] using convexOn_Icc n

lemma symmetry (n : ℕ) (x : ℝ) : phi n (1 - x) = phi n x := by
  unfold phi
  rw [← sum_range_reflect (fun k => (basis n k x) ^ 2) (n + 1)]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  simp only [Nat.add_sub_cancel, basis, Nat.choose_symm hk',
    Nat.sub_sub_self hk', sub_sub_cancel]
  ring

theorem midpoint_minimum (n : ℕ) (x : ℝ) : phi n (1 / 2) ≤ phi n x := by
  have h := (convexOn_univ n).2 (Set.mem_univ x) (Set.mem_univ (1 - x))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (1 - x) = 1 / 2 := by
    ring
  simp only [symmetry, smul_eq_mul] at h
  rw [he] at h
  linarith

theorem antitoneOn_left (n : ℕ) : AntitoneOn (phi n) (Set.Iic (1 / 2)) := by
  intro x hx y hy hxy
  change x ≤ (1 / 2 : ℝ) at hx
  change y ≤ (1 / 2 : ℝ) at hy
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  rcases hy.eq_or_lt with rfl | hy
  · exact midpoint_minimum n x
  apply (convexOn_univ n).le_left_of_right_le (Set.mem_univ x) (Set.mem_univ (1 / 2))
    ?_ (midpoint_minimum n y)
  rw [openSegment_eq_Ioo (show x < (1 / 2 : ℝ) by linarith)]
  exact ⟨hxy, hy⟩

theorem monotoneOn_right (n : ℕ) : MonotoneOn (phi n) (Set.Ici (1 / 2)) := by
  intro x hx y hy hxy
  change (1 / 2 : ℝ) ≤ x at hx
  change (1 / 2 : ℝ) ≤ y at hy
  have h := antitoneOn_left n
    (show 1 - y ∈ Set.Iic (1 / 2 : ℝ) by change 1 - y ≤ (1 / 2 : ℝ); linarith)
    (show 1 - x ∈ Set.Iic (1 / 2 : ℝ) by change 1 - x ≤ (1 / 2 : ℝ); linarith)
    (show 1 - y ≤ 1 - x by linarith)
  simpa only [symmetry] using h

lemma basis_midpoint (n k : ℕ) (hk : k ≤ n) :
    basis n k (1 / 2) = (n.choose k : ℝ) * (1 / 2) ^ n := by
  unfold basis
  norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk]

theorem midpoint_value (n : ℕ) : phi n (1 / 2) = ((2 * n).choose n : ℝ) / 4 ^ n := by
  have h : phi n (1 / 2) = (∑ k ∈ range (n + 1), (n.choose k : ℝ) ^ 2) *
      ((1 / 2 : ℝ) ^ n) ^ 2 := by
    unfold phi
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [basis_midpoint n k (by simpa using hk), mul_pow]
  rw [h]
  have hs : (∑ k ∈ range (n + 1), (n.choose k : ℝ) ^ 2) = ((2 * n).choose n : ℝ) := by
    exact_mod_cast Nat.sum_range_choose_sq n
  rw [hs, ← pow_mul, mul_comm n 2, pow_mul]
  norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num, one_div_pow]
  ring

theorem sharp_lower_bound (n : ℕ) (x : ℝ) :
    ((2 * n).choose n : ℝ) / 4 ^ n ≤ phi n x := by
  rw [← midpoint_value]
  exact midpoint_minimum n x

end BernsteinShape
