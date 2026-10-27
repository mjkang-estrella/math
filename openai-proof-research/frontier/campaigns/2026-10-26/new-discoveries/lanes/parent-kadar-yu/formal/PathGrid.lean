import RootCounts

namespace KadarYu

open Polynomial

/-- A single sufficiently fine finite grid contains arbitrarily many consecutive
points in any open subinterval of (0,1). -/
theorem exists_many_grid_points (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hab : a < b) (R : ℕ) :
    ∃ N : ℕ, ∃ k : Fin R ↪ Fin N,
      ∀ i, a < ((k i).val + 1 : ℝ) / (N + 1) ∧
        ((k i).val + 1 : ℝ) / (N + 1) < b := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + 1 : ℝ) / (b - a))
  have hd : 0 < b - a := sub_pos.mpr hab
  have hbig : (R + 1 : ℝ) < (b - a) * (N + 1) := by
    have h := (div_lt_iff₀ hd).mp hN
    nlinarith
  have hM : (0 : ℝ) < N + 1 := by positivity
  let K := ⌊a * (N + 1)⌋₊
  have hK : (K : ℝ) ≤ a * (N + 1) := Nat.floor_le (by positivity)
  have hK' : a * (N + 1) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hi : ∀ i : Fin R, (K + i.val : ℕ) < N := by
    intro i
    have hiR : (i.val : ℝ) < R := by exact_mod_cast i.isLt
    have hupper : (K : ℝ) + i.val + 1 < b * (N + 1) := by nlinarith
    have hlt : (K + i.val + 1 : ℝ) < N + 1 := by
      nlinarith
    have hh : K + i.val + 1 < N + 1 := by exact_mod_cast hlt
    omega
  let k : Fin R ↪ Fin N :=
    ⟨fun i => ⟨K + i.val, hi i⟩, fun i j h => by
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp at hv
      omega⟩
  refine ⟨N, k, ?_⟩
  intro i
  change a < ((K + i.val : ℕ) + 1 : ℝ) / (N + 1) ∧
    ((K + i.val : ℕ) + 1 : ℝ) / (N + 1) < b
  have hiR : (i.val : ℝ) < R := by exact_mod_cast i.isLt
  constructor
  · apply (lt_div_iff₀ hM).mpr
    push_cast
    have hip : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    nlinarith
  · apply (div_lt_iff₀ hM).mpr
    push_cast
    nlinarith

noncomputable def pathGridRoot (N : ℕ) (k : Fin N) : ℝ :=
  2 * Real.cos (((k.val : ℝ) + 1) * Real.pi / (N + 1))

theorem pathGrid_angle (N : ℕ) (k : Fin N) :
    0 < ((k.val : ℝ) + 1) * Real.pi / (N + 1) ∧
      ((k.val : ℝ) + 1) * Real.pi / (N + 1) < Real.pi := by
  have hM : (0 : ℝ) < N + 1 := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hM).mpr
    have hk : (k.val : ℝ) < N := by exact_mod_cast k.isLt
    nlinarith [Real.pi_pos]

theorem pathGridRoot_isRoot (N : ℕ) (k : Fin N) :
    (jacobiPolynomial (fun _ => 0) (fun _ => 1) N).eval (pathGridRoot N k) = 0 := by
  rw [unitPath_polynomial_eq_S]
  let t := ((k.val : ℝ) + 1) * Real.pi / (N + 1)
  have hs : Real.sin t ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (pathGrid_angle N k).1 (pathGrid_angle N k).2)
  have h := Polynomial.Chebyshev.S_two_mul_real_cos t (N : ℤ)
  have ht : ((N : ℝ) + 1) * t = (k.val + 1 : ℕ) * Real.pi := by
    dsimp [t]
    push_cast
    field_simp
  push_cast at h
  rw [ht, Real.sin_nat_mul_pi] at h
  exact (mul_eq_zero.mp h).resolve_right hs

theorem pathGridRoot_injective (N : ℕ) : Function.Injective (pathGridRoot N) := by
  intro i j hij
  have hc : Real.cos (((i.val : ℝ) + 1) * Real.pi / (N + 1)) =
      Real.cos (((j.val : ℝ) + 1) * Real.pi / (N + 1)) := by
    unfold pathGridRoot at hij
    linarith
  have he := Real.injOn_cos ⟨(pathGrid_angle N i).1.le, (pathGrid_angle N i).2.le⟩
    ⟨(pathGrid_angle N j).1.le, (pathGrid_angle N j).2.le⟩ hc
  apply Fin.ext
  have hv : (i.val : ℝ) = j.val := by
    have hM : (N : ℝ) + 1 ≠ 0 := by positivity
    have hh := (div_left_inj' hM).mp he
    nlinarith [Real.pi_pos]
  exact_mod_cast hv

theorem exists_many_path_roots (a b : ℝ) (ha : -2 < a) (hb : b < 2)
    (hab : a < b) (R : ℕ) :
    ∃ N : ℕ, ∃ f : Fin R ↪ ℝ, ∀ i,
      (jacobiPolynomial (fun _ => 0) (fun _ => 1) N).eval (f i) = 0 ∧
        a < f i ∧ f i < b := by
  have hab' : a / 2 < b / 2 := by linarith
  have ha' : -1 < a / 2 := by linarith
  have hb' : b / 2 < 1 := by linarith
  have hanti : Real.arccos (b / 2) < Real.arccos (a / 2) :=
    Real.arccos_lt_arccos ha'.le hab' hb'.le
  obtain ⟨N, k, hk⟩ := exists_many_grid_points
    (Real.arccos (b / 2) / Real.pi) (Real.arccos (a / 2) / Real.pi)
    (div_pos (Real.arccos_pos.mpr hb') Real.pi_pos)
    ((div_lt_one Real.pi_pos).mpr (Real.arccos_lt_pi.mpr ha'))
    ((div_lt_div_iff_of_pos_right Real.pi_pos).mpr hanti) R
  let f : Fin R ↪ ℝ := ⟨fun i => pathGridRoot N (k i),
    (pathGridRoot_injective N).comp k.injective⟩
  refine ⟨N, f, ?_⟩
  intro i
  refine ⟨pathGridRoot_isRoot N (k i), ?_, ?_⟩
  · have ht : ((k i).val + 1 : ℝ) * Real.pi / (N + 1) < Real.arccos (a / 2) := by
      have h := (lt_div_iff₀ Real.pi_pos).mp (hk i).2
      simpa only [div_mul_eq_mul_div] using h
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (pathGrid_angle N (k i)).1.le
      (Real.arccos_le_pi _) ht
    rw [Real.cos_arccos ha'.le (by linarith)] at hcos
    change a < 2 * Real.cos _
    linarith
  · have ht : Real.arccos (b / 2) < ((k i).val + 1 : ℝ) * Real.pi / (N + 1) := by
      have h := (div_lt_iff₀ Real.pi_pos).mp (hk i).1
      simpa only [div_mul_eq_mul_div] using h
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
      (pathGrid_angle N (k i)).2.le ht
    rw [Real.cos_arccos (by linarith : -1 ≤ b / 2) hb'.le] at hcos
    change 2 * Real.cos _ < b
    linarith

end KadarYu
