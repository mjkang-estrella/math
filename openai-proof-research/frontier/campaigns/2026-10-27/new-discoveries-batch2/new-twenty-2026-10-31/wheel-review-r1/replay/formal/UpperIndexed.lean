import LowerWeighted
set_option autoImplicit false
open scoped BigOperators
namespace WheelFormal

/-- Push indexed weights onto literal independent sets; repeated sets add. -/
noncomputable def indexedColouring {V I : Type} [Fintype V] [DecidableEq V]
    [Fintype I] (G : SimpleGraph V)
    (sets : I → {s : Finset V // Independent G s}) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ v, 1 ≤ ∑ i, if v ∈ (sets i).val then w i else 0) :
    FractionalColouring G where
  weight s := ∑ i, if sets i = s then w i else 0
  nonnegative s := by
    apply Finset.sum_nonneg
    intro i _
    split
    · exact hw i
    · exact le_rfl
  coverage v := by
    classical
    have he : (∑ s : {s : Finset V // Independent G s},
        if v ∈ s.val then (∑ i, if sets i = s then w i else 0) else 0) =
        ∑ i, if v ∈ (sets i).val then w i else 0 := by
      calc
        _ = ∑ s : {s : Finset V // Independent G s}, ∑ i,
            if v ∈ s.val then (if sets i = s then w i else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hv : v ∈ s.val <;> simp [hv]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          have hswap : ∀ s : {s : Finset V // Independent G s},
              (if v ∈ s.val then (if sets i = s then w i else 0) else 0) =
              (if sets i = s then (if v ∈ (sets i).val then w i else 0) else 0) := by
            intro s
            by_cases hs : sets i = s
            · subst s; simp
            · simp [hs]
          simp_rw [hswap]
          simp
    change 1 ≤ ∑ s : {s : Finset V // Independent G s},
      if v ∈ s.val then (∑ i, if sets i = s then w i else 0) else 0
    rw [he]
    exact hc v

theorem indexedColouring_total {V I : Type} [Fintype V] [DecidableEq V]
    [Fintype I] (G : SimpleGraph V)
    (sets : I → {s : Finset V // Independent G s}) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ v, 1 ≤ ∑ i, if v ∈ (sets i).val then w i else 0) :
    (indexedColouring G sets w hw hc).total = ∑ i, w i := by
  classical
  unfold FractionalColouring.total indexedColouring
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The three coverage equations, including the unnormalised F2 count. -/
theorem upper_coverage_arithmetic (t : ℕ) :
    let m : ℝ := 2*(t:ℝ)+1
    let D : ℝ := 2*(t:ℝ)^2+(t:ℝ)+1
    1 / D + (t:ℝ)*m/D = 1 ∧
    (t:ℝ)/m + 2*(t:ℝ)^2/(m*D) + ((t:ℝ)^2+1)/D = 1 ∧
    1 + m/D + m^2/D = (6*(t:ℝ)^2+7*(t:ℝ)+3)/D := by
  dsimp
  have hm : (2*(t:ℝ)+1) ≠ 0 := by positivity
  have hd : (2*(t:ℝ)^2+(t:ℝ)+1) ≠ 0 := by positivity
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · field_simp; ring
end WheelFormal
