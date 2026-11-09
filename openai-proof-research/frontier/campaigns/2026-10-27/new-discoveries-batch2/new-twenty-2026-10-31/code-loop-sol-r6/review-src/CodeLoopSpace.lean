import CodeLoopCodes
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi

/-! Actual binary subspaces and coordinate transport for the two representations. -/

theorem dot3_add_right (x y z : W3) : dot3 (x + y) z = dot3 x z + dot3 y z := by
  simp only [dot3, Pi.add_apply, add_mul, Finset.sum_add_distrib]

noncomputable def dEval (i : Fin 2) : (W4 × W3) →ₗ[ZMod 2] (Dcoord i → ZMod 2) where
  toFun p := dval i p.1 p.2
  map_add' p q := by
    funext c
    cases c with
    | inl c => exact dot4_add_right _ _ _
    | inr b => exact dot3_add_right _ _ _
  map_smul' a p := by
    rcases zmod2_cases a with h | h
    · subst a; funext c; cases c <;> simp [dval, cval, sval, dot4_zero_left, dot3_zero_left]
    · subst a; simp

noncomputable def D (i : Fin 2) : Submodule (ZMod 2) (Dcoord i → ZMod 2) := (dEval i).range

theorem dEval_injective (i : Fin 2) : Function.Injective (dEval i) := by
  intro p q h
  exact Prod.ext (dval_inj i h).1 (dval_inj i h).2

noncomputable def parametersEquiv (i : Fin 2) : (W4 × W3) ≃ₗ[ZMod 2] D i :=
  LinearEquiv.ofInjective (dEval i) (dEval_injective i)

noncomputable def coordEquiv50 (i : Fin 2) : Dcoord i ≃ Fin 50 :=
  Fintype.equivFinOfCardEq (dcoord_card i)

noncomputable def transport50 (i : Fin 2) :
    (Dcoord i → ZMod 2) ≃ₗ[ZMod 2] (Fin 50 → ZMod 2) where
  toFun v k := v ((coordEquiv50 i).symm k)
  invFun v c := v (coordEquiv50 i c)
  left_inv v := by funext c; simp
  right_inv v := by funext c; simp
  map_add' v w := rfl
  map_smul' a v := rfl

noncomputable def D50 (i : Fin 2) : Submodule (ZMod 2) (Fin 50 → ZMod 2) :=
  (D i).map (transport50 i).toLinearMap

theorem D_full_support (i : Fin 2) (c : Dcoord i) : ∃ v ∈ D i, v c = 1 := by
  cases c with
  | inl c =>
    obtain ⟨j, hj⟩ := exists_one_of_ne_zero4 c.1.property
    refine ⟨dval i (e4v j) 0, ⟨(e4v j, 0), rfl⟩, ?_⟩
    change dot4 (e4v j) c.1 = 1
    rw [dot4_comm, dot4_e4v_left]; exact hj
  | inr b =>
    have hex : ∃ j, b.val j ≠ 0 := by
      by_contra h
      push Not at h
      exact b.property (funext h)
    obtain ⟨j, hj⟩ := hex
    refine ⟨dval i 0 (e3v j), ⟨(0, e3v j), rfl⟩, ?_⟩
    change dot3 (e3v j) b.val = 1
    have he : dot3 (e3v j) b.val = b.val j := by
      unfold dot3 e3v
      simp
    rw [he]; exact (zmod2_cases _).resolve_left hj

/-- Source coordinate equivalence quantifies over every word of the actual subspace. -/
def SameColumn (i : Fin 2) (c d : Dcoord i) : Prop := ∀ v ∈ D i, v c = v d

def columnLabel (i : Fin 2) : Dcoord i → ({a : W4 // a ≠ 0} ⊕ B3)
  | Sum.inl c => Sum.inl c.1
  | Sum.inr b => Sum.inr b

theorem sameColumn_iff (i : Fin 2) (c d : Dcoord i) :
    SameColumn i c d ↔ columnLabel i c = columnLabel i d := by
  constructor
  · intro h
    cases c with
    | inl c =>
      cases d with
      | inl d =>
        apply congrArg Sum.inl
        apply Subtype.ext
        funext j
        have hh := h (dval i (e4v j) 0) ⟨(e4v j, 0), rfl⟩
        change dot4 (e4v j) c.1 = dot4 (e4v j) d.1 at hh
        simpa only [dot4_comm (e4v j), dot4_e4v_left] using hh
      | inr b =>
        obtain ⟨j, hj⟩ := exists_one_of_ne_zero4 c.1.property
        have hh := h (dval i (e4v j) 0) ⟨(e4v j, 0), rfl⟩
        change dot4 (e4v j) c.1 = dot3 0 b at hh
        rw [dot4_comm, dot4_e4v_left, hj, dot3_zero_left] at hh
        exact (zmod2_one_ne_zero hh).elim
    | inr b =>
      cases d with
      | inl d =>
        obtain ⟨j, hj⟩ := exists_one_of_ne_zero4 d.1.property
        have hh := h (dval i (e4v j) 0) ⟨(e4v j, 0), rfl⟩
        change dot3 0 b = dot4 (e4v j) d.1 at hh
        rw [dot4_comm, dot4_e4v_left, hj, dot3_zero_left] at hh
        exact (zmod2_one_ne_zero hh.symm).elim
      | inr d =>
        apply congrArg Sum.inr
        apply Subtype.ext
        funext j
        have hh := h (dval i 0 (e3v j)) ⟨(0, e3v j), rfl⟩
        change dot3 (e3v j) b = dot3 (e3v j) d at hh
        simpa [dot3, e3v] using hh
  · intro h v hv
    obtain ⟨p, rfl⟩ := hv
    cases c <;> cases d <;> simp only [columnLabel, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at h
    · change dot4 p.1 _ = dot4 p.1 _
      rw [h]
    · cases h; rfl
