import R73.Cert

/-!
# A facet of `P_Δ^{4,4,5}` that is not obtained by collapsing from `P_Δ^{4,4,4}`

This refutes the collapsing conjecture (MathDB 378395) of Eriksson, Fienberg, Rinaldo and
Sullivant at `p = q = 4`, `r = 5`.
-/

open scoped BigOperators

namespace R73.Main

open R73 R73.Cert

/-- Real weights of an integer functional. -/
noncomputable def toR (w : Margin 4 4 5 → ℤ) : Margin 4 4 5 → ℝ := fun x => (w x : ℝ)

theorem dotL_toR_col (w : Margin 4 4 5 → ℤ) (c : Cell 4 4 5) :
    dotL (toR w) (col c) = (onCol w c : ℝ) := by
  rw [dotL_col]
  simp [toR, onCol]

theorem dotL_single (w : Margin 4 4 5 → ℝ) (a : Margin 4 4 5) :
    dotL w (Pi.single a 1) = w a := by
  rw [dotL_apply]
  simp [Pi.single_apply]

/-- The facet-defining functional. -/
noncomputable def ell : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR ellZ)

/-- The facet. -/
def F : Set (Margin 4 4 5 → ℝ) := {y | y ∈ marginalCone 4 4 5 ∧ ell y = 0}

theorem ell_nonneg_cone : ∀ y ∈ marginalCone 4 4 5, 0 ≤ ell y := by
  rintro y ⟨x, hx, rfl⟩
  rw [ell, dotL_margins]
  refine Finset.sum_nonneg fun c _ => ?_
  rw [dotL_toR_col]
  exact mul_nonneg (hx c) (by exact_mod_cast ell_nonneg c)

theorem card_margin : Fintype.card (Margin 4 4 5) = 56 := by
  simp [Fintype.card_sum, Fintype.card_prod]

theorem finrank_margin : Module.finrank ℝ (Margin 4 4 5 → ℝ) = 56 := by
  rw [Module.finrank_fintype_fun_eq_card, card_margin]

/-- The 43 independent tight columns together with one column off the facet. -/
noncomputable def vfam : Option (Fin 43) → (Margin 4 4 5 → ℝ)
  | none => col c0
  | some t => col (bcell t)

theorem ell_col (c : Cell 4 4 5) : ell (col c) = (onCol ellZ c : ℝ) := by
  rw [ell, dotL_toR_col]

/-- Real functionals from the integer tables. -/
noncomputable def phiL (s : Fin 43) : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR (phiZ s))

noncomputable def psiL (s : Fin 12) : (Margin 4 4 5 → ℝ) →ₗ[ℝ] ℝ := dotL (toR (psiZ s))

theorem phiL_col (s : Fin 43) (c : Cell 4 4 5) : phiL s (col c) = (onCol (phiZ s) c : ℝ) := by
  rw [phiL, dotL_toR_col]

theorem psiL_col (s : Fin 12) (c : Cell 4 4 5) : psiL s (col c) = 0 := by
  rw [psiL, dotL_toR_col, psi_cols]
  norm_num

theorem psiL_single (s t : Fin 12) : psiL s (Pi.single (piv t) 1) = if s = t then 1 else 0 := by
  rw [psiL, dotL_single, toR, psi_piv]
  split_ifs <;> norm_num

theorem psiL_margins (s : Fin 12) (x : Cell 4 4 5 → ℝ) : psiL s (margins x) = 0 := by
  rw [psiL, dotL_margins]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [dotL_toR_col, psi_cols]
  simp

theorem vfam_li : LinearIndependent ℝ vfam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g none = 0 := by
    have h := congrArg ell hg
    rw [map_sum, Fintype.sum_option, map_zero] at h
    simp only [vfam, map_smul, smul_eq_mul, ell_col, ell_c0, ell_basis] at h
    simpa using h
  have hs : ∀ s, g (some s) = 0 := by
    intro s
    have h := congrArg (phiL s) hg
    rw [map_sum, Fintype.sum_option, map_zero] at h
    simp only [vfam, map_smul, smul_eq_mul, phiL_col, phi_biorth, h0, zero_mul, zero_add] at h
    simpa using h
  intro o
  cases o with
  | none => exact h0
  | some s => exact hs s

theorem basis_li : LinearIndependent ℝ (fun t : Fin 43 => col (bcell t)) :=
  vfam_li.comp some (Option.some_injective _)

/-- The twelve margin relations as one linear map. -/
noncomputable def L12 : (Margin 4 4 5 → ℝ) →ₗ[ℝ] (Fin 12 → ℝ) :=
  LinearMap.pi fun s => psiL s

theorem L12_surj : Function.Surjective L12 := by
  intro y
  refine ⟨∑ t, y t • Pi.single (piv t) 1, ?_⟩
  funext s
  simp only [L12, LinearMap.pi_apply, map_sum, map_smul, psiL_single, smul_eq_mul]
  simp

theorem cone_le_ker_L12 : marginalCone 4 4 5 ⊆ LinearMap.ker L12 := by
  rintro y ⟨x, -, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  funext s
  simp only [L12, LinearMap.pi_apply, psiL_margins]
  rfl

/-- The thirteen functionals `ℓ, ψ₁, …, ψ₁₂` as one linear map. -/
noncomputable def L13 : (Margin 4 4 5 → ℝ) →ₗ[ℝ] (Option (Fin 12) → ℝ) :=
  LinearMap.pi fun o => match o with
    | none => ell
    | some s => psiL s

theorem L13_surj : Function.Surjective L13 := by
  intro y
  refine ⟨∑ t, y (some t) • Pi.single (piv t) 1 +
      (y none - ∑ t, y (some t) * toR ellZ (piv t)) • col c0, ?_⟩
  funext o
  cases o with
  | none =>
      simp only [L13, LinearMap.pi_apply, map_add, map_sum, map_smul, ell_col, ell_c0,
        smul_eq_mul]
      simp only [ell, dotL_single]
      push_cast
      ring
  | some s =>
      simp only [L13, LinearMap.pi_apply, map_add, map_sum, map_smul, psiL_single, psiL_col,
        smul_eq_mul]
      simp

theorem F_le_ker_L13 : F ⊆ LinearMap.ker L13 := by
  rintro y ⟨⟨x, -, rfl⟩, hy⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  funext o
  cases o with
  | none => exact hy
  | some s =>
      simp only [L13, LinearMap.pi_apply, psiL_margins]
      rfl

theorem col_mem_F_iff (c : Cell 4 4 5) : col c ∈ F ↔ onCol ellZ c = 0 := by
  simp only [F, Set.mem_ofPred_eq, col_mem c, true_and, ell_col]
  exact_mod_cast Iff.rfl

theorem finrank_span_cone :
    Module.finrank ℝ (Submodule.span ℝ (marginalCone 4 4 5)) = 44 := by
  apply le_antisymm
  · have h1 := Submodule.finrank_mono
      ((Submodule.span_le (p := LinearMap.ker L12)).mpr cone_le_ker_L12)
    have h2 := finrank_ker_of_surjective L12 L12_surj
    rw [finrank_margin, Fintype.card_fin] at h2
    omega
  · have h1 : Submodule.span ℝ (Set.range vfam) ≤ Submodule.span ℝ (marginalCone 4 4 5) := by
      apply Submodule.span_mono
      rintro _ ⟨o, rfl⟩
      cases o <;> exact col_mem _
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card vfam_li, Fintype.card_option, Fintype.card_fin] at h2
    exact h2

theorem finrank_span_F : Module.finrank ℝ (Submodule.span ℝ F) = 43 := by
  apply le_antisymm
  · have h1 := Submodule.finrank_mono
      ((Submodule.span_le (p := LinearMap.ker L13)).mpr F_le_ker_L13)
    have h2 := finrank_ker_of_surjective L13 L13_surj
    rw [finrank_margin, Fintype.card_option, Fintype.card_fin] at h2
    omega
  · have h1 : Submodule.span ℝ (Set.range fun t : Fin 43 => col (bcell t)) ≤
        Submodule.span ℝ F := by
      apply Submodule.span_mono
      rintro _ ⟨t, rfl⟩
      exact (col_mem_F_iff _).mpr (ell_basis t)
    have h2 := Submodule.finrank_mono h1
    rw [finrank_span_eq_card basis_li, Fintype.card_fin] at h2
    exact h2

/-- `F` is a facet of the marginal cone `P_Δ^{4,4,5}`. -/
theorem F_isFacet : IsFacet (marginalCone 4 4 5) F :=
  ⟨⟨ell, ell_nonneg_cone, rfl⟩, by rw [finrank_span_F, finrank_span_cone]⟩

/-- `F` is not obtained by collapsing from any facet of `P_Δ^{4,4,4}`. -/
theorem F_not_collapsed : ¬ ObtainedByCollapsing 4 4 5 4 4 4 F := by
  intro h
  obtain ⟨k, l, hkl, hag⟩ := collapsed_slices_agree (by norm_num) F h
  obtain ⟨i, j, hij⟩ := slices_distinct k l hkl
  exact hij (by rw [← col_mem_F_iff, ← col_mem_F_iff]; exact hag i j)

/-- Explicit counterexample: a facet of `P_Δ^{4,4,5}` not obtained by collapsing from
`P_Δ^{4,4,4}`. -/
theorem exists_noncollapsible_facet :
    ∃ F : Set (Margin 4 4 5 → ℝ), IsFacet (marginalCone 4 4 5) F ∧
      ¬ ObtainedByCollapsing 4 4 5 4 4 4 F :=
  ⟨F, F_isFacet, F_not_collapsed⟩

/-- MathDB 378395: the collapsing conjecture is false. -/
theorem collapsing_conjecture_false : ¬ CollapsingConjecture := by
  intro h
  exact F_not_collapsed (h 4 4 5 (by norm_num) le_rfl (by norm_num) F F_isFacet)

end R73.Main
