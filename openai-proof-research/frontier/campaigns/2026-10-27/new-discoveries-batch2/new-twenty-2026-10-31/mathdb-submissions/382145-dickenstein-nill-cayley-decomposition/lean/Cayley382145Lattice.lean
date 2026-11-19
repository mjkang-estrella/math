import Cayley382145Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-! # MathDB 382145: integral splitting and the Cayley identification

If an integral affine map `L = A(·) - c : ℤ^n → ℤ^t` sends every generator to a vertex of the
standard simplex and hits every vertex, then `A(v_j - v_0) = e_j` gives a section, the kernel
has a `ℤ`-basis (PID), `ℤ^n ≅ ℤ^r × ℤ^t` with `r + t = n`, and the real extension maps the
lattice hull onto `conv ⋃ (P_i × {e_i})`, `P_i` the hull of the projected fibre generators. -/

namespace Cayley382145

open Finset
open scoped Matrix

/-- Integral standard-simplex vertices. -/
def zVertex {t : ℕ} : Option (Fin t) → Fin t → ℤ
  | none => 0
  | some j => Pi.single j 1

theorem castPt_zVertex {t : ℕ} (i : Option (Fin t)) : castPt (zVertex i) = cayleyVertex i := by
  cases i with
  | none =>
    funext j
    simp [zVertex, cayleyVertex, castPt]
  | some j =>
    funext j'
    by_cases h : j' = j
    · subst h
      simp [zVertex, cayleyVertex, castPt]
    · simp [zVertex, cayleyVertex, castPt, h]

theorem castPt_sub {ι : Type*} (v w : ι → ℤ) : castPt (v - w) = castPt v - castPt w := by
  funext i
  simp [castPt]

theorem realExt_mulVec_castPt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) (p : ι → ℤ) : realExt g *ᵥ castPt p = castPt (g p) := by
  funext k
  have h := RingHom.map_mulVec (Int.castRingHom ℝ) (LinearMap.toMatrix' g) p k
  rw [LinearMap.toMatrix'_mulVec] at h
  exact h.symm

/-- `p ↦ (p, e_i)` as a real affine map. -/
noncomputable def cayleyAff {k t : ℕ} (i : Option (Fin t)) : (Fin k → ℝ) →ᵃ[ℝ] (Fin k ⊕ Fin t → ℝ) where
  toFun := cayleyEmbed i
  linear := LinearMap.pi (Sum.elim (fun m : Fin k => (LinearMap.proj m : (Fin k → ℝ) →ₗ[ℝ] ℝ))
    (fun _ : Fin t => (0 : (Fin k → ℝ) →ₗ[ℝ] ℝ)))
  map_vadd' p w := by
    funext s
    cases s with
    | inl m => simp [cayleyEmbed, vadd_eq_add, LinearMap.pi_apply]
    | inr j => simp [cayleyEmbed, vadd_eq_add, LinearMap.pi_apply]

theorem cayley_of_projection {n t : ℕ} (V : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) →ₗ[ℤ] (Fin t → ℤ))
    (c : Fin t → ℤ) (ht : 1 ≤ t)
    (himg : ∀ v ∈ V, ∃ i : Option (Fin t), A v - c = zVertex i)
    (hhit : ∀ i : Option (Fin t), ∃ v ∈ V, A v - c = zVertex i) :
    ∃ k, k + t = n ∧ IsCayleySumIn (latticeHull V) k t := by
  classical
  obtain ⟨v₀, hv₀, h₀⟩ := hhit none
  have hAv₀ : A v₀ = c := by
    have h := h₀
    simp only [zVertex] at h
    exact sub_eq_zero.mp h
  choose vj hvj hvjA using fun j : Fin t => hhit (some j)
  have hAdiff : ∀ j, A (vj j - v₀) = Pi.single j 1 := by
    intro j
    have h1 := hvjA j
    simp only [zVertex] at h1
    rw [map_sub, hAv₀, h1]
  let sec : (Fin t → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun γ => ∑ j, γ j • (vj j - v₀)
      map_add' := fun γ δ => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r γ => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hAsec : ∀ γ, A (sec γ) = γ := by
    intro γ
    show A (∑ j, γ j • (vj j - v₀)) = γ
    rw [map_sum]
    have hterm : ∀ j, A (γ j • (vj j - v₀)) = γ j • Pi.single j 1 := fun j => by
      rw [← hAdiff j]
      exact A.map_smul (γ j) (vj j - v₀)
    simp only [hterm]
    funext m
    rw [Finset.sum_apply, Finset.sum_eq_single m]
    · simp
    · intro j _ hjm
      simp [Ne.symm hjm]
    · intro h
      exact absurd (Finset.mem_univ m) h
  let e₁ : (Fin n → ℤ) ≃ₗ[ℤ] LinearMap.ker A × (Fin t → ℤ) :=
    { toFun := fun x => (⟨x - sec (A x), by rw [LinearMap.mem_ker, map_sub, hAsec, sub_self]⟩, A x)
      map_add' := fun x y => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, Prod.fst_add, Submodule.coe_add]
          abel
        · simp only [map_add, Prod.snd_add]
      map_smul' := fun r x => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_smul, Prod.smul_fst, SetLike.val_smul, RingHom.id_apply, smul_sub]
        · simp only [map_smul, Prod.smul_snd, RingHom.id_apply]
      invFun := fun p => (p.1 : Fin n → ℤ) + sec p.2
      left_inv := fun x => by simp only [sub_add_cancel]
      right_inv := fun p => by
        obtain ⟨⟨k, hk⟩, γ⟩ := p
        have hk' : A k = 0 := hk
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, hk', zero_add, hAsec, add_sub_cancel_right]
        · simp only [map_add, hk', zero_add, hAsec] }
  obtain ⟨r, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin n)) (LinearMap.ker A)
  let g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin r ⊕ Fin t → ℤ) :=
    e₁.trans ((bK.equivFun.prodCongr (LinearEquiv.refl ℤ (Fin t → ℤ))).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) ℤ ℤ).symm)
  have hg_inr : ∀ x j, g x (Sum.inr j) = A x j := by
    intro x j
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, LinearEquiv.refl_apply]
    rfl
  have hrank : r + t = n := by
    have h := LinearEquiv.finrank_eq g
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
    omega
  let α : (Fin n → ℤ) → Fin r → ℤ := fun v m => g (v - v₀) (Sum.inl m)
  have hgv : ∀ v (i : Option (Fin t)), A v - c = zVertex i →
      castPt (g (v - v₀)) = cayleyEmbed i (castPt (α v)) := by
    intro v i hvi
    funext s
    cases s with
    | inl m => rfl
    | inr j =>
      have e1 : A (v - v₀) = zVertex i := by rw [map_sub, hAv₀, hvi]
      show ((g (v - v₀) (Sum.inr j) : ℤ) : ℝ) = cayleyVertex i j
      rw [hg_inr, e1, ← castPt_zVertex]
      rfl
  let Q : Option (Fin t) → Finset (Fin r → ℤ) := fun i =>
    (V.filter (fun v => A v - c = zVertex i)).image α
  have hQne : ∀ i, (Q i).Nonempty := by
    intro i
    obtain ⟨v, hv, hvi⟩ := hhit i
    exact ⟨α v, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩, rfl⟩⟩
  let M := realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ))
  let φA : (Fin n → ℝ) →ᵃ[ℝ] (Fin r ⊕ Fin t → ℝ) :=
    { toFun := fun x => M *ᵥ (x - castPt v₀)
      linear := Matrix.toLin' M
      map_vadd' := fun p w => by
        show M *ᵥ (w + p - castPt v₀) = Matrix.toLin' M w + M *ᵥ (p - castPt v₀)
        rw [add_sub_assoc, Matrix.mulVec_add, Matrix.toLin'_apply] }
  have hφv : ∀ v, φA (castPt v) = castPt (g (v - v₀)) := by
    intro v
    show realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ)) *ᵥ (castPt v - castPt v₀) = _
    rw [← castPt_sub]
    exact realExt_mulVec_castPt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ)) (v - v₀)
  refine ⟨r, hrank, ht, g, v₀, Q, hQne, ?_⟩
  show φA '' latticeHull V = _
  rw [latticeHull, AffineMap.image_convexHull]
  apply Set.Subset.antisymm
  · apply convexHull_mono
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨i, hvi⟩ := himg v hv
    refine Set.mem_iUnion.mpr ⟨i, castPt (α v), subset_convexHull ℝ _ ⟨α v, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩, rfl⟩)
    · rw [hφv, hgv v i hvi]
  · apply convexHull_min _ (convex_convexHull ℝ _)
    refine Set.iUnion_subset fun i => ?_
    have hc : cayleyEmbed i '' latticeHull (Q i) = cayleyAff i '' latticeHull (Q i) := rfl
    rw [hc, latticeHull, AffineMap.image_convexHull]
    apply convexHull_mono
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨v, hvf, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hv, hvi⟩ := Finset.mem_filter.mp hvf
    refine ⟨castPt v, ⟨v, hv, rfl⟩, ?_⟩
    rw [hφv, hgv v i hvi]
    rfl

end Cayley382145
