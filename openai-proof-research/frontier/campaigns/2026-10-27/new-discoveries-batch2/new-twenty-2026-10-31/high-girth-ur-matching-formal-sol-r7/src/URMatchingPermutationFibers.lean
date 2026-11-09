module
public import URMatchingIndependentCount
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype
@[expose] public section
namespace URMatching
open scoped Classical
noncomputable def restriction {N : ℕ} (A : Finset (Fin N))
    (σ : Equiv.Perm (Fin N)) : A ↪ Fin N :=
  ⟨fun x => σ x, fun _ _ h => Subtype.ext (σ.injective h)⟩
/-- All prescribed injective images of A have equally many permutation extensions. -/
noncomputable def restrictionFiberEquiv {N : ℕ} (A : Finset (Fin N))
    (f g : A ↪ Fin N) :
    {σ : Equiv.Perm (Fin N) // restriction A σ = f} ≃
    {σ : Equiv.Perm (Fin N) // restriction A σ = g} := by
  classical
  let ex := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  let τ := Classical.choose ex
  have hτ := Classical.choose_spec ex
  have forward (σ : Equiv.Perm (Fin N)) (h : restriction A σ = f) :
      restriction A (σ.trans τ) = g := by
    apply DFunLike.ext
    intro x
    change τ (σ x) = g x
    have hx := congrArg (fun e : A ↪ Fin N => e x) h
    exact hx ▸ hτ x
  have backward (σ : Equiv.Perm (Fin N)) (h : restriction A σ = g) :
      restriction A (σ.trans τ.symm) = f := by
    apply DFunLike.ext
    intro x
    change τ.symm (σ x) = f x
    apply τ.injective
    simp only [Equiv.apply_symm_apply]
    have hx := congrArg (fun e : A ↪ Fin N => e x) h
    exact hx.trans (hτ x).symm
  exact {
    toFun := fun σ => ⟨σ.val.trans τ, forward σ.val σ.property⟩
    invFun := fun σ => ⟨σ.val.trans τ.symm, backward σ.val σ.property⟩
    left_inv := fun σ => Subtype.ext (by ext x; simp)
    right_inv := fun σ => Subtype.ext (by ext x; simp) }
end URMatching
