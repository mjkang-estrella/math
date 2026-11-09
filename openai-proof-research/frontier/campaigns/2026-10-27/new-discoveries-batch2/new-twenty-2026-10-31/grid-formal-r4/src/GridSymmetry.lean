module
public import GridBasic
@[expose] public section

namespace Grid343536
open SimpleGraph
def rowFlip (m n : ℕ) : G m n ≃g G m n where
  toEquiv := Fin.revPerm.prodCongr (Equiv.refl _)
  map_rel_iff' := by
    intro x y
    simp only [grid_adj_iff, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Fin.revPerm_apply, Equiv.refl_apply, Fin.val_rev, Fin.ext_iff]
    have hx := x.1.isLt
    have hy := y.1.isLt
    omega

def colFlip (m n : ℕ) : G m n ≃g G m n where
  toEquiv := (Equiv.refl _).prodCongr Fin.revPerm
  map_rel_iff' := by
    intro x y
    simp only [grid_adj_iff, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Fin.revPerm_apply, Equiv.refl_apply, Fin.val_rev, Fin.ext_iff]
    have hx := x.2.isLt
    have hy := y.2.isLt
    omega

def transpose (m n : ℕ) : G m n ≃g G n m :=
  SimpleGraph.boxProdComm (pathGraph m) (pathGraph n)

def A0 (m n : ℕ) : Subgroup (G m n ≃g G m n) :=
  if h : m = n then by
    subst n
    exact Subgroup.closure {rowFlip m m, colFlip m m, transpose m m}
  else Subgroup.closure {rowFlip m n, colFlip m n}

def Hpi {m n : ℕ} (r : Setoid (Fin m × Fin n)) :
    Subgroup (G m n ≃g G m n) where
  carrier := {g | g ∈ A0 m n ∧ ∀ x, r (g x) x}
  one_mem' := ⟨Subgroup.one_mem _, fun x => r.refl x⟩
  mul_mem' := by
    rintro g k ⟨hg, hgr⟩ ⟨hk, hkr⟩
    exact ⟨Subgroup.mul_mem _ hg hk, fun x => r.trans (hgr (k x)) (hkr x)⟩
  inv_mem' := by
    rintro g ⟨hg, hgr⟩
    refine ⟨Subgroup.inv_mem _ hg, fun x => ?_⟩
    have h := r.symm (hgr (g⁻¹ x))
    simpa using h

theorem Hpi_orbit_le {m n : ℕ} (r : Setoid (Fin m × Fin n)) :
    orbitSetoid (G m n) (Hpi r) ≤ r := by
  rintro u v ⟨g, hg, rfl⟩
  exact r.symm (hg.2 u)
end Grid343536
