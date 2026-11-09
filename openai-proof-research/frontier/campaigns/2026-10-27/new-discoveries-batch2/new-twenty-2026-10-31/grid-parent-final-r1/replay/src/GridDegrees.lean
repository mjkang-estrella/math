module
public import GridFreePaths
@[expose] public section
set_option linter.unusedSimpArgs false
namespace Grid343536
open Finset SimpleGraph
instance pathDecAdj (m : ℕ) : DecidableRel (pathGraph m).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

theorem path_degree_formula {m : ℕ} (i : Fin m) :
    (pathGraph m).degree i = (if 0 < i.val then 1 else 0) +
      (if i.val + 1 < m then 1 else 0) := by
  classical
  have hi := i.isLt
  have he : (pathGraph m).neighborFinset i =
      (if h : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅) ∪
      (if h : i.val + 1 < m then {⟨i.val + 1, h⟩} else ∅) := by
    ext j
    simp only [mem_neighborFinset, pathGraph_adj, mem_union]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  rw [← card_neighborFinset_eq_degree, he]
  have hne : i.val - 1 ≠ i.val + 1 := by omega
  split_ifs <;> simp_all [Fin.ext_iff]

theorem grid_degree_formula {m n : ℕ} (x : Fin m × Fin n) :
    (G m n).degree x =
      (if 0 < x.1.val then 1 else 0) + (if x.1.val + 1 < m then 1 else 0) +
      ((if 0 < x.2.val then 1 else 0) + (if x.2.val + 1 < n then 1 else 0)) := by
  change (pathGraph m □ pathGraph n).degree x = _
  rw [degree_boxProd, path_degree_formula, path_degree_formula]

theorem ladder_free (n : ℕ) (hn : 3 ≤ n) : HasFreeVertex (G 2 n) := by
  let z : Fin n := ⟨0, by omega⟩
  refine ⟨(0,z), ?_⟩
  intro g hg
  have hp : g (1,z) = (1,z) := by
    have ha : (G 2 n).Adj (0,z) (1,z) := (grid_adj_iff _ _).mpr (Or.inr ⟨Or.inl rfl, rfl⟩)
    have hb := g.map_rel_iff.mpr ha
    rw [hg] at hb
    have hd := g.degree_eq (1,z)
    rw [grid_degree_formula, grid_degree_formula] at hd
    have hi := (g (1,z)).1.isLt
    have hj := (g (1,z)).2.isLt
    rcases (grid_adj_iff _ _).mp hb with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hv : (g (1,z)).1.val = 0 := congrArg Fin.val h1.symm
      have hz : z.val = 0 := rfl
      have hv2 : (g (1,z)).2.val = 1 := by change z.val + 1 = _ ∨ _ + 1 = z.val at h2; omega
      simp only [hv, hv2, z, Fin.val_zero, Fin.val_one] at hd
      split_ifs at hd <;> omega
    · apply Prod.ext
      · apply Fin.ext
        change (0 + 1 = (g (1,z)).1.val ∨ (g (1,z)).1.val + 1 = 0) at h1
        change (g (1,z)).1.val = 1
        omega
      · exact h2.symm
  let f := transpose 2 n
  let k := (f.symm.trans g).trans f
  have he := row_determinism (Setoid.ker (id : Fin n × Fin 2 → _))
    (by intro u v h w; change u = v at h; subst v; rfl) k (by
      intro j h0
      fin_cases j
      · change f (g (0,z)) = f (0,z)
        rw [hg]
      · change f (g (1,z)) = f (1,z)
        rw [hp])
  apply DFunLike.ext
  intro x
  have h := he (f x)
  change f (g (f.symm (f x))) = f x at h
  apply f.injective
  simpa using h
end Grid343536
