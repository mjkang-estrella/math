import PDTAR.ReductionFlip
import Mathlib.Combinatorics.SimpleGraph.Finite
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
open scoped symmDiff
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An edge of the cube has one unique coordinate. -/
theorem reduction_adj_iff_toggle (S T : Finset V) :
    (S ∆ T).card = 1 ↔ ∃ v, T = S ∆ {v} := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := card_eq_one.mp h
    refine ⟨v,?_⟩
    rw [← hv]
    simp
  · rintro ⟨v,rfl⟩
    simp

theorem reduction_toggle_injective (S : Finset V) :
    Function.Injective (fun v : V => S ∆ {v}) := by
  intro x y h
  have hh := congrArg (fun T => S ∆ T) h
  simpa using hh

/-- All neighbours are obtained by toggling one coordinate which stays feasible. -/
noncomputable def reduction_neighbor_equiv (G : SimpleGraph V)
    (S : {S : Finset V // IsPD G S}) :
    {v : V // IsPD G (S.val ∆ {v})} ≃ (tar G).neighborSet S where
  toFun v := ⟨⟨S.val ∆ {v.val},v.property⟩, by change (S.val ∆ (S.val ∆ {v.val})).card = 1; simp⟩
  invFun T := by
    have h : ∃ v, T.val.val = S.val ∆ {v} := (reduction_adj_iff_toggle _ _).mp T.property
    exact ⟨Classical.choose h, by rw [← Classical.choose_spec h]; exact T.val.property⟩
  left_inv v := by
    apply Subtype.ext
    apply reduction_toggle_injective S.val
    exact (Classical.choose_spec ((reduction_adj_iff_toggle _ _).mp (show
      (S.val ∆ (S.val ∆ {v.val})).card = 1 by simp))).symm
  right_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec ((reduction_adj_iff_toggle _ _).mp T.property)).symm

/-- The degree bound, expressed as the cardinality of the neighbour subtype. -/
theorem reduction_degree_le (G : SimpleGraph V) (S : {S : Finset V // IsPD G S}) :
    Nat.card ((tar G).neighborSet S) ≤ Fintype.card V := by
  classical
  rw [Nat.card_congr (reduction_neighbor_equiv G S).symm, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_le _

/-- At the full set every coordinate is available, including on the empty type. -/
theorem reduction_degree_top (G : SimpleGraph V) (hG : NoIsolated G) :
    Nat.card ((tar G).neighborSet ⟨univ,isPD_univ G⟩) = Fintype.card V := by
  classical
  have hh : ∀ v : V, IsPD G (univ ∆ {v}) := by
    intro v
    have he : (univ : Finset V) ∆ {v} = univ.erase v := by
      ext x; simp only [mem_symmDiff,mem_univ,mem_singleton,mem_erase]; tauto
    rw [he]
    exact erase_isPD G hG v
  rw [Nat.card_congr (reduction_neighbor_equiv G ⟨univ,isPD_univ G⟩).symm,
    Nat.card_eq_fintype_card]
  simp [hh]

/-- The base order is an invariant of TAR isomorphism. -/
theorem reduction_card_eq {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : NoIsolated G) (hH : NoIsolated H)
    (φ : tar G ≃g tar H) : Fintype.card V = Fintype.card W := by
  have hf : ∀ S : {S : Finset V // IsPD G S},
      Nat.card ((tar G).neighborSet S) = Nat.card ((tar H).neighborSet (φ S)) := by
    intro S
    exact Nat.card_congr (φ.mapNeighborSet S)
  have hf' : ∀ T : {T : Finset W // IsPD H T},
      Nat.card ((tar H).neighborSet T) = Nat.card ((tar G).neighborSet (φ.symm T)) := by
    intro T
    exact Nat.card_congr (φ.symm.mapNeighborSet T)
  have h₁ := reduction_degree_le H (φ ⟨univ,isPD_univ G⟩)
  have h₂ := reduction_degree_le G (φ.symm ⟨univ,isPD_univ H⟩)
  rw [← hf, reduction_degree_top G hG] at h₁
  rw [← hf', reduction_degree_top H hH] at h₂
  exact Nat.le_antisymm h₁ h₂

/-- A direct coordinate calculation: the two common neighbours of a 2-face. -/
theorem reduction_common_neighbors (S : Finset V) (x y : V) (hxy : x ≠ y)
    (T : Finset V) :
    (S ∆ T).card = 1 ∧ ((S ∆ {x} ∆ {y}) ∆ T).card = 1 ↔
      T = S ∆ {x} ∨ T = S ∆ {y} := by
  constructor
  · rintro ⟨ht,hu⟩
    obtain ⟨z,rfl⟩ := (reduction_adj_iff_toggle S T).mp ht
    by_cases hzx : z = x
    · exact .inl (by rw [hzx])
    by_cases hzy : z = y
    · exact .inr (by rw [hzy])
    have he : (S ∆ {x} ∆ {y}) ∆ (S ∆ {z}) = {x,y,z} := by
      ext w
      simp only [mem_symmDiff,mem_singleton,mem_insert]
      by_cases hwx : w = x <;> by_cases hwy : w = y <;> by_cases hwz : w = z <;>
        simp_all <;> tauto
    rw [he] at hu
    have hc : ({x,y,z} : Finset V).card = 3 := by simp [hxy, Ne.symm hzx, Ne.symm hzy]
    omega
  · rintro (rfl | rfl)
    · constructor
      · simp
      · have he : (S ∆ {x} ∆ {y}) ∆ (S ∆ {x}) = {y} := by
          ext w; simp only [mem_symmDiff, mem_singleton]; tauto
        rw [he]; simp
    · constructor
      · simp
      · have he : (S ∆ {x} ∆ {y}) ∆ (S ∆ {y}) = {x} := by
          ext w; simp only [mem_symmDiff, mem_singleton]; tauto
        rw [he]; simp
end PDTAR
