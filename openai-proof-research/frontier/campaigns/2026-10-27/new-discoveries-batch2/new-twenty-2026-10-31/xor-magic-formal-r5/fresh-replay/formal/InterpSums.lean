import InterpGraph
import LiftSums
set_option linter.unusedSectionVars false
namespace XorMagic
variable {A : Type*} [AddCommGroup A]
theorem four_sum_nonzero (f : Four → A) (h : ∑ a, f a = 0)
    (hchar : ∀ z : A, z+z=0) : (∑ a : NonzeroFour, f a.1) = f 0 := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun a : Four => a = 0) f
  have hz : (default : {a : Four // a = 0}).val = 0 := (default : {a : Four // a = 0}).property
  simp only [Fintype.sum_unique, hz] at hs
  have he : f 0 + (∑ a : NonzeroFour, f a.1) = 0 := by simpa using hs.trans h
  have hc := hchar (f 0)
  exact add_left_cancel (he.trans hc.symm)

variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj] {d c : ℕ}
theorem blockMate_sum (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (l : V × Four → A) (h : ∀ v, ∑ x : Four, l (v,x) = 0) (i : Fin d) (p : V × Four) :
    ∑ a : Four, l (blockMate F C i a p) = 0 := by
  let e : Four ≃ Four := (Equiv.addLeft (C i p.1 p.2)).trans (C i (F.mate i p.1)).symm
  have he := e.sum_comp (fun x => l (F.mate i p.1,x))
  exact he.trans (h _)

theorem allowed_sum (F : MatchingDecomposition G d) (C : Fin d → V → Four ≃ Four)
    (l : V × Four → A) (h : ∀ v, ∑ x : Four, l (v,x) = 0)
    (hchar : ∀ z : A, z+z=0) (k : ℕ) (i : Fin d) (p : V × Four) :
    ∑ a : InterpAllowed k i, l (blockMate F C i a.1 p) = l (blockMate F C i 0 p) := by
  classical
  have hsum : ∑ a : InterpAllowed k i, l (blockMate F C i a.1 p) =
      ∑ a : Four, if (if i.val < k then a ≠ 0 else a = 0) then l (blockMate F C i a p) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp : ∀ a : Four, a ∈ Finset.univ.filter (fun a => if i.val < k then a ≠ 0 else a = 0) ↔ (if i.val < k then a ≠ 0 else a = 0)) (fun a => l (blockMate F C i a p))).symm
  rw [hsum]
  by_cases hi : i.val < k
  · simp only [hi,ite_true]
    rw [← Finset.sum_filter, Finset.sum_subtype _ (by simp : ∀ a : Four, a ∈ Finset.univ.filter (fun a => a ≠ 0) ↔ a ≠ 0)]
    exact four_sum_nonzero _ (blockMate_sum F C l h i p) hchar
  · simp [hi]

namespace EdgeTransport
theorem interpGraph_sum (T : EdgeTransport G) (F : MatchingDecomposition G d)
    (H : MatchingDecomposition Gᶜ c) (k j : ℕ) (hj : j ≤ c)
    (l : V × Four → A) (h : ∀ v, ∑ x : Four, l (v,x) = 0)
    (hchar : ∀ z : A, z+z=0) (p : V × Four) :
    ∑ q ∈ (T.interpGraph F H k j hj).neighborFinset p, l q =
      ∑ q ∈ T.graph.neighborFinset p, l q := by
  classical
  change (∑ q ∈ (involutionGraph _ _ _).neighborFinset p, l q) = _
  rw [involutionGraph_sum _ _ _ (T.interpMate_distinct F H k j hj)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type]
  change (∑ i : Fin d, ∑ a : InterpAllowed k i,
    l (blockMate F (T.matchingChart F) i a.1 p)) +
    (∑ i : Fin j, ∑ a : Four, l (blockMate H (fun _ _ => Equiv.refl _)
      ⟨i.val,lt_of_lt_of_le i.isLt hj⟩ a p)) = _
  simp_rw [allowed_sum F (T.matchingChart F) l h hchar, blockMate_sum H _ l h]
  simp only [Finset.sum_const_zero, add_zero, T.blockMate_zero F]
  let hm := T.matching F
  have he : T.graph.neighborFinset p = Finset.univ.image (fun i => hm.mate i p) := by
    ext q
    rw [SimpleGraph.mem_neighborFinset]
    simp [hm.cover]
  rw [he,Finset.sum_image]
  · exact Finset.sum_congr rfl (fun _ _ => rfl)
  · exact fun _ _ _ _ he => hm.distinct p he
end EdgeTransport
end XorMagic
