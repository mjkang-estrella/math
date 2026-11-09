import LiftScalarWalk
import StrongCycles
namespace XorMagic
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
structure FactorColouring (F : MatchingDecomposition G d) (hd : 2 ≤ d) where
  colour : V → Bool
  proper0 : ∀ v, colour v ≠ colour (F.mate ⟨0, by omega⟩ v)
  proper1 : ∀ v, colour v ≠ colour (F.mate ⟨1, by omega⟩ v)

namespace FactorColouring
variable {F : MatchingDecomposition G d} {hd : 2 ≤ d} (b : FactorColouring F hd)
def directed (u v : V) : Fin 3 :=
  if F.mate ⟨0, by omega⟩ u = v then (if b.colour u then 1 else 2)
  else if F.mate ⟨1, by omega⟩ u = v then (if b.colour u then 2 else 1)
  else 0

omit [Fintype V] [DecidableEq V] in
theorem mate_reverse (i : Fin d) (u v : V) : F.mate i u = v ↔ F.mate i v = u := by
  constructor <;> intro h
  · rw [← h, F.involutive]
  · rw [← h, F.involutive]

omit [Fintype V] in
theorem reverse (u v : V) : b.directed v u = inverseScalar (b.directed u v) := by
  have h0 := mate_reverse (F := F) ⟨0, by omega⟩ u v
  have h1 := mate_reverse (F := F) ⟨1, by omega⟩ u v
  unfold directed
  by_cases e0 : F.mate ⟨0, by omega⟩ u = v
  · have bc := b.proper0 u
    rw [e0] at bc
    simp only [h0.mp e0, e0, ite_true]
    cases hu : b.colour u <;> cases hv : b.colour v <;> simp_all <;> decide
  · by_cases e1 : F.mate ⟨1, by omega⟩ u = v
    · have bc := b.proper1 u
      rw [e1] at bc
      simp only [e0, show ¬ F.mate ⟨0, by omega⟩ v = u from fun h => e0 (h0.mpr h),
        e1, h1.mp e1, ite_true, ite_false]
      cases hu : b.colour u <;> cases hv : b.colour v <;> simp_all <;> decide
    · simp only [e0,e1,show ¬ F.mate ⟨0, by omega⟩ v = u from fun h => e0 (h0.mpr h),
        show ¬ F.mate ⟨1, by omega⟩ v = u from fun h => e1 (h1.mpr h), ite_false]
      decide
end FactorColouring
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
def chosenSlopes {d : ℕ} {F : MatchingDecomposition G d} {hd : 2 ≤ d}
    (b : FactorColouring F hd) (e : OrientedEdge G) : Fin 3 := b.directed e.val.1 e.val.2

theorem chosen_outgoing {d : ℕ} {F : MatchingDecomposition G d} {hd : 2 ≤ d}
    (b : FactorColouring F hd) {u v : Fin m} (h : G.Adj u v) :
    outgoingSlope G (chosenSlopes G b) u v = b.directed u v := by
  rcases lt_or_gt_of_ne h.ne with huv | hvu
  · simp [outgoingSlope, chosenSlopes, huv, h]
  · have hn : ¬ u < v := not_lt_of_gt hvu
    simp only [outgoingSlope, hn, false_and, dite_false, hvu, h.symm, and_self, dite_true,
      chosenSlopes]
    rw [b.reverse]
    have : ∀ a : Fin 3, inverseScalar (inverseScalar a) = a := by decide
    exact this _
end XorMagic
