import Literal
namespace XorMagic
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Fixed point free involutions partition all graph edges, with distinct mates at each vertex. -/
structure MatchingDecomposition (G : SimpleGraph V) (d : ℕ) where
  mate : Fin d → V → V
  involutive : ∀ i v, mate i (mate i v) = v
  no_fixed : ∀ i v, mate i v ≠ v
  distinct : ∀ v, Function.Injective (fun i => mate i v)
  cover : ∀ v w, G.Adj v w ↔ ∃ i, mate i v = w

structure FactorCycleData (G : SimpleGraph V) (d : ℕ) where
  factors : MatchingDecomposition G d
  complementFactors : MatchingDecomposition Gᶜ (Fintype.card V-1-d)
  two_le : 2 ≤ d
  length : ℕ
  positive : 0 < length
  not_three : length % 3 ≠ 0
  cycle : Fin length → V
  injective : Function.Injective cycle
  edges : ∀ i, factors.mate ⟨0, by omega⟩ (cycle i) = cycle ⟨(i.val+1)%length, Nat.mod_lt _ positive⟩ ∨
    factors.mate ⟨1, by omega⟩ (cycle i) = cycle ⟨(i.val+1)%length, Nat.mod_lt _ positive⟩

structure LiftSeed (G : SimpleGraph V) [DecidableRel G.Adj] (n d : ℕ) (closed : Bool) where
  regular : G.IsRegularOfDegree d
  magic : if closed then ClosedMagic G n else OpenMagic G n
  factorCycle : FactorCycleData G d
end XorMagic
