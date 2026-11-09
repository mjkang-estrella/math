import LiftGraph
import Mathlib.Algebra.BigOperators.Pi
namespace XorMagic

def bitsFourAddHom (n : ℕ) : Bits n × Four →+ Bits (n+2) where
  toFun := bitsFourEquiv n
  map_add' := bitsFourEquiv_add n
  map_zero' := by
    have h := bitsFourEquiv_add n 0 0
    simpa only [zero_add, add_eq_left] using h.symm

namespace EdgeTransport
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (T : EdgeTransport G)

def label {n : ℕ} (l : V ≃ Bits n) : V × Four ≃ Bits (n+2) :=
  (Equiv.prodCongr l (Equiv.refl Four)).trans (bitsFourEquiv n)

theorem sum_label {n : ℕ} (l : V ≃ Bits n) (v : V) (x : Four) :
    ∑ p ∈ T.graph.neighborFinset (v,x), label l p =
      bitsFourEquiv n (∑ u ∈ G.neighborFinset v, l u,
        ∑ u ∈ G.neighborFinset v, T.map v u x) := by
  rw [T.sum_neighbors]
  change (∑ u ∈ G.neighborFinset v, bitsFourAddHom n (l u,T.map v u x)) = _
  rw [← map_sum]
  change bitsFourAddHom n _ = bitsFourAddHom n _
  apply congrArg (bitsFourAddHom n)
  simp only [← prod_mk_sum]

/-- Exact second-coordinate formula for affine transports; constants need not vanish. -/
theorem sum_affine (L : V → V → Four →+ Four) (c : V → V → Four)
    (ha : ∀ u v x, T.map u v x = L u v x + c u v) (v : V) (x : Four) :
    ∑ p ∈ T.graph.neighborFinset (v,x), p.2 =
      (∑ u ∈ G.neighborFinset v, L v u x) + ∑ u ∈ G.neighborFinset v, c v u := by
  rw [T.sum_neighbors]
  simp only [ha, Finset.sum_add_distrib]
end EdgeTransport
end XorMagic
