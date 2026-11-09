import LiftConstantSum
import LiftSums
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

theorem affine_neighbor_sum (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (v : Fin m) (x : Four) :
    (∑ u ∈ G.neighborFinset v, (affineTransport G s c).map v u x) =
      (∑ u ∈ G.neighborFinset v, scalar (outgoingSlope G s v u) x) + incidenceB G s c v := by
  calc
    _ = ∑ u ∈ G.neighborFinset v, (scalar (outgoingSlope G s v u) x +
        (affineTransport G s c).map v u 0) :=
      Finset.sum_congr rfl (fun u _ => outgoing_affine G s c v u x)
    _ = _ := by rw [Finset.sum_add_distrib, incidenceB_eq_neighbor_constants]

/-- Open magic transfer with the exact remaining scalar cancellation displayed. -/
theorem open_magic_of_scalar_sum {n : ℕ} (l : Fin m ≃ Bits n)
    (hl : ∀ v, ∑ u ∈ G.neighborFinset v, l u = 0)
    (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    (hc : incidenceB G s c = 0)
    (hs : ∀ v x, ∑ u ∈ G.neighborFinset v, scalar (outgoingSlope G s v u) x = 0)
    (hconn : (affineTransport G s c).graph.Connected) :
    OpenMagic (affineTransport G s c).graph (n+2) := by
  classical
  refine ⟨hconn,EdgeTransport.label l, ?_⟩
  rintro ⟨v,x⟩
  rw [EdgeTransport.sum_label, hl, affine_neighbor_sum, hs]
  have hz : incidenceB G s c v = 0 := congrFun hc v
  rw [hz,add_zero]
  exact (bitsFourAddHom n).map_zero

/-- Closed magic transfer with the exact remaining scalar cancellation displayed. -/
theorem closed_magic_of_scalar_sum {n : ℕ} (l : Fin m ≃ Bits n)
    (hl : ∀ v, l v + ∑ u ∈ G.neighborFinset v, l u = 0)
    (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    (hc : incidenceB G s c = 0)
    (hs : ∀ v x, x + ∑ u ∈ G.neighborFinset v, scalar (outgoingSlope G s v u) x = 0)
    (hconn : (affineTransport G s c).graph.Connected) :
    ClosedMagic (affineTransport G s c).graph (n+2) := by
  classical
  refine ⟨hconn,EdgeTransport.label l, ?_⟩
  rintro ⟨v,x⟩
  rw [EdgeTransport.sum_label, affine_neighbor_sum]
  have hz : incidenceB G s c v = 0 := congrFun hc v
  rw [hz,add_zero]
  change bitsFourEquiv n (l v,x) + bitsFourEquiv n _ = 0
  rw [← bitsFourEquiv_add]
  change bitsFourEquiv n (l v + ∑ u ∈ G.neighborFinset v, l u,
    x + ∑ u ∈ G.neighborFinset v, scalar (outgoingSlope G s v u) x) = 0
  rw [hl,hs]
  exact (bitsFourAddHom n).map_zero
end XorMagic
