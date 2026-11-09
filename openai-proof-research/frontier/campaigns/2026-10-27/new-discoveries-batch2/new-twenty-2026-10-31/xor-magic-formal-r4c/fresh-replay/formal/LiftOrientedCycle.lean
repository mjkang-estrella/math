import LiftScalarWalk
import LiftHolonomy
import LiftCycleWalk
import LiftEdgeCount
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

/-- A proved component result, not a seed-lift endpoint: the consistently
oriented simple cycle is an explicit hypothesis still to be constructed. -/
theorem lift_connected_cycle_of_oriented_walk [Nonempty (Fin m)]
    {d : ℕ} (reg : G.IsRegularOfDegree d) (hd : 4 ≤ d) (hG : G.Connected)
    (s : OrientedEdge G → Fin 3) {v : Fin m} (p : G.Walk v v)
    (hp : p.IsCycle) (ho : OmegaWalk G s p) (hn : p.length % 3 ≠ 0) :
    ∃ c : OrientedEdge G → Four,
      incidenceB G s c = 0 ∧ c ∉ (incidenceD G s).range ∧
      (affineTransport G s c).graph.Connected ∧
      (affineTransport G s c).graph.IsRegularOfDegree d ∧
      ∃ x : Four, ∃ q : (affineTransport G s c).graph.Walk (v,x) (v,x),
        q.IsCycle ∧ q.length = p.length := by
  obtain ⟨c,hB,hD⟩ := affine_translation_exists_regular G reg hd s
  obtain ⟨a,b,hab⟩ := nontrivial_holonomy_of_omega_walk G s c p ho hn
  exact ⟨c,hB,hD,connected_of_affine_loop G hG s c hD v p a b hab,
    (affineTransport G s c).regular reg,
    (affineTransport G s c).cycle_of_affine_holonomy p hp a b hab⟩

/-- r4b's future input to seed assembly. This records only a decomposition of
the actual lifted complement; it asserts neither magic nor a cycle. -/
structure LiftComplementInput (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (d : ℕ) where
  factors : MatchingDecomposition (affineTransport G s c).graphᶜ (4*m-1-d)
end XorMagic
