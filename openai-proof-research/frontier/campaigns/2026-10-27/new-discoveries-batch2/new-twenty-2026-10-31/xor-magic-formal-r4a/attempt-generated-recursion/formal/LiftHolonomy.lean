import LiftWalks
import LiftSections
namespace XorMagic
variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

/-- Holonomy connectivity bridge: the affine loop hypothesis must be supplied
by the chosen cycle orientation, not by translation existence alone. -/
theorem connected_of_affine_loop (hG : G.Connected)
    (s : OrientedEdge G → Fin 3) (c : OrientedEdge G → Four)
    (hc : c ∉ (incidenceD G s).range)
    (v : Fin m) (p : G.Walk v v) (a : Bool) (b : Four)
    (hp : ∀ x, (affineTransport G s c).along p x = affine a b x) :
    (affineTransport G s c).graph.Connected := by
  let : Nonempty (Fin m) := ⟨v⟩
  apply EdgeTransport.connected_of_full_fibres
  intro r u
  let T := affineTransport G s c
  have heq : ∀ w, (T.fibre r w).card = (T.fibre r v).card :=
    fun w => T.fibre_card_reachable r (hG.preconnected w v)
  rcases T.fibre_sizes_of_affine_loop r p a b hp with h0 | h1 | h3 | h4
  · have hn := T.fibre_nonempty_of_connected hG r v
    omega
  · exact False.elim (hc (constants_in_range_of_singleton G s c r
      (fun w => (heq w).trans h1)))
  · exact False.elim (hc (constants_in_range_of_three G s c r
      (fun w => (heq w).trans h3)))
  · exact (heq u).trans h4

/-- Nonidentity affine holonomy has a unique fixed fibre point. -/
theorem unique_fixed_of_affine_loop (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (v : Fin m) (p : G.Walk v v)
    (a : Bool) (b : Four)
    (hp : ∀ x, (affineTransport G s c).along p x = affine a b x) :
    ∃! x, (affineTransport G s c).along p x = x := by
  simpa only [hp] using affine_unique_fixed a b
end XorMagic
