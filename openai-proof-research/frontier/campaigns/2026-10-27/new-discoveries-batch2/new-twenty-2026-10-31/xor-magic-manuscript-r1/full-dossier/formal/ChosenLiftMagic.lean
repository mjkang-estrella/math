import ColouredSeed
import ColourScalar
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]

/-- The chosen lift: translation existence, connectivity, regularity and literal open magic.
No complement decomposition is needed for this endpoint. -/
theorem chosen_lift_open [Nonempty (Fin m)] (S : ColouredSeed G n d false)
    (hd : 4 ≤ d) (hodd : Odd d) :
    ∃ c : OrientedEdge G → Four,
      incidenceB G (chosenSlopes G S.colouring) c = 0 ∧
      c ∉ (incidenceD G (chosenSlopes G S.colouring)).range ∧
      (affineTransport G (chosenSlopes G S.colouring) c).graph.IsRegularOfDegree d ∧
      OpenMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2) := by
  obtain ⟨hconn,l,hl⟩ := S.seed.magic
  obtain ⟨c,hB,hD⟩ := affine_translation_exists_regular G S.seed.regular hd (chosenSlopes G S.colouring)
  have hn : S.walk.length % 3 ≠ 0 := by rw [S.length_eq]; exact S.seed.factorCycle.not_three
  obtain ⟨a,b,hab⟩ := nontrivial_holonomy_of_omega_walk G _ c S.walk S.oriented hn
  have hc := connected_of_affine_loop G hconn _ c hD _ S.walk a b hab
  exact ⟨c,hB,hD,(affineTransport G _ c).regular S.seed.regular,
    open_magic_of_scalar_sum G l hl _ c hB (chosen_open_scalar S.colouring hodd) hc⟩

/-- The closed case uses the same chosen slopes, translations and connectivity proof. -/
theorem chosen_lift_closed [Nonempty (Fin m)] (S : ColouredSeed G n d true)
    (hd : 4 ≤ d) (heven : Even d) :
    ∃ c : OrientedEdge G → Four,
      incidenceB G (chosenSlopes G S.colouring) c = 0 ∧
      c ∉ (incidenceD G (chosenSlopes G S.colouring)).range ∧
      (affineTransport G (chosenSlopes G S.colouring) c).graph.IsRegularOfDegree d ∧
      ClosedMagic (affineTransport G (chosenSlopes G S.colouring) c).graph (n+2) := by
  obtain ⟨hconn,l,hl⟩ := S.seed.magic
  obtain ⟨c,hB,hD⟩ := affine_translation_exists_regular G S.seed.regular hd (chosenSlopes G S.colouring)
  have hn : S.walk.length % 3 ≠ 0 := by rw [S.length_eq]; exact S.seed.factorCycle.not_three
  obtain ⟨a,b,hab⟩ := nontrivial_holonomy_of_omega_walk G _ c S.walk S.oriented hn
  have hc := connected_of_affine_loop G hconn _ c hD _ S.walk a b hab
  exact ⟨c,hB,hD,(affineTransport G _ c).regular S.seed.regular,
    closed_magic_of_scalar_sum G l hl _ c hB (chosen_closed_scalar S.colouring heven) hc⟩
end XorMagic
