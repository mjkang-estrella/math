import ChosenLiftMagic
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
theorem chosen_open_exists [Nonempty (Fin m)] (S : ColouredSeed G n d false)
    (hd : 4 ≤ d) (hodd : Odd d) : OpenExists (n+2) d := by
  obtain ⟨c,_,_,hr,hm⟩ := chosen_lift_open S hd hodd
  exact ⟨Fin m × Four,inferInstance,inferInstance,
    (affineTransport G (chosenSlopes G S.colouring) c).graph,inferInstance,hr,hm⟩
theorem chosen_closed_exists [Nonempty (Fin m)] (S : ColouredSeed G n d true)
    (hd : 4 ≤ d) (heven : Even d) : ClosedExists (n+2) d := by
  obtain ⟨c,_,_,hr,hm⟩ := chosen_lift_closed S hd heven
  exact ⟨Fin m × Four,inferInstance,inferInstance,
    (affineTransport G (chosenSlopes G S.colouring) c).graph,inferInstance,hr,hm⟩
end XorMagic
