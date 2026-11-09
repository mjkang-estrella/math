import SeedRecursion
namespace XorMagic
variable {m n d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
theorem ColouredSeed.open_interval [Nonempty (Fin m)] (S : ColouredSeed G n d false)
    (hd : 4 ≤ d) (hp : Odd d) (q : ℕ) (hqo : Odd q) (hl : d ≤ q)
    (hu : q ≤ 4*m-4-d) : OpenExists (n+2) q := by
  obtain ⟨hc,l,hm⟩ := S.seed.magic
  obtain ⟨c,hB,_,_,hmagic⟩ := chosen_lift_open S hd hp
  let T := affineTransport G (chosenSlopes G S.colouring) c
  apply T.open_interval_exists S.seed.factorCycle.factors S.seed.factorCycle.complementFactors
    l hc hmagic.1
  · intro p
    rcases p with ⟨v,x⟩
    rw [EdgeTransport.sum_label, hm, affine_neighbor_sum, chosen_open_scalar S.colouring hp]
    have hz : incidenceB G (chosenSlopes G S.colouring) c v = 0 := congrFun hB v
    rw [hz,add_zero]
    exact (bitsFourAddHom n).map_zero
  · omega
  · obtain ⟨v⟩ := ‹Nonempty (Fin m)›
    have hh := G.degree_lt_card_verts v
    rw [S.seed.regular v] at hh
    simpa using hh
  · exact hp
  · exact hqo
  · exact hl
  · simpa using hu

theorem ColouredSeed.closed_interval [Nonempty (Fin m)] (S : ColouredSeed G n d true)
    (hd : 4 ≤ d) (hp : Even d) (q : ℕ) (hqe : Even q) (hl : d ≤ q)
    (hu : q ≤ 4*m-4-d) : ClosedExists (n+2) q := by
  obtain ⟨hc,l,hm⟩ := S.seed.magic
  obtain ⟨c,hB,_,_,hmagic⟩ := chosen_lift_closed S hd hp
  let T := affineTransport G (chosenSlopes G S.colouring) c
  apply T.closed_interval_exists S.seed.factorCycle.factors S.seed.factorCycle.complementFactors
    l hc hmagic.1
  · rintro ⟨v,x⟩
    rw [EdgeTransport.sum_label, affine_neighbor_sum]
    have hz : incidenceB G (chosenSlopes G S.colouring) c v = 0 := congrFun hB v
    rw [hz,add_zero]
    change bitsFourEquiv n (l v,x) + bitsFourEquiv n _ = 0
    rw [← bitsFourEquiv_add]
    change bitsFourEquiv n (l v + ∑ u ∈ G.neighborFinset v, l u,
      x + ∑ u ∈ G.neighborFinset v, scalar (outgoingSlope G (chosenSlopes G S.colouring) v u) x) = 0
    rw [hm, chosen_closed_scalar S.colouring hp]
    exact (bitsFourAddHom n).map_zero
  · omega
  · obtain ⟨v⟩ := ‹Nonempty (Fin m)›
    have hh := G.degree_lt_card_verts v
    rw [S.seed.regular v] at hh
    simpa using hh
  · exact hp
  · exact hqe
  · exact hl
  · simpa using hu
end XorMagic
