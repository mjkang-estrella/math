import MiddleWitness
namespace R139.MiddleOCD

def IsOuterConnected (G : SimpleGraph W) (S : Finset W) : Prop :=
  (G.induce ((S : Set W)ᶜ)).Preconnected

def IsOuterConnected' (G : SimpleGraph W) (S : Finset W) : Prop :=
  (G.induce ((S : Set W)ᶜ)).Connected

theorem g8_value :
    IsLeast {k | ∃ S : Finset (Fin 8), S.card = k ∧ IsDominating G8 S ∧
      IsOuterConnected G8 S} 4 := by
  refine ⟨⟨S0, by decide, S0_dom, S0_conn.preconnected⟩, ?_⟩
  rintro k ⟨S, rfl, hd, hc⟩
  exact ocd_G8_lower S ⟨hd, hc⟩

theorem g8_value' :
    IsLeast {k | ∃ S : Finset (Fin 8), S.card = k ∧ IsDominating G8 S ∧
      IsOuterConnected' G8 S} 4 := by
  refine ⟨⟨S0, by decide, S0_dom, S0_conn⟩, ?_⟩
  rintro k ⟨S, rfl, hd, hc⟩
  exact ocd'_G8_lower S ⟨hd, hc⟩

theorem middle_g8_value :
    IsLeast {k | ∃ S : Finset (Fin 8 ⊕ G8.edgeSet), S.card = k ∧
      IsDominating (middle G8) S ∧ IsOuterConnected (middle G8) S} 4 := by
  refine ⟨⟨D8, D8_card, D8_dom, M8_conn.preconnected⟩, ?_⟩
  rintro k ⟨S, rfl, hd, _⟩
  exact ocd_M8_lower S hd

theorem middle_g8_value' :
    IsLeast {k | ∃ S : Finset (Fin 8 ⊕ G8.edgeSet), S.card = k ∧
      IsDominating (middle G8) S ∧ IsOuterConnected' (middle G8) S} 4 := by
  refine ⟨⟨D8, D8_card, D8_dom, M8_conn⟩, ?_⟩
  rintro k ⟨S, rfl, hd, _⟩
  exact ocd_M8_lower S hd

theorem mathdb_355217_connected :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      2 ≤ Fintype.card V → ocd G < ocd (middle G)) := by
  intro h
  have h8 := h (Fin 8) G8 G8_connected (by decide)
  rw [ocd_G8, ocd_M8] at h8
  exact Nat.lt_irrefl 4 h8

theorem mathdb_355217_connected' :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      2 ≤ Fintype.card V → ocd' G < ocd' (middle G)) := by
  intro h
  have h8 := h (Fin 8) G8 G8_connected (by decide)
  rw [ocd'_G8, ocd'_M8] at h8
  exact Nat.lt_irrefl 4 h8

/-- Uncredited domain control: at an edgeless graph, domination forces the full set. -/
theorem isolated_dom [Fintype W] (G : SimpleGraph W)
    (hn : ∀ a b, ¬ G.Adj a b) (S : Finset W) (hd : IsDominating G S) :
    ∀ v, v ∈ S := by
  intro v
  rcases hd v with hv | ⟨w, _, hw⟩
  · exact hv
  · exact False.elim (hn v w hw)

/-- Under convention B the edgeless graph on two vertices has no feasible set. -/
theorem edgeless_two_no_ocd' : ¬ ∃ S : Finset (Fin 2), IsOCD' (⊥ : SimpleGraph (Fin 2)) S := by
  rintro ⟨S, hd, hc⟩
  obtain ⟨v, hv⟩ := hc.nonempty
  exact hv (isolated_dom _ (by simp) S hd v)

/-- Under convention A its minimum is 2. This is uncredited. -/
theorem edgeless_two_value :
    IsLeast {k | ∃ S : Finset (Fin 2), IsOCD (⊥ : SimpleGraph (Fin 2)) S ∧ S.card = k} 2 := by
  refine ⟨⟨Finset.univ, ⟨?_, ?_⟩, by decide⟩, ?_⟩
  · intro v; exact Or.inl (Finset.mem_univ v)
  · intro a; exact False.elim (a.property (Finset.mem_univ a.val))
  · rintro k ⟨S, hd, rfl⟩
    have hs : S = Finset.univ := Finset.eq_univ_iff_forall.mpr (isolated_dom _ (by simp) S hd.1)
    simp [hs]

theorem edgeless_numbers [Fintype W] [Nonempty W] (G : SimpleGraph W)
    (hn : ∀ a b, ¬ G.Adj a b) :
    ocd G = Fintype.card W ∧ ocd' G = 0 := by
  classical
  have hall : IsOCD G Finset.univ := by
    refine ⟨fun v => Or.inl (Finset.mem_univ v), ?_⟩
    intro a
    exact False.elim (a.property (Finset.mem_univ a.val))
  have hcard : ∀ S : Finset W, IsDominating G S → S.card = Fintype.card W := by
    intro S hd
    have hs := Finset.eq_univ_iff_forall.mpr (isolated_dom G hn S hd)
    simp [hs]
  constructor
  · apply le_antisymm
    · exact Nat.sInf_le ⟨Finset.univ, hall, Finset.card_univ⟩
    · change Fintype.card W ≤ sInf {k | ∃ S : Finset W, IsOCD G S ∧ S.card = k}
      apply le_csInf (show Set.Nonempty {k | ∃ S : Finset W, IsOCD G S ∧ S.card = k} from ⟨Fintype.card W, Finset.univ, hall, Finset.card_univ⟩)
      rintro k ⟨S, hd, rfl⟩
      exact (hcard S hd.1).ge
  · have he : {k | ∃ S : Finset W, IsOCD' G S ∧ S.card = k} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro k ⟨S, ⟨hd, hc⟩, _⟩
      obtain ⟨v, hv⟩ := hc.nonempty
      exact hv (isolated_dom G hn S hd v)
    simp [ocd', he]

/-- Uncredited literal-domain control, with the minimum convention B undefined:
its totalized sInf value is 0 on both sides. -/
theorem edgeless_two_literal_failure :
    ¬ ocd (⊥ : SimpleGraph (Fin 2)) < ocd (middle (⊥ : SimpleGraph (Fin 2))) ∧
    ¬ ocd' (⊥ : SimpleGraph (Fin 2)) < ocd' (middle (⊥ : SimpleGraph (Fin 2))) := by
  classical
  let G : SimpleGraph (Fin 2) := ⊥
  have : IsEmpty G.edgeSet := ⟨fun e => by simpa [G] using e.property⟩
  have hm : ∀ a b, ¬ (middle G).Adj a b := by
    rintro (a | e) (b | f)
    · exact id
    · exact isEmptyElim f
    · exact isEmptyElim e
    · exact isEmptyElim e
  obtain ⟨hA, hB⟩ := edgeless_numbers G (by simp [G])
  obtain ⟨hmA, hmB⟩ := edgeless_numbers (middle G) hm
  change ¬ ocd G < ocd (middle G) ∧ ¬ ocd' G < ocd' (middle G)
  rw [hA, hB, hmA, hmB]
  simp
end R139.MiddleOCD
