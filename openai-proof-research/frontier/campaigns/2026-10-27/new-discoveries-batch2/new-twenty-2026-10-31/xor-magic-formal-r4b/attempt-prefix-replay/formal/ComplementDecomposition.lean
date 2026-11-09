import ComplementCharts
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {d c : ℕ}
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d)
  (H : MatchingDecomposition Gᶜ c)
abbrev ComplementIndex (d c : ℕ) := NonzeroFour ⊕ ((Fin d × NonzeroFour) ⊕ (Fin c × Four))
def complementMate : ComplementIndex d c → (V × Four) → (V × Four)
  | .inl a => fibreMatching V a
  | .inr (.inl ia) => blockMate F (T.matchingChart F) ia.1 ia.2.1
  | .inr (.inr ia) => blockMate H (fun _ _ => Equiv.refl _) ia.1 ia.2

theorem complementMate_involutive (i : ComplementIndex d c) :
    Function.Involutive (T.complementMate F H i) := by
  rcases i with a | (ia | ia)
  · exact fibreMatching_involutive V a
  · exact blockMate_involutive F _ _ _
  · exact blockMate_involutive H _ _ _
theorem complementMate_no_fixed (i : ComplementIndex d c) (p : V × Four) :
    T.complementMate F H i p ≠ p := by
  rcases i with a | (ia | ia)
  · exact fibreMatching_no_fixed V a p
  · exact blockMate_no_fixed F _ _ _ p
  · exact blockMate_no_fixed H (fun _ _ => Equiv.refl _) ia.1 ia.2 p

theorem complementMate_cover (p q : V × Four) :
    T.graphᶜ.Adj p q ↔ ∃ i, T.complementMate F H i p = q := by
  change (p ≠ q ∧ ¬ (G.Adj p.1 q.1 ∧ T.map p.1 q.1 p.2 = q.2)) ↔ _
  constructor
  · rintro ⟨hne,hn⟩
    by_cases hv : p.1 = q.1
    · have hx : p.2 ≠ q.2 := fun hx => hne (Prod.ext hv hx)
      obtain ⟨a,ha⟩ := fibreMatching_cover p q |>.mp ⟨hv,hx⟩
      exact ⟨.inl a,ha⟩
    · by_cases ha : G.Adj p.1 q.1
      · obtain ⟨ia,hi⟩ := (T.blockMate_nonzero_cover F p q).mp ⟨ha,fun he => hn ⟨ha,he⟩⟩
        exact ⟨.inr (.inl ia),hi⟩
      · obtain ⟨i,hi⟩ := (H.cover _ _).mp ⟨hv,ha⟩
        exact ⟨.inr (.inr (i,q.2-p.2)), Prod.ext hi (by simp [complementMate,blockMate])⟩
  · rintro ⟨i,he⟩
    refine ⟨fun hh => T.complementMate_no_fixed F H i p (he.trans hh.symm), ?_⟩
    rcases i with a | (ia | ia)
    · have hv : p.1 = q.1 := by simpa [complementMate,fibreMatching] using congrArg Prod.fst he
      intro ha
      exact G.irrefl (hv ▸ ha.1)
    · exact fun ha => ((T.blockMate_nonzero_cover F p q).mpr ⟨ia,he⟩).2 ha.2
    · have hv : H.mate ia.1 p.1 = q.1 := congrArg Prod.fst he
      exact fun ha => ((H.cover _ _).mpr ⟨ia.1,hv⟩).2 ha.1

theorem complementMate_distinct (p : V × Four) :
    Function.Injective (fun i => T.complementMate F H i p) := by
  intro i j he
  rcases i with a | (ia | ia) <;> rcases j with b | (jb | jb)
  · exact congrArg Sum.inl (fibreMatching_distinct V p he)
  · exact False.elim (F.no_fixed jb.1 p.1 (congrArg Prod.fst he.symm))
  · exact False.elim (H.no_fixed jb.1 p.1 (congrArg Prod.fst he.symm))
  · exact False.elim (F.no_fixed ia.1 p.1 (congrArg Prod.fst he))
  · have h : (ia.1,ia.2.1) = (jb.1,jb.2.1) :=
      blockMate_distinct F (T.matchingChart F) p (by exact he)
    have hi := congrArg Prod.fst h
    have ha := congrArg Prod.snd h
    exact congrArg (fun z => Sum.inr (Sum.inl z)) (Prod.ext hi (Subtype.ext ha))
  · have hv : F.mate ia.1 p.1 = H.mate jb.1 p.1 := congrArg Prod.fst he
    have hg := (F.cover p.1 _).mpr ⟨ia.1,rfl⟩
    have hh := (H.cover p.1 _).mpr ⟨jb.1,rfl⟩
    exact False.elim (hh.2 (hv ▸ hg))
  · exact False.elim (H.no_fixed ia.1 p.1 (congrArg Prod.fst he))
  · have hv : H.mate ia.1 p.1 = F.mate jb.1 p.1 := congrArg Prod.fst he
    have hg := (F.cover p.1 _).mpr ⟨jb.1,rfl⟩
    have hh := (H.cover p.1 _).mpr ⟨ia.1,rfl⟩
    exact False.elim (hh.2 (hv.symm ▸ hg))
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (blockMate_distinct H (fun _ _ => Equiv.refl _) p (by exact he))

theorem complementIndex_card : Fintype.card (ComplementIndex d c) = 3+3*d+4*c := by
  simp [ComplementIndex, Fintype.card_sum, Fintype.card_prod,
    show Fintype.card Four = 4 by decide]
  omega

/-- All three disjoint block families, reindexed by Fin, in the inherited convention. -/
noncomputable def complementMatching : MatchingDecomposition T.graphᶜ (3+3*d+4*c) := by
  let e : ComplementIndex d c ≃ Fin (3+3*d+4*c) :=
    (Fintype.equivFin _).trans (finCongr complementIndex_card)
  exact {
    mate := fun i => T.complementMate F H (e.symm i)
    involutive := fun i => T.complementMate_involutive F H (e.symm i)
    no_fixed := fun i => T.complementMate_no_fixed F H (e.symm i)
    distinct := fun p => (T.complementMate_distinct F H p).comp e.symm.injective
    cover := fun p q => (T.complementMate_cover F H p q).trans (by
      constructor
      · rintro ⟨i,hi⟩; exact ⟨e i,by simpa using hi⟩
      · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩) }
end EdgeTransport
end XorMagic
