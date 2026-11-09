import CMDRRCells

open scoped Classical
namespace CMDRR
variable {M W O : Type} [Fintype O]
namespace Source
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)

noncomputable def oppositionCell (x : Incidence d) : Cell s :=
  ⟨(x.2.1.1, ((d.game x.1).other x.2).1.2), by
    intro hs
    exact h.1 _ _ hs x.1
      ⟨⟨_,x.2.2,rfl⟩,⟨_,((d.game x.1).other x.2).2,rfl⟩⟩⟩

 theorem oppositionCell_bijective : Function.Bijective h.oppositionCell := by
  constructor
  · rintro ⟨o,a,ha⟩ ⟨p,b,hb⟩ he
    have hm := congrArg (fun c : Cell s => c.1.1) he
    have hw := congrArg (fun c : Cell s => c.1.2) he
    have hxo : (d.game o).Opposes a.1 ((d.game o).other ⟨a,ha⟩).1.2 :=
      ⟨a,ha,_,((d.game o).other ⟨a,ha⟩).2,rfl,rfl,
        fun heq => (d.game o).other_ne ⟨a,ha⟩ (Subtype.ext heq.symm)⟩
    have hxp : (d.game p).Opposes a.1 ((d.game o).other ⟨a,ha⟩).1.2 := by
      refine ⟨b,hb,_,((d.game p).other ⟨b,hb⟩).2,hm.symm,hw.symm,?_⟩
      exact fun heq => (d.game p).other_ne ⟨b,hb⟩ (Subtype.ext heq.symm)
    obtain ⟨t,_,ht⟩ := h.opposition_unique (h.oppositionCell ⟨o,⟨a,ha⟩⟩).2
    have hop := (ht o hxo).trans (ht p hxp).symm
    subst p
    have hab : a = b := by
      by_contra hn
      exact (d.game o).men_distinct a ha b hb hn hm
    subst b
    rfl
  · rintro ⟨⟨m,w⟩,ha⟩
    obtain ⟨o,⟨a,ha',b,hb,hm,hw,hab⟩,_⟩ := h.opposition_unique ha
    have hb' : (d.game o).other ⟨a,ha'⟩ = ⟨b,hb⟩ := by
      apply Subtype.ext
      symm
      exact (Game.opposite_unique _ ha').choose_spec.2 b ⟨hb,Ne.symm hab⟩
    refine ⟨⟨o,⟨a,ha'⟩⟩,?_⟩
    apply Subtype.ext
    change (a.1,((d.game o).other ⟨a,ha'⟩).1.2) = (m,w)
    rw [hb']
    exact Prod.ext hm hw

noncomputable def oppositionEquiv : Incidence d ≃ Cell s :=
  Equiv.ofBijective h.oppositionCell h.oppositionCell_bijective

/-- Genuine row permutation; partner-to-opposing-woman. -/
noncomputable def U : Equiv.Perm (Cell s) :=
  h.cellsEquiv.symm.trans h.oppositionEquiv

/-- Genuine column permutation; partner-to-opposing-man. -/
noncomputable def C : Equiv.Perm (Cell s) := h.T.trans h.U

 theorem C_T (x : Cell s) : h.C (h.T x) = h.U x := by
  change h.U (h.T (h.T x)) = h.U x
  rw [h.T_involutive x]

 theorem U_incidence (x : Incidence d) :
    h.U (h.cellsEquiv x) = h.oppositionCell x := by
  change h.oppositionEquiv (h.cellsEquiv.symm (h.cellsEquiv x)) = _
  rw [Equiv.symm_apply_apply]
  rfl

 theorem U_first (x : Cell s) : (h.U x).1.1 = x.1.1 := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  rw [h.U_incidence]
  rfl

 theorem U_second_ne (x : Cell s) : (h.U x).1.2 ≠ x.1.2 := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  rw [h.U_incidence]
  exact (d.game a.1).other_female_ne a.2

 theorem T_incidence (x : Incidence d) :
    h.T (h.cellsEquiv x) = h.cellsEquiv (d.exchange x) := by
  change h.cellsEquiv (d.exchange (h.cellsEquiv.symm (h.cellsEquiv x))) = _
  rw [Equiv.symm_apply_apply]

 theorem C_incidence (x : Incidence d) :
    (h.C (h.cellsEquiv x)).1 = (((d.game x.1).other x.2).1.1,x.2.1.2) := by
  change (h.U (h.T (h.cellsEquiv x))).1 = _
  rw [h.T_incidence, h.U_incidence]
  change (((d.game x.1).other x.2).1.1,
    ((d.game x.1).other ((d.game x.1).other x.2)).1.2) = _
  rw [Game.other_other]

 theorem C_second (x : Cell s) : (h.C x).1.2 = x.1.2 := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  have he := congrArg Prod.snd (h.C_incidence a)
  exact he

 theorem C_first_ne (x : Cell s) : (h.C x).1.1 ≠ x.1.1 := by
  obtain ⟨a,rfl⟩ := h.cellsEquiv.surjective x
  have he := congrArg Prod.fst (h.C_incidence a)
  rw [he]
  exact (d.game a.1).other_male_ne a.2
end Source
end CMDRR
