import CMDRRWeightedOccurrences
open scoped Classical BigOperators
namespace CMDRR
namespace Game
variable {M W : Type}
theorem women_display (g : Game M W) {a b : M × W} (he : g.teams = {a,b})
    (hab : a ≠ b) (w v : W) :
    g.Women w v ↔ (w = a.2 ∧ v = b.2) ∨ (w = b.2 ∧ v = a.2) := by
  classical
  simp only [Women,he,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨x,hx,y,hy,hxw,hyv,hxy⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact Or.inl ⟨hxw.symm,hyv.symm⟩
    · exact Or.inr ⟨hxw.symm,hyv.symm⟩
    · exact (hxy rfl).elim
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨a,Or.inl rfl,b,Or.inr rfl,rfl,rfl,hab⟩
    · exact ⟨b,Or.inr rfl,a,Or.inl rfl,rfl,rfl,hab.symm⟩

theorem all_display (g : Game M W) {a b : M × W} (he : g.teams = {a,b})
    (P : W → Prop) : (∀ t ∈ g.teams, P t.2) ↔ P a.2 ∧ P b.2 := by
  classical
  simp only [he,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl),h b (Or.inr rfl)⟩
  · rintro ⟨ha,hb⟩ t (rfl | rfl) <;> assumption

theorem all_singles (g : Game (Fin 5) (Fin 5)) :
    (∀ t ∈ g.teams, 3 ≤ t.2.val) ↔ g.Women 3 4 := by
  obtain ⟨a,b,_,hw,he⟩ := g.display
  have hab : a ≠ b := fun e => hw (congrArg Prod.snd e)
  rw [g.all_display he (fun w : Fin 5 => 3 ≤ w.val),g.women_display he hab]
  constructor
  · rintro ⟨ha,hb⟩
    have ha5 := a.2.isLt
    have hb5 := b.2.isLt
    have hne : a.2.val ≠ b.2.val := fun e => hw (Fin.ext e)
    have hv : (a.2.val = 3 ∧ b.2.val = 4) ∨ (a.2.val = 4 ∧ b.2.val = 3) := by omega
    rcases hv with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨(Fin.ext ha).symm,(Fin.ext hb).symm⟩
    · exact Or.inr ⟨(Fin.ext hb).symm,(Fin.ext ha).symm⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩) <;> simp [← ha,← hb]

theorem all_married (g : Game (Fin 5) (Fin 5)) :
    (∀ t ∈ g.teams, t.2.val < 3) ↔
      ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ g.Women w v := by
  obtain ⟨a,b,_,hw,he⟩ := g.display
  have hab : a ≠ b := fun e => hw (congrArg Prod.snd e)
  rw [g.all_display he (fun w : Fin 5 => w.val < 3)]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨a.2,b.2,ha,hb,(g.women_display he hab _ _).mpr (Or.inl ⟨rfl,rfl⟩)⟩
  · rintro ⟨w,v,hw,hv,hp⟩
    rcases (g.women_display he hab w v).mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hw,hv⟩
    · exact ⟨hv,hw⟩

/-- The three unordered pairs in the three married female labels form a
disjoint occurrence partition, not an enumeration of schedules. -/
theorem married_pair_indicator (g : Game (Fin 5) (Fin 5)) :
    (if ∀ t ∈ g.teams, t.2.val < 3 then 1 else 0) =
      (if g.Women 0 1 then 1 else 0) + (if g.Women 0 2 then 1 else 0) +
      (if g.Women 1 2 then 1 else 0) := by
  classical
  obtain ⟨a,b,_,hw,he⟩ := g.display
  have hab : a ≠ b := fun e => hw (congrArg Prod.snd e)
  simp only [g.all_display he (fun w : Fin 5 => w.val < 3)]
  simp only [g.women_display he hab,Fin.ext_iff]
  have ha5 := a.2.isLt
  have hb5 := b.2.isLt
  have hne : a.2.val ≠ b.2.val := fun e => hw (Fin.ext e)
  split_ifs <;> simp_all <;> omega
end Game

namespace Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)

include h in
theorem no_two_married_men_for_married_women (o : O)
    (hw : ∀ t ∈ (d.game o).teams, t.2.val < 3) :
    ¬ ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ (d.game o).Men m n := by
  obtain ⟨a,b,hm,hf,he⟩ := (d.game o).display
  have hab : a ≠ b := fun e => hm (congrArg Prod.fst e)
  have ha : a ∈ (d.game o).teams := by simp [he]
  have hb : b ∈ (d.game o).teams := by simp [he]
  have hwa := hw a ha
  have hwb := hw b hb
  have avoid : ∀ x ∈ (d.game o).teams, ∀ y ∈ (d.game o).teams,
      x.1.val < 3 → x.1 ≠ y.2 := by
    intro x hx y hy hlt heq
    exact h.1 x.1 y.2 ⟨heq,hlt⟩ o ⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩
  rintro ⟨m,n,hmc,hnc,hmn⟩
  rcases ((d.game o).men_display he hab m n).mp hmn with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    have hmaa : a.1 ≠ a.2 := avoid a ha a ha (by assumption) <;>
    have hmab : a.1 ≠ b.2 := avoid a ha b hb (by assumption) <;>
    have hmba : b.1 ≠ a.2 := avoid b hb a ha (by assumption) <;>
    have hmbb : b.1 ≠ b.2 := avoid b hb b hb (by assumption) <;>
    have h1 : a.1.val ≠ a.2.val := fun e => hmaa (Fin.ext e) <;>
    have h2 : a.1.val ≠ b.2.val := fun e => hmab (Fin.ext e) <;>
    have h3 : b.1.val ≠ a.2.val := fun e => hmba (Fin.ext e) <;>
    have h4 : b.1.val ≠ b.2.val := fun e => hmbb (Fin.ext e) <;>
    have h5 : a.1.val ≠ b.1.val := fun e => hm (Fin.ext e) <;>
    have h6 : a.2.val ≠ b.2.val := fun e => hf (Fin.ext e) <;> omega

include h in
theorem married_women_games_three :
    count (fun o => ∀ t ∈ (d.game o).teams, t.2.val < 3) = 3 := by
  classical
  have h01 : count (fun o => (d.game o).Women 0 1) = 1 :=
    h.2.2.2.1 0 ⟨0,⟨rfl,by decide⟩⟩ 1 (by decide)
  have h02 : count (fun o => (d.game o).Women 0 2) = 1 :=
    h.2.2.2.1 0 ⟨0,⟨rfl,by decide⟩⟩ 2 (by decide)
  have h12 : count (fun o => (d.game o).Women 1 2) = 1 :=
    h.2.2.2.1 1 ⟨1,⟨rfl,by decide⟩⟩ 2 (by decide)
  simp only [count_as_sum] at *
  calc
    _ = ∑ o : O, ((if (d.game o).Women 0 1 then 1 else 0) +
        (if (d.game o).Women 0 2 then 1 else 0) +
        (if (d.game o).Women 1 2 then 1 else 0)) :=
      Finset.sum_congr rfl (fun o _ => (d.game o).married_pair_indicator)
    _ = 3 := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,h01,h02,h12]

include h in
theorem married_women_weighted :
    (∑ o : O, if ∀ t ∈ (d.game o).teams, t.2.val < 3 then
      count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, (d.game o).Partners m w) else 0) +
      B d = 3 := by
  classical
  have he : ∀ o : O,
      (if ∀ t ∈ (d.game o).teams, t.2.val < 3 then
        count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, (d.game o).Partners m w) else 0) +
      (if (d.game o).Men 3 4 ∧
        ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v then 1 else 0) =
      (if ∀ t ∈ (d.game o).teams, t.2.val < 3 then 1 else 0) := by
    intro o
    by_cases hw : ∀ t ∈ (d.game o).teams, t.2.val < 3
    · have hh := h.no_two_married_men_for_married_women o hw
      have hm := (d.game o).spouse_man_incidence
      have hwp := ((d.game o).all_married).mp hw
      split_ifs <;> simp_all
    · have hh : ¬ ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v :=
        fun hp => hw ((d.game o).all_married.mpr hp)
      have hn : ¬ ((d.game o).Men 3 4 ∧
          ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v) :=
        fun hp => hh hp.2
      simp only [ite_eq_right hw,ite_eq_right hn,Nat.zero_add]
  have hs := congrArg (fun f : O → ℕ => ∑ o, f o) (funext he)
  simp only [Finset.sum_add_distrib] at hs
  have hb := count_as_sum (fun o => (d.game o).Men 3 4 ∧
    ∃ w v : Fin 5, w.val < 3 ∧ v.val < 3 ∧ (d.game o).Women w v)
  have hw := count_as_sum (fun o => ∀ t ∈ (d.game o).teams, t.2.val < 3)
  change B d = _ at hb
  rw [← hb,← hw,h.married_women_games_three] at hs
  exact hs
end Source
end CMDRR
