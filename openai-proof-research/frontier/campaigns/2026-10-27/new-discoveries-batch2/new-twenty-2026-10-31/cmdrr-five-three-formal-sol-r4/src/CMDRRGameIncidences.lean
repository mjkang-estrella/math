import CMDRRRowOccurrences

open scoped Classical
namespace CMDRR
namespace Game
variable {M W : Type}
theorem partners_display (g : Game M W) {a b : M × W} (he : g.teams = {a,b})
    (m : M) : (∃ w, g.Partners m w) ↔ m = a.1 ∨ m = b.1 := by
  classical
  simp only [Partners,he,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨w,h | h⟩
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
  · rintro (h | h)
    · exact ⟨a.2,Or.inl (Prod.ext h rfl)⟩
    · exact ⟨b.2,Or.inr (Prod.ext h rfl)⟩

theorem men_display (g : Game M W) {a b : M × W} (he : g.teams = {a,b})
    (hab : a ≠ b) (m n : M) :
    g.Men m n ↔ (m = a.1 ∧ n = b.1) ∨ (m = b.1 ∧ n = a.1) := by
  classical
  simp only [Men,he,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨x,hx,y,hy,hxm,hyn,hxy⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact Or.inl ⟨hxm.symm,hyn.symm⟩
    · exact Or.inr ⟨hxm.symm,hyn.symm⟩
    · exact (hxy rfl).elim
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨a,Or.inl rfl,b,Or.inr rfl,rfl,rfl,hab⟩
    · exact ⟨b,Or.inr rfl,a,Or.inl rfl,rfl,rfl,hab.symm⟩

theorem spouse_man_incidence (g : Game (Fin 5) (Fin 5)) :
    count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, g.Partners m w) +
      (if g.Men 3 4 then 1 else 0) =
    1 + (if ∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ g.Men m n then 1 else 0) := by
  classical
  obtain ⟨a,b,hm,_,he⟩ := g.display
  have hab : a ≠ b := fun e => hm (congrArg Prod.fst e)
  have hp := g.partners_display he
  have hcount : count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, g.Partners m w) =
      (if a.1.val < 3 then 1 else 0) + (if b.1.val < 3 then 1 else 0) := by
    have hc : count (fun m : Fin 5 => m.val < 3 ∧ ∃ w, g.Partners m w) =
        (({a.1,b.1} : Finset (Fin 5)).filter (fun m => m.val < 3)).card := by
      unfold count
      congr 1
      ext m
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hp,
        Finset.mem_insert,Finset.mem_singleton]
      tauto
    rw [hc]
    simp only [Finset.filter_insert, Finset.filter_singleton]
    split_ifs <;> simp_all
  have hh : (∃ m n : Fin 5, m.val < 3 ∧ n.val < 3 ∧ g.Men m n) ↔
      a.1.val < 3 ∧ b.1.val < 3 := by
    simp only [g.men_display he hab]
    constructor
    · rintro ⟨m,n,hm,hn,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
      · exact ⟨hm,hn⟩
      · exact ⟨hn,hm⟩
    · rintro ⟨ha,hb⟩
      exact ⟨a.1,b.1,ha,hb,Or.inl ⟨rfl,rfl⟩⟩
  have hz : g.Men 3 4 ↔ ¬ a.1.val < 3 ∧ ¬ b.1.val < 3 := by
    rw [g.men_display he hab]
    constructor
    · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩) <;> simp [← ha,← hb]
    · rintro ⟨ha,hb⟩
      have ha5 := a.1.isLt
      have hb5 := b.1.isLt
      have hne : a.1.val ≠ b.1.val := fun h => hm (Fin.ext h)
      have hv : (a.1.val = 3 ∧ b.1.val = 4) ∨ (a.1.val = 4 ∧ b.1.val = 3) := by omega
      rcases hv with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl ⟨(Fin.ext ha).symm,(Fin.ext hb).symm⟩
      · exact Or.inr ⟨(Fin.ext hb).symm,(Fin.ext ha).symm⟩
  rw [hcount]
  simp only [hh,hz]
  by_cases ha : a.1.val < 3 <;> by_cases hb : b.1.val < 3 <;> simp [ha,hb]
end Game
end CMDRR
