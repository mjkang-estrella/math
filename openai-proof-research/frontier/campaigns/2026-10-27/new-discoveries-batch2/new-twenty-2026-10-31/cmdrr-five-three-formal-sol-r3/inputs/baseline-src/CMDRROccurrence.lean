import CMDRRBase

open scoped Classical

namespace CMDRR
variable {M W O : Type}

 theorem count_eq_one_iff [Fintype O] (p : O → Prop) :
    count p = 1 ↔ ∃! o, p o := by
  classical
  simp only [count, Finset.card_eq_one_iff_existsUnique, Finset.mem_filter,
    Finset.mem_univ, true_and]

 theorem count_congr [Fintype O] {p q : O → Prop} (h : ∀ o, p o ↔ q o) :
    count p = count q := by
  classical
  unfold count
  congr 1
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]

namespace Game
 theorem ext_teams {g h : Game M W} (e : g.teams = h.teams) : g = h := by
  cases g
  cases h
  cases e
  rfl

/-- Every unordered game has an ordered display; its only data are two
mixed teams with different men and different women. -/
 theorem display (g : Game M W) :
    ∃ a b : M × W, a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧ g.teams = {a,b} := by
  classical
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp g.two
  refine ⟨a,b,g.men_distinct a ?_ b ?_ hab,
    g.women_distinct a ?_ b ?_ hab,he⟩ <;> simp [he]

 theorem partner_shares (g : Game M W) {m w} (h : g.Partners m w) :
    g.Shares m w := ⟨⟨(m,w),h,rfl⟩,⟨(m,w),h,rfl⟩⟩

 theorem partner_unique_woman (g : Game M W) {m w v}
    (h : g.Partners m w) (k : g.Partners m v) : w = v := by
  by_contra hn
  exact g.men_distinct (m,w) h (m,v) k (by simpa) rfl

 theorem partner_unique_man (g : Game M W) {m n w}
    (h : g.Partners m w) (k : g.Partners n w) : m = n := by
  by_contra hn
  exact g.women_distinct (m,w) h (n,w) k (by simpa) rfl

 theorem opposite_unique (g : Game M W) {a : M × W} (ha : a ∈ g.teams) :
    ∃! b, b ∈ g.teams ∧ b ≠ a := by
  classical
  obtain ⟨x,y,_,_,he⟩ := g.display
  have hxy : x ≠ y := by intro h; subst y; simpa [he] using g.two
  rw [he] at ha ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
  rcases ha with rfl | rfl
  · refine ⟨y,⟨Or.inr rfl,Ne.symm hxy⟩,?_⟩
    intro b hb
    rcases hb.1 with rfl | rfl
    · exact (hb.2 rfl).elim
    · rfl
  · refine ⟨x,⟨Or.inl rfl,hxy⟩,?_⟩
    intro b hb
    rcases hb.1 with rfl | rfl
    · rfl
    · exact (hb.2 rfl).elim
end Game

namespace Source
variable [Fintype O] {s : Matching M W} {d : Schedule M W O}
 theorem allowed (h : Source s d) {o m w} (hp : (d.game o).Partners m w) :
    ¬ s.spouse m w := by
  intro hs
  exact h.1 m w hs o ((d.game o).partner_shares hp)

 theorem partnership_unique (h : Source s d) {m w} (ha : ¬ s.spouse m w) :
    ∃! o, (d.game o).Partners m w :=
  (count_eq_one_iff _).mp (h.2.1 m w ha).1

 theorem opposition_unique (h : Source s d) {m w} (ha : ¬ s.spouse m w) :
    ∃! o, (d.game o).Opposes m w :=
  (count_eq_one_iff _).mp (h.2.1 m w ha).2

 theorem occurrence_eq (h : Source s d) {o p : O} {m w}
    (ho : (d.game o).Partners m w) (hp : (d.game p).Partners m w) : o = p := by
  obtain ⟨t,_,ht⟩ := h.partnership_unique (h.allowed ho)
  exact (ht o ho).trans (ht p hp).symm

/-- Duplicate occurrences are impossible as a consequence, not a model field. -/
 theorem game_injective (h : Source s d) : Function.Injective d.game := by
  intro o p he
  obtain ⟨a,b,_,_,ha⟩ := (d.game o).display
  have hx : (d.game o).Partners a.1 a.2 := by
    cases a
    simp [Game.Partners,ha]
  exact h.occurrence_eq hx (he ▸ hx)
end Source
end CMDRR
