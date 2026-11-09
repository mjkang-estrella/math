import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option autoImplicit false

def Noncollinear5 (p q r : Points 5) : Prop :=
  ∀ l, ¬ (incidence p l = true ∧ incidence q l = true ∧ incidence r l = true)
instance (p q r : Points 5) : Decidable (Noncollinear5 p q r) :=
  inferInstanceAs (Decidable (∀ l, ¬ (incidence p l = true ∧ incidence q l = true ∧ incidence r l = true)))

theorem line_fixed5 (l p : Points 5) :
    step PG5 5 (fun x => incidence x l) p = incidence p l := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hp | ⟨k,_,hpk,hc⟩
    · exact hp
    · by_cases he : l = k
      · subst k; exact hpk
      · have hm := PG5.meet l k he
        change card (List.finRange 31) (fun x => incidence x l && incidence x k) = 1 at hm
        change 5 ≤ card (List.finRange 31) (fun x => incidence x l && incidence x k) at hc
        omega
  · intro hp
    simp only [step, Bool.or_eq_true]
    exact Or.inl hp

theorem join_unique5 (p q l k : Points 5) (hne : p ≠ q)
    (hpl : incidence p l = true) (hql : incidence q l = true)
    (hpk : incidence p k = true) (hqk : incidence q k = true) : l = k := by
  have h := PG5.join p q hne
  obtain ⟨x,hx⟩ := List.length_eq_one_iff.mp h
  change (List.finRange 31).filter (fun j => incidence p j && incidence q j) = [x] at hx
  have hl : l ∈ (List.finRange 31).filter (fun j => incidence p j && incidence q j) := by
    simp [hpl,hql]
  have hk : k ∈ (List.finRange 31).filter (fun j => incidence p j && incidence q j) := by
    simp [hpk,hqk]
  rw [hx] at hl hk
  exact (List.eq_of_mem_singleton hl).trans (List.eq_of_mem_singleton hk).symm

theorem line_nonfull5 : ∀ l : Points 5, ∃ p, incidence p l = false := by decide

theorem percolates_not_in_line5 (a : Infection 5) (h : Percolates PG5 5 a)
    (l : Points 5) : ∃ p, a p = true ∧ incidence p l = false := by
  classical
  apply Classical.byContradiction
  intro hn
  obtain ⟨p, hp⟩ := line_nonfull5 l
  apply separator_blocks PG5 5 a (fun x => incidence x l) ?_ ?_ p hp h
  · intro x hx
    have hh : ¬ (a x = true ∧ incidence x l = false) := fun h => hn ⟨x,h⟩
    cases hi : incidence x l <;> simp_all
  · funext x
    exact line_fixed5 l x

theorem point_on_line5 : ∀ p : Points 5, ∃ l, incidence p l = true := by decide

theorem pair_on_line5 : ∀ p q : Points 5, ∃ l,
    incidence p l = true ∧ incidence q l = true := by decide

theorem off_join_noncollinear5 (p q l r : Points 5)
    (hne : p ≠ q) (hp : incidence p l = true) (hq : incidence q l = true)
    (hr : incidence r l = false) : Noncollinear5 p q r := by
  intro k ⟨hpk,hqk,hrk⟩
  have he := join_unique5 p q l k hne hp hq hpk hqk
  subst k
  rw [hr] at hrk
  contradiction

theorem percolates_noncollinear5 (a : Infection 5) (h : Percolates PG5 5 a) :
    ∃ p q r, a p = true ∧ a q = true ∧ a r = true ∧ Noncollinear5 p q r := by
  obtain ⟨p, hp, _⟩ := percolates_not_in_line5 a h 0
  obtain ⟨l, hl⟩ := point_on_line5 p
  obtain ⟨q, hq, hql⟩ := percolates_not_in_line5 a h l
  have hne : p ≠ q := by intro he; subst q; rw [hl] at hql; contradiction
  obtain ⟨j, hpj, hqj⟩ := pair_on_line5 p q
  obtain ⟨r, hr, hrj⟩ := percolates_not_in_line5 a h j
  exact ⟨p,q,r,hp,hq,hr,off_join_noncollinear5 p q j r hne hpj hqj hrj⟩

theorem noncollinear_pull5 (e : Collineation5) (p q r : Points 5)
    (h : Noncollinear5 p q r) :
    Noncollinear5 (e.pinv p) (e.pinv q) (e.pinv r) := by
  intro l ⟨hp,hq,hr⟩
  apply h (e.l l)
  have hi (x : Points 5) : incidence x (e.l l) = incidence (e.pinv x) l := by
    have hh := e.incidence_preserved (e.pinv x) l
    rw [e.pp] at hh
    exact hh
  exact ⟨(hi p).trans hp,(hi q).trans hq,(hi r).trans hr⟩

theorem noncollinear_ne5 (p q r : Points 5) (h : Noncollinear5 p q r) : p ≠ q := by
  intro he
  subst q
  obtain ⟨l,hp,hr⟩ := pair_on_line5 p r
  exact h l ⟨hp,hp,hr⟩

theorem noncollinear_fixed5 (p : Points 5) (h : Noncollinear5 0 25 p) :
    incidence p 30 = false := by
  cases hi : incidence p 30
  · rfl
  · exact False.elim (h 30 ⟨by decide,by decide,hi⟩)
end Percolation
