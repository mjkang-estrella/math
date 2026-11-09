import CMDRRSingleElimination
open scoped Classical
namespace CMDRR

/-- On five points, a derangement without two-cycles is one five-cycle.
The proof uses cardinal complements and injectivity, not permutations enumeration. -/
theorem orbit_five_of_no_two {α : Type} [Fintype α]
    (p : Equiv.Perm α) (hc : Fintype.card α = 5)
    (hd : ∀ y, p y ≠ y) (h2 : ∀ y, p (p y) ≠ y) (x : α) :
    p (p (p (p (p x)))) = x ∧
    x ≠ p x ∧ x ≠ p (p x) ∧ x ≠ p (p (p x)) ∧ x ≠ p (p (p (p x))) ∧
    p x ≠ p (p x) ∧ p x ≠ p (p (p x)) ∧ p x ≠ p (p (p (p x))) ∧
    p (p x) ≠ p (p (p x)) ∧ p (p x) ≠ p (p (p (p x))) ∧
    p (p (p x)) ≠ p (p (p (p x))) ∧
    ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = p (p (p x)) ∨ y = p (p (p (p x))) := by
  classical
  have h01 : x ≠ p x := (hd x).symm
  have h02 : x ≠ p (p x) := (h2 x).symm
  have h12 : p x ≠ p (p x) := fun e => h01 (p.injective e)
  have h03 : x ≠ p (p (p x)) := by
    intro h3
    let S : Finset α := {x,p x,p (p x)}
    have hs : S.card = 3 := by simp [S,h01,h02,h12]
    have hcompl : Sᶜ.card = 2 := by rw [Finset.card_compl,hs,hc]
    obtain ⟨c,d,hcd,he⟩ := Finset.card_eq_two.mp hcompl
    have cnot : c ∉ S := by
      have hh : c ∈ Sᶜ := by rw [he]; simp
      simpa using hh
    have dnot : d ∉ S := by
      have hh : d ∈ Sᶜ := by rw [he]; simp
      simpa using hh
    have closed : ∀ a, a ∉ S → p a ∉ S := by
      intro a ha hh
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · have heq : a = p (p x) := p.injective (hh.trans h3)
        exact ha (by simp [S,heq])
      · have heq : a = x := p.injective hh
        exact ha (by simp [S,heq])
      · have heq : a = p x := p.injective hh
        exact ha (by simp [S,heq])
    have pcd : p c = d := by
      have hh : p c ∈ Sᶜ := by simpa using closed c cnot
      rw [he] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      exact hh.resolve_left (hd c)
    have pdc : p d = c := by
      have hh : p d ∈ Sᶜ := by simpa using closed d dnot
      rw [he] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      exact hh.resolve_right (hd d)
    exact h2 c (by rw [pcd,pdc])
  have h13 : p x ≠ p (p (p x)) := fun e => h02 (p.injective e)
  have h23 : p (p x) ≠ p (p (p x)) := fun e => h12 (p.injective e)
  let S : Finset α := {x,p x,p (p x),p (p (p x))}
  have hs : S.card = 4 := by simp [S,h01,h02,h03,h12,h13,h23]
  have hcompl : Sᶜ.card = 1 := by rw [Finset.card_compl,hs,hc]
  obtain ⟨c,he⟩ := Finset.card_eq_one.mp hcompl
  have cnot : c ∉ S := by
    have hh : c ∈ Sᶜ := by rw [he]; simp
    simpa using hh
  have hc0 : c ≠ x := by intro e; exact cnot (by simp [S,e])
  have hc1 : c ≠ p x := by intro e; exact cnot (by simp [S,e])
  have hc2 : c ≠ p (p x) := by intro e; exact cnot (by simp [S,e])
  have hc3 : c ≠ p (p (p x)) := by intro e; exact cnot (by simp [S,e])
  have cover : ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = p (p (p x)) ∨ y = c := by
    intro y
    by_cases hy : y ∈ S
    · simp only [S,Finset.mem_insert,Finset.mem_singleton] at hy
      tauto
    · have hh : y ∈ Sᶜ := by simpa using hy
      rw [he] at hh
      exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hh))))
  have p4c : p (p (p (p x))) = c := by
    have hh := cover (p (p (p (p x))))
    rcases hh with hh | hh | hh | hh | hh
    · have pc : p c = c := by
        rcases cover (p c) with hp | hp | hp | hp | hp
        · exact (hc3 (p.injective (hp.trans hh.symm))).elim
        · exact (hc0 (p.injective hp)).elim
        · exact (hc1 (p.injective hp)).elim
        · exact (hc2 (p.injective hp)).elim
        · exact hp
      exact (hd c pc).elim
    · exact (h03 (p.injective hh).symm).elim
    · exact (h13 (p.injective hh).symm).elim
    · exact (h23 (p.injective hh).symm).elim
    · exact hh
  have pcx : p c = x := by
    rcases cover (p c) with hp | hp | hp | hp | hp
    · exact hp
    · exact (hc0 (p.injective hp)).elim
    · exact (hc1 (p.injective hp)).elim
    · exact (hc2 (p.injective hp)).elim
    · exact (hd c hp).elim
  refine ⟨by rw [p4c,pcx],h01,h02,h03,?_,h12,h13,?_,h23,?_,?_,?_⟩
  · rw [p4c]; exact hc0.symm
  · rw [p4c]; exact hc1.symm
  · rw [p4c]; exact hc2.symm
  · rw [p4c]; exact hc3.symm
  · intro y
    simpa only [p4c] using cover y

namespace Source
variable {O : Type} [Fintype O] {d : Schedule (Fin 5) (Fin 5) O}
variable (h : Source canonical d)
theorem single_row_no_two (m : Fin 5) (hm : 3 ≤ m.val)
    (w : Row (s := canonical) m) : h.rowPerm m (h.rowPerm m w) ≠ w := by
  intro he
  let x := rowCell (s := canonical) m w
  let y := rowCell (s := canonical) m (h.rowPerm m w)
  have hxy : x ≠ y := by
    intro hh
    exact h.rowPerm_no_fixed m w (Subtype.ext (congrArg (fun c : Cell canonical => c.1.2) hh.symm))
  have hx : h.U x = y := (h.rowCell_perm m w).symm
  have hy : h.U y = x := by rw [← h.rowCell_perm m (h.rowPerm m w),he]
  exact h.no_single_twoCycle x y hxy hx hy hm

theorem canonical_single_row_card (m : Fin 5) (hm : 3 ≤ m.val) :
    Fintype.card (Row (s := canonical) m) = 5 := by
  classical
  have hn : ∀ w, ¬ canonical.spouse m w := fun _ hh => by have := hh.2; omega
  change Fintype.card {w : Fin 5 // ¬ canonical.spouse m w} = 5
  simp [hn]

theorem single_row_five (m : Fin 5) (hm : 3 ≤ m.val) (x : Row (s := canonical) m) :
    let p := h.rowPerm m
    p (p (p (p (p x)))) = x ∧
    x ≠ p x ∧ x ≠ p (p x) ∧ x ≠ p (p (p x)) ∧ x ≠ p (p (p (p x))) ∧
    p x ≠ p (p x) ∧ p x ≠ p (p (p x)) ∧ p x ≠ p (p (p (p x))) ∧
    p (p x) ≠ p (p (p x)) ∧ p (p x) ≠ p (p (p (p x))) ∧
    p (p (p x)) ≠ p (p (p (p x))) ∧
    ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = p (p (p x)) ∨ y = p (p (p (p x))) :=
  orbit_five_of_no_two (h.rowPerm m) (canonical_single_row_card m hm)
    (h.rowPerm_no_fixed m) (h.single_row_no_two m hm) x
end Source
end CMDRR
