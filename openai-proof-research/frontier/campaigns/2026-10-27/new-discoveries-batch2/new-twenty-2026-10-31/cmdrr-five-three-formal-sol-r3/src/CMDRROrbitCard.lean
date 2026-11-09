import CMDRRFourOrbit
import Mathlib.GroupTheory.Perm.Cycle.Basic

open scoped Classical
namespace CMDRR
/-- A derangement of a four-element domain which is not a two-cycle at x
has one orbit of length four. The proof uses only the domain cardinality. -/
theorem orbit_four_of_not_two {α : Type} [Fintype α]
    (p : Equiv.Perm α) (hc : Fintype.card α = 4)
    (hd : ∀ y, p y ≠ y) (x : α) (h2 : p (p x) ≠ x) :
    ∃ c, p (p (p x)) = c ∧ p c = x ∧
      x ≠ p x ∧ x ≠ p (p x) ∧ x ≠ c ∧
      p x ≠ p (p x) ∧ p x ≠ c ∧ p (p x) ≠ c ∧
      ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = c := by
  classical
  have h01 : x ≠ p x := (hd x).symm
  have h02 : x ≠ p (p x) := h2.symm
  have h12 : p x ≠ p (p x) := fun he => h01 (p.injective he)
  let S : Finset α := {x,p x,p (p x)}
  have hs : S.card = 3 := by simp [S,h01,h02,h12]
  obtain ⟨c,hcS⟩ : ∃ c, c ∉ S := by
    by_contra hn
    have he : S = Finset.univ := by
      ext y
      simp only [Finset.mem_univ, iff_true]
      exact Classical.not_not.mp (fun hy => hn ⟨y,hy⟩)
    have hh := congrArg Finset.card he
    rw [hs,Finset.card_univ,hc] at hh
    omega
  have hc0 : x ≠ c := by intro he; apply hcS; simp [S,← he]
  have hc1 : p x ≠ c := by intro he; apply hcS; simp [S,← he]
  have hc2 : p (p x) ≠ c := by intro he; apply hcS; simp [S,← he]
  let A : Finset α := insert c S
  have ha : A.card = 4 := by simp [A,hcS,hs]
  have he : A = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,hc,ha]
  have cover : ∀ y, y = x ∨ y = p x ∨ y = p (p x) ∨ y = c := by
    intro y
    have hy : y ∈ A := by rw [he]; exact Finset.mem_univ _
    simp only [A,S,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy
    · exact Or.inr (Or.inr (Or.inr hy))
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl hy))
  have hh := four_orbit p x (p x) (p (p x)) c h02 hc0 h12 hc1 hc2 cover hd rfl h2
  rcases hh with ⟨_,hb,hdc⟩ | ⟨hec,_,_⟩
  · exact ⟨c,hb,hdc,h01,h02,hc0,h12,hc1,hc2,cover⟩
  · exact (hc2 hec).elim
end CMDRR
