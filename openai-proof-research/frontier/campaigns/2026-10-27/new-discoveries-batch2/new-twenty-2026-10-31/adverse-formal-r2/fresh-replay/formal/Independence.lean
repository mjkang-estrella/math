import Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace Adverse381433

theorem independent_projections (s : Finset Cell) (h : Independent latinGraph s) :
    Set.InjOn Prod.fst (s : Set Cell) ∧ Set.InjOn Prod.snd (s : Set Cell) ∧
      Set.InjOn (fun p : Cell => p.1 + p.2) (s : Set Cell) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha b hb he
  · by_contra hn
    exact h a ha b hb hn ⟨hn, Or.inl he⟩
  · by_contra hn
    exact h a ha b hb hn ⟨hn, Or.inr (Or.inl he)⟩
  · by_contra hn
    exact h a ha b hb hn ⟨hn, Or.inr (Or.inr he)⟩

theorem independent_card_le_five (s : Finset Cell) (h : Independent latinGraph s) :
    s.card ≤ 5 := by
  classical
  obtain ⟨hr,hc,hs⟩ := independent_projections s h
  have hb : s.card ≤ 6 := by
    calc s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hr).symm
         _ ≤ (Finset.univ : Finset (ZMod 6)).card := Finset.card_le_card (Finset.subset_univ _)
         _ = 6 := by decide
  have hn : s.card ≠ 6 := by
    intro he
    have image_univ (f : Cell → ZMod 6) (hf : Set.InjOn f (s : Set Cell)) :
        s.image f = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_iff.mpr hf, he]
      decide
    have row : ∑ p ∈ s, p.1 = (3 : ZMod 6) := by
      rw [← Finset.sum_image (f := fun x : ZMod 6 => x) hr, image_univ Prod.fst hr]
      decide
    have col : ∑ p ∈ s, p.2 = (3 : ZMod 6) := by
      rw [← Finset.sum_image (f := fun x : ZMod 6 => x) hc, image_univ Prod.snd hc]
      decide
    have sym : ∑ p ∈ s, (p.1 + p.2) = (3 : ZMod 6) := by
      rw [← Finset.sum_image (f := fun x : ZMod 6 => x) hs, image_univ (fun p => p.1 + p.2) hs]
      decide
    rw [Finset.sum_add_distrib, row, col] at sym
    exact (by decide : (6 : ZMod 6) ≠ 3) sym
  omega

def independentFive : Finset Cell := {(0,0),(1,1),(2,2),(3,4),(4,5)}

theorem independentFive_valid : Independent latinGraph independentFive ∧
    independentFive.card = 5 := by
  unfold Independent latinGraph independentFive
  decide

theorem alpha_eq_five : alpha latinGraph = 5 := by
  have hb : BddAbove {n | ∃ s : Finset Cell, Independent latinGraph s ∧ s.card = n} :=
    ⟨5, by rintro n ⟨s,hs,rfl⟩; exact independent_card_le_five s hs⟩
  apply Nat.le_antisymm
  · exact csSup_le ⟨5, independentFive, independentFive_valid⟩
      (by rintro n ⟨s,hs,rfl⟩; exact independent_card_le_five s hs)
  · exact le_csSup hb ⟨independentFive, independentFive_valid⟩

end Adverse381433
