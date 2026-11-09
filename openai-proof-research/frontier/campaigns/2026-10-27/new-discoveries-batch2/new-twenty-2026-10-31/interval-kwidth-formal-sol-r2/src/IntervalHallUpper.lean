import IntervalDummy
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace IntervalWidth
variable {α : Type*} [LE α] {n k d : Nat} {I : Fin n → Interval α}

noncomputable def copyNeighbors (k : Nat) (I : Fin n → Interval α) (j : Fin n) :
    Finset (Fin n × Fin k) := by
  classical
  exact Finset.univ.filter (fun c => Compatible I c.1 j)

/-- Finite Hall with universal dummy supplies: no continuum or limit premise. -/
theorem width_le_of_hall (k d : Nat) (I : Fin n → Interval α)
    (h : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (copyNeighbors k I)).card + d) :
    width k I ≤ d := by
  classical
  let t : Fin n → Finset ((Fin n × Fin k) ⊕ Fin d) :=
    fun j => (copyNeighbors k I j).disjSum Finset.univ
  have hh : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion t).card := by
    intro S
    by_cases hs : S.Nonempty
    · have eq : S.biUnion t = (S.biUnion (copyNeighbors k I)).disjSum Finset.univ := by
        ext c
        cases c with
        | inl c => simp [t]
        | inr c => simpa [t, Finset.Nonempty] using hs
      rw [eq, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      exact h S
    · have eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [eq]
  obtain ⟨f, hf, ht⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hh
  let D : DummyMatching k d I := {
    assign := f
    injective := hf
    edge := by
      intro j i s e
      have hmem := ht j
      rw [e] at hmem
      simpa [t, copyNeighbors] using hmem }
  exact D.width_le

end IntervalWidth
