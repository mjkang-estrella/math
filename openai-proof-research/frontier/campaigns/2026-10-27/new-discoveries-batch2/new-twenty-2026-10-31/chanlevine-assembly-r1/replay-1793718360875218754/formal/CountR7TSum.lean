import CountR7TWeights
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7T
open Round6 Polynomial
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n] {F : Type*} [CommRing F]

theorem sum_words_matching (z : F) (g : ZMod n → F) :
    (∑ q : StateWord n, wordWeight z g q) =
      ∑ s : {s : Finset (ZMod n) // Matching s},
        (-z)^s.val.card * (1+z)^(n-2*s.val.card) *
          ∏ k ∈ s.val ∪ rightEnds s.val, g k := by
  have hzero : (∑ q : {q : StateWord n // ¬ Admissible q},
      wordWeight z g q.val) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact inadmissible_weight z g q.val q.property
  have he := Fintype.sum_subtype_add_sum_subtype (Admissible (n := n)) (wordWeight z g)
  rw [hzero,add_zero] at he
  rw [← he]
  calc
    _ = ∑ s : {s : Finset (ZMod n) // Matching s},
        wordWeight z g (matchingWord s.val) := by
      exact (stateMatchingEquiv (n := n)).symm.sum_comp (wordWeight z g ∘ Subtype.val) |>.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact matching_weight z g s.val s.property

/-- All closed state words sum to the literal frozen matching numerator. -/
theorem sum_words_numerator {K : Type*} [Field K] (z : K) :
    (∑ q : StateWord n, wordWeight (Polynomial.C z)
      (fun k => 1-X*Polynomial.C (z^k.val)) q) = matchingNumerator n z := by
  rw [sum_words_matching]
  unfold matchingNumerator
  rw [Finset.powerset_univ]
  have he := Fintype.sum_subtype_add_sum_subtype (Matching (n := n))
    (fun s : Finset (ZMod n) => if Matching s then
      (Polynomial.C (-z))^s.card * (Polynomial.C (1+z))^(n-2*s.card) *
        ∏ k ∈ s ∪ rightEnds s, (1-X*Polynomial.C (z^k.val)) else 0)
  have hn (s : {s : Finset (ZMod n) // ¬ Matching s}) : ¬ Matching s.val := s.property
  simp only [Subtype.property, hn, ite_true, ite_false,
    Finset.sum_const_zero, add_zero] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro s _
  simp only [map_neg, map_add, map_one]
end ChanLevine.Round7T
