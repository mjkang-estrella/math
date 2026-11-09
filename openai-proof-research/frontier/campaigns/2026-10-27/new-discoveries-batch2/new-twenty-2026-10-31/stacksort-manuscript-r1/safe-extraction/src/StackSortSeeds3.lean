import StackSortShuffle3Tuples
namespace StackSort.Round3
open Seeds2
/-- Exact remaining common-cut identity; no bijection is assumed in the environment. -/
def CommonCutCount : Prop := ∀ M r s, 1 ≤ M →
    1 ≤ r → r ≤ bound M → 1 ≤ s → s ≤ bound M →
    literalX M r s = literalI M r s + correction false literalX literalI M r s
/-- Exact remaining maximum-final count, requiring the tuple-level deletion assembly. -/
def MaximumFinalCount : Prop := ∀ M r s, 1 ≤ M →
    1 ≤ r → r ≤ bound M → 1 ≤ s → s ≤ bound M →
    literalI M r s + correction true literalX literalI M r s = deletion literalX M r s
 theorem additiveRecursion_of_counts (hc : CommonCutCount) (hm : MaximumFinalCount) :
    AdditiveRecursion := by
  intro M r s hM hr hrB hs hsB
  exact ⟨hm M r s hM hr hrB hs hsB, hc M r s hM hr hrB hs hsB⟩
 theorem counts_iff_additiveRecursion :
    (CommonCutCount ∧ MaximumFinalCount) ↔ AdditiveRecursion := by
  constructor
  · rintro ⟨hc,hm⟩; exact additiveRecursion_of_counts hc hm
  · intro h
    exact ⟨fun M r s hM hr hrB hs hsB => (h M r s hM hr hrB hs hsB).2,
      fun M r s hM hr hrB hs hsB => (h M r s hM hr hrB hs hsB).1⟩
end StackSort.Round3
