import Factoring.Contract

namespace Factoring

/-- Exhaustive specification baseline; intentionally not an efficient candidate. -/
def exhaustive (n : Nat) : Option Nat := (List.range n).find? (accepts n)

theorem exhaustive_sound {n d : Nat} (h : exhaustive n = some d) :
    NontrivialFactor n d := by
  exact (accepts_iff n d).mp (List.find?_some h)

theorem exhaustive_complete {n : Nat} (h : Composite n) :
    (exhaustive n).isSome := by
  rcases h with ⟨d, hd⟩
  apply List.find?_isSome.mpr
  exact ⟨d, List.mem_range.mpr hd.2.1, (accepts_iff n d).mpr hd⟩

theorem exhaustive_none_iff (n : Nat) : exhaustive n = none ↔ ¬ Composite n := by
  constructor
  · intro hn hc
    have hs := exhaustive_complete hc
    simp [hn] at hs
  · intro hc
    cases h : exhaustive n with
    | none => rfl
    | some d => exact False.elim (hc (factor_implies_composite (exhaustive_sound h)))

theorem factor_15 : exhaustive 15 = some 3 := by decide +kernel
theorem prime_13 : exhaustive 13 = none := by decide +kernel

end Factoring

