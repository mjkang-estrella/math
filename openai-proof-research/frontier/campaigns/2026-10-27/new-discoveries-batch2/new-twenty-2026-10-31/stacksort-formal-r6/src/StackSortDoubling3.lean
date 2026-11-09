import StackSortShuffle3Root
namespace StackSort.Round3
 theorem doublingInjection_proved : StackSort.DoublingInjection := by
  intro a
  have h := StackSort.Shuffle3.choose_split_bound (2*a) a
  have hsub : 2*a-a = a := by omega
  simpa [hsub, pow_two, Nat.mul_assoc] using h
 theorem doubling_proved : StackSort.Doubling :=
  StackSort.doubling_of_injection doublingInjection_proved
end StackSort.Round3
