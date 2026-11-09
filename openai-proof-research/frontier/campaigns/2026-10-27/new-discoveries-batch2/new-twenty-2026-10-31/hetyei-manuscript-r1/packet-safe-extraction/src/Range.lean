import Defs
namespace Hetyei347230
theorem cop_snd_shorter {w : Word} {p : Word × Word} (hp : p ∈ cop w) :
    p.2.length < w.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hi' := List.mem_range.mp hi
  simp only [List.length_drop]
  omega

theorem Mrs_eq_nil_of_large (n : ℕ) :
    ∀ (r s : Bool) (u v : Word), u.length + v.length + 2 < n →
      Mrs r s n u v = [] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r s u v hn
    match n with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | k + 3 =>
      cases r
      · simp only [Mrs_step_false, List.flatMap_eq_nil_iff]
        intro p hp
        rw [ih (k + 2) (by omega) true s p.2 v (by
          have := cop_snd_shorter hp
          omega)]
        rfl
      · simp only [Mrs_step_true, List.flatMap_eq_nil_iff]
        intro p hp
        rw [ih (k + 2) (by omega) false s u p.2 (by
          have := cop_snd_shorter hp
          omega)]
        rfl
end Hetyei347230
