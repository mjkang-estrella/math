import Closure
set_option autoImplicit false
set_option warningAsError true
namespace FourAttractor
def bits (s : String) : Word := s.toList.map (· == '1')
def w1 := bits "01"
def w2 := bits "0101"
def w3 := bits "0101100101"
def w4 := bits "010110010101100101"
def w := bits "010110010101100101101001101010011010"
theorem check_closure (e : Bool) (s t : Word) (k : Nat)
    (hg : good e s k) (hm : ∀ j ∈ List.range k, ¬ good e s j)
    (ht : candidate e s k = t) : closure e s = t := by
  rw [closure_eq_checked e s k hg (by simpa using hm), ht]
theorem step1 : closure true [false] = w1 := by
  apply check_closure _ _ _ 1 <;> decide
theorem step2 : closure true (w1 ++ [false]) = w2 := by
  apply check_closure _ _ _ 1 <;> decide
theorem step3 : closure true (w2 ++ [true]) = w3 := by
  apply check_closure _ _ _ 5 <;> decide
theorem step4 : closure true (w3 ++ [false]) = w4 := by
  apply check_closure _ _ _ 7 <;> decide
theorem step5 : closure false (w4 ++ [true]) = w := by
  apply check_closure _ _ _ 17 <;> decide
def delta (n : Nat) : Bool := n = 2 || n = 4
def anti (n : Nat) : Bool := n < 4
def prefixWord (d t : Nat → Bool) : Nat → Word :=
  Nat.rec [] (fun n prev => closure (t n) (prev ++ [d n]))
theorem fifth : prefixWord delta anti 5 = w := by
  change closure false (closure true (closure true (closure true (closure true [false] ++ [false]) ++ [true]) ++ [false]) ++ [true]) = w
  rw [step1, step2, step3, step4, step5]
theorem prefix_step (d t : Nat → Bool) (n : Nat) :
    (prefixWord d t n).IsPrefix (prefixWord d t (n+1)) := by
  exact (List.prefix_append _ _).trans (closure_spec _ _).1
theorem strict_growth (d t : Nat → Bool) (n : Nat) :
    (prefixWord d t n).length < (prefixWord d t (n+1)).length := by
  have h := (closure_spec (t n) (prefixWord d t n ++ [d n])).1.length_le
  change _ < (closure (t n) (prefixWord d t n ++ [d n])).length
  simp only [List.length_append, List.length_singleton] at h
  omega
theorem length_ge (d t : Nat → Bool) (n : Nat) : n ≤ (prefixWord d t n).length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => have := strict_growth d t n; omega
theorem prefix_nested (d t : Nat → Bool) {n m : Nat} (h : n ≤ m) :
    (prefixWord d t n).IsPrefix (prefixWord d t m) := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step h ih => exact ih.trans (prefix_step d t _)
def infiniteWord (d t : Nat → Bool) (i : Nat) : Bool :=
  (prefixWord d t (i+1))[i]'(by have := length_ge d t (i+1); omega)
theorem prefixes_infinite (d t : Nat → Bool) (n i : Nat)
    (hi : i < (prefixWord d t n).length) :
    (prefixWord d t n)[i] = infiniteWord d t i := by
  unfold infiniteWord
  have hn := prefix_nested d t (Nat.le_max_left n (i+1))
  have hm := prefix_nested d t (Nat.le_max_right n (i+1))
  exact (hn.getElem hi).trans (hm.getElem (by have := length_ge d t (i+1); omega)).symm
theorem definition3 (d t : Nat → Bool) :
    prefixWord d t 0 = [] ∧
    (∀ n, IsClosure (t n) (prefixWord d t n ++ [d n]) (prefixWord d t (n+1))) ∧
    (∀ n i (h : i < (prefixWord d t n).length), (prefixWord d t n)[i] = infiniteWord d t i) ∧
    (∀ n, n ≤ (prefixWord d t n).length) :=
  ⟨rfl, fun _ => closure_spec _ _, prefixes_infinite d t, length_ge d t⟩
end FourAttractor
