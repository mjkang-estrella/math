import Digits
-- False admissibility of the enlarged digit set, tested on explicit permutations.
def enlarged (v : Fin 9 → ZMod 13) : Prop :=
  (∀ i, (v i).val ≤ 8) ∧ ∀ t : Fin 9,
    (Finset.univ.filter (fun i => v i = (t.val : ZMod 13))).card = 1
def a : Fin 9 → ZMod 13 := ![0,1,2,3,4,5,6,7,8]
def b : Fin 9 → ZMod 13 := ![0,2,8,4,3,6,5,1,7]
def c : Fin 9 → ZMod 13 := ![0,3,1,5,2,7,4,8,6]
def d : Fin 9 → ZMod 13 := ![0,4,7,6,1,8,3,2,5]
example : ¬ (enlarged a ∧ enlarged b ∧ enlarged c ∧ enlarged d ∧
    (∀ i, a i - 2*b i + c i = 0) ∧
    (∀ i, b i - 2*c i + d i = 0) ∧ a ≠ b) := by
  unfold enlarged a b c d
  decide
