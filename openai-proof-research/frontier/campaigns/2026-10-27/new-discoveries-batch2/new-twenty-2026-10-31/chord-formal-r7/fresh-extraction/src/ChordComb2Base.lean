import ChordFinal
import Mathlib.Tactic.FinCases
namespace Chord.Comb2
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def tableDiagram {n : Nat} (hn : 0 < n) (xs : List Nat)
    (hi : ∀ i : Fin (2*n), (xs.getD ((xs.getD i.val 0) % (2*n)) 0) % (2*n) = i.val)
    (hf : ∀ i : Fin (2*n), (xs.getD i.val 0) % (2*n) ≠ i.val) : Diagram n where
  partner i := ⟨xs.getD i.val 0 % (2*n), Nat.mod_lt _ (by omega)⟩
  involutive i := Fin.ext (hi i)
  noFixed i h := hf i (congrArg Fin.val h)

theorem partner_choices {n} (D : Diagram n) (i : Fin (2*n))
    (xs : List (Fin (2*n)))
    (cover : ∀ j, j ≠ i → (∀ k, D.partner k = j → k = i) → j ∈ xs) :
    D.partner i ∈ xs := by
  apply cover
  · exact D.noFixed i
  · intro k hk
    have h := congrArg D.partner hk
    simpa only [D.involutive] using h

end Chord.Comb2
namespace Chord.Comb2
def maskSides5 (m : Nat) : Sides 5 := fun i => m / 2^i.val % 2 == 1

def dihedral5 (r : Nat) (rev : Bool) : Fin 10 ≃ Fin 10 where
  toFun i := ⟨(if rev then r+10-1-i.val else i.val+r)%10, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨(if rev then r+10-1-i.val else i.val+10-r%10)%10, Nat.mod_lt _ (by decide)⟩
  left_inv := by
    intro i
    apply Fin.ext
    simp only
    split <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    simp only
    split <;> omega
end Chord.Comb2
namespace Chord.Comb2
instance {n} (D : Diagram n) (a b) : Decidable (Crosses D a b) := by unfold Crosses; infer_instance
instance {n} (D : Diagram n) : Decidable (HasTriangle D) := by unfold HasTriangle; infer_instance
instance {n} (D : Diagram n) c g : Decidable (HasGenus D c g) := by unfold HasGenus; infer_instance
end Chord.Comb2
