import StackSortMaximum4

namespace StackSort.Round4
open Seeds2

def childrenTuple : Children → List (List ℕ)
  | .leaf => []
  | .unary _ w => [w.val]
  | .binary L R => [L.val,R.val]

def childrenArity : Children → ℕ
  | .leaf => 0
  | .unary _ _ => 1
  | .binary _ _ => 2

theorem childrenTuple_length (c : Children) : (childrenTuple c).length = childrenArity c := by
  cases c <;> rfl

theorem childrenTuple_nonempty (c : Children) : NonemptyWords (childrenTuple c) := by
  cases c with
  | leaf => simp [childrenTuple,NonemptyWords]
  | unary b w => simpa [childrenTuple,NonemptyWords] using w.property
  | binary L R => simpa [childrenTuple,NonemptyWords] using And.intro L.property R.property

theorem childrenTuple_output (c : Children) :
    output (childrenTuple c) = s c.parts.1 ++ s c.parts.2 := by
  cases c with
  | leaf => rfl
  | unary b w => cases b <;> simp [childrenTuple,Children.parts,output,s]
  | binary L R => simp [childrenTuple,Children.parts,output]

/-- Root deletion in an arbitrary tuple prefix, with empty children omitted. -/
theorem delete_last_output (m : ℕ) (A : List (List ℕ)) (c : Children)
    (hL : Below m c.parts.1) (hR : Below m c.parts.2) :
    output (A ++ [rootWord m c.parts]) =
      output (A ++ childrenTuple c) ++ [m] := by
  rw [output_append,output_append,childrenTuple_output]
  simp only [output,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [sort_rootWord m c.parts hL hR]
  simp only [List.append_assoc]

/-- Deletion preserves and reflects collisions of maximum-final tuples. -/
theorem delete_last_collision_iff (m : ℕ) (A B : List (List ℕ)) (c d : Children)
    (hcL : Below m c.parts.1) (hcR : Below m c.parts.2)
    (hdL : Below m d.parts.1) (hdR : Below m d.parts.2) :
    output (A ++ [rootWord m c.parts]) = output (B ++ [rootWord m d.parts]) ↔
      output (A ++ childrenTuple c) = output (B ++ childrenTuple d) := by
  rw [delete_last_output m A c hcL hcR,delete_last_output m B d hdL hdR]
  simp only [List.append_cancel_right_eq]

/-- The reduced tuple has the exact arity shift used in the deletion sum. -/
theorem delete_last_length (A : List (List ℕ)) (c : Children) :
    (A ++ childrenTuple c).length = (A ++ [rootWord m c.parts]).length - 1 + childrenArity c := by
  simp [childrenTuple_length]

end StackSort.Round4
