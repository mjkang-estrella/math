import Assembly
set_option autoImplicit false
namespace Polyomino57
-- Sorting is needed only for completeness of supplied data, not for soundness.
-- Inserting in lexicographic position makes one linear equality replace two
-- quadratic mutual-membership tests when the supplied rows are sorted.
def insertSorted (b : GridPoint) : List GridPoint → List GridPoint
  | [] => [b]
  | p :: ps => if b.1 < p.1 ∨ (b.1 = p.1 ∧ b.2 ≤ p.2) then
      b :: p :: ps else p :: insertSorted b ps

theorem insertSorted_semantics (b : GridPoint) (P : List GridPoint) :
    (insertSorted b P).toFinset = insert b P.toFinset := by
  induction P with
  | nil => simp [insertSorted]
  | cons p ps ih =>
    simp only [insertSorted]
    split
    · simp
    · simp only [List.toFinset_cons, ih, Finset.insert_comm]

def edgeFastCheck (next : Array (List GridPoint)) (P : List GridPoint)
    (b : GridPoint) (index : ℕ) (t : GridPoint) : Bool :=
  if hi : index < next.size then decide (shiftedCells (insertSorted b P) t = next[index]) else false

theorem edgeFastCheck_implies (next : Array (List GridPoint)) (P : List GridPoint)
    (b : GridPoint) (index : ℕ) (t : GridPoint)
    (h : edgeFastCheck next P b index t = true) : edgeCheck next P b index t = true := by
  unfold edgeFastCheck at h
  unfold edgeCheck
  split at h
  next hi =>
    rw [dite_eq_left hi]
    apply (cellsEqCheck_iff _ _).mpr
    have he := congrArg List.toFinset (of_decide_eq_true h)
    rw [shiftedCells_semantics,insertSorted_semantics] at he
    simpa only [shiftedCells_semantics,List.toFinset_cons] using he
  next hn => simp at h

def successorFastRowCheck (next : Array (List GridPoint)) (P : List GridPoint)
    (choice : GridPoint → ℕ × GridPoint) : Bool :=
  P.all (fun a => (neighborCells a).all (fun b =>
    P.contains b || edgeFastCheck next P b (choice b).1 (choice b).2))

theorem successorFastRowCheck_implies (next : Array (List GridPoint)) (P : List GridPoint)
    (choice : GridPoint → ℕ × GridPoint) (h : successorFastRowCheck next P choice = true) :
    successorRowCheck next P choice = true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  have he := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
  simp only [Bool.or_eq_true] at he ⊢
  rcases he with he | he
  · exact Or.inl he
  · exact Or.inr (edgeFastCheck_implies next P b _ _ he)

def arrayFastClosureCheck (A B : Array (List GridPoint))
    (choices : List GridPoint → GridPoint → ℕ × GridPoint) : Bool :=
  A.toList.all (fun row => successorFastRowCheck B row (choices row))

theorem arrayFastClosureCheck_implies (A B : Array (List GridPoint))
    (choices : List GridPoint → GridPoint → ℕ × GridPoint)
    (h : arrayFastClosureCheck A B choices = true) : arrayClosureCheck A B choices = true := by
  apply List.all_eq_true.mpr
  intro row hr
  exact successorFastRowCheck_implies B row (choices row) (List.all_eq_true.mp h row hr)
end Polyomino57
