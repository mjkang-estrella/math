import StackSortFinal

namespace StackSort.Seeds2

/-- The two ordered children left after deleting the maximum. -/
def rootWord (m : ℕ) (p : List ℕ × List ℕ) : List ℕ := p.1 ++ m :: p.2

def rootParts (m : ℕ) (w : List ℕ) : List ℕ × List ℕ :=
  (w.takeWhile (· != m), (w.dropWhile (· != m)).drop 1)

def Below (m : ℕ) (w : List ℕ) : Prop := ∀ x ∈ w, x < m

 theorem rootParts_rootWord (m : ℕ) (p : List ℕ × List ℕ)
    (h : Below m p.1) : rootParts m (rootWord m p) = p := by
  rcases p with ⟨L, R⟩
  have ht : (L ++ m :: R).takeWhile (· != m) = L := by
    rw [List.takeWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (h x hx))]
    simp
  have hd : (L ++ m :: R).dropWhile (· != m) = m :: R := by
    rw [List.dropWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (h x hx))]
    simp
  simp [rootParts, rootWord, ht, hd]

 theorem rootWord_rootParts (m : ℕ) (w : List ℕ) (h : m ∈ w) :
    rootWord m (rootParts m w) = w := (split_spec w m h).symm

 theorem rootWord_injective (m : ℕ) (p q : List ℕ × List ℕ)
    (hp : Below m p.1) (hq : Below m q.1)
    (h : rootWord m p = rootWord m q) : p = q := by
  have := congrArg (rootParts m) h
  rwa [rootParts_rootWord m p hp, rootParts_rootWord m q hq] at this

 theorem sort_rootWord (m : ℕ) (p : List ℕ × List ℕ)
    (hL : Below m p.1) (hR : Below m p.2) :
    s (rootWord m p) = s p.1 ++ s p.2 ++ [m] :=
  s_split _ _ _ hL (fun x hx => (hR x hx).le)

/-- Removing the final maximum preserves equality of concatenated sorted children. -/
 theorem root_collision_iff (m : ℕ) (p q : List ℕ × List ℕ)
    (hpL : Below m p.1) (hpR : Below m p.2)
    (hqL : Below m q.1) (hqR : Below m q.2) :
    s (rootWord m p) = s (rootWord m q) ↔
      s p.1 ++ s p.2 = s q.1 ++ s q.2 := by
  rw [sort_rootWord m p hpL hpR, sort_rootWord m q hqL hqR]
  simp only [List.append_cancel_right_eq]

/-- Arity zero, one (with a left/right choice), or two. Empty children are omitted. -/
inductive Children where
  | leaf
  | unary (right : Bool) (w : {w : List ℕ // w ≠ []})
  | binary (L R : {w : List ℕ // w ≠ []})
  deriving DecidableEq

def Children.parts : Children → List ℕ × List ℕ
  | .leaf => ([], [])
  | .unary false w => (w, [])
  | .unary true w => ([], w)
  | .binary L R => (L, R)

def childrenOfParts (p : List ℕ × List ℕ) : Children :=
  if hL : p.1 = [] then
    if hR : p.2 = [] then .leaf else .unary true ⟨p.2, hR⟩
  else if hR : p.2 = [] then .unary false ⟨p.1, hL⟩
  else .binary ⟨p.1, hL⟩ ⟨p.2, hR⟩

 theorem parts_childrenOfParts (p : List ℕ × List ℕ) :
    (childrenOfParts p).parts = p := by
  rcases p with ⟨L, R⟩
  unfold childrenOfParts
  split_ifs <;> simp_all [Children.parts]

 theorem childrenOfParts_parts (c : Children) : childrenOfParts c.parts = c := by
  cases c with
  | leaf => rfl
  | unary b w => cases b <;> simp [Children.parts, childrenOfParts, w.property]
  | binary L R => simp [Children.parts, childrenOfParts, L.property, R.property]

/-- This equivalence accounts for the multiplicities 1, 2, 1 without any counting assumption. -/
def childrenEquiv : Children ≃ (List ℕ × List ℕ) where
  toFun := Children.parts
  invFun := childrenOfParts
  left_inv := childrenOfParts_parts
  right_inv := parts_childrenOfParts

end StackSort.Seeds2
