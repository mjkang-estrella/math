import Invariances
namespace Nut8
/-- Signs propagated along an explicitly ordered rooted tree. The parent of every
non-root vertex has smaller index; this is the ordering provided by a BFS. -/
noncomputable def treeSign (p : ℕ → ℕ) (hp : ∀ i, 0 < i → p i < i)
    (w : ℕ → ℤ) (i : ℕ) : ℤ :=
  if _h : i = 0 then 1 else treeSign p hp w (p i) * w i
termination_by i
decreasing_by exact hp i (Nat.pos_of_ne_zero _h)

theorem treeSign_unit (p : ℕ → ℕ) (hp : ∀ i, 0 < i → p i < i)
    (w : ℕ → ℤ) (hw : ∀ i, w i = 1 ∨ w i = -1) (i : ℕ) :
    treeSign p hp w i = 1 ∨ treeSign p hp w i = -1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [treeSign]
    split_ifs with hi
    · exact Or.inl rfl
    · rcases ih (p i) (hp i (Nat.pos_of_ne_zero hi)) with h | h <;>
        rcases hw i with h' | h' <;> simp [h, h']

theorem treeSign_edge (p : ℕ → ℕ) (hp : ∀ i, 0 < i → p i < i)
    (w : ℕ → ℤ) (hw : ∀ i, w i = 1 ∨ w i = -1) (i : ℕ) (hi : i ≠ 0) :
    treeSign p hp w (p i) * w i * treeSign p hp w i = 1 := by
  conv_lhs => arg 2; rw [treeSign]; simp only [hi, ↓reduceDIte]
  rcases treeSign_unit p hp w hw (p i) with h | h <;>
    rcases hw i with h' | h' <;> simp [h, h']
theorem treeSign_weight (p : ℕ → ℕ) (hp : ∀ i, 0 < i → p i < i)
    (w : ℕ → ℤ) (hw : ∀ i, w i = 1 ∨ w i = -1)
    (v : ℕ → ℤ) (hv : ∀ i, v i = w i * |v i|) (i : ℕ) (hi : i ≠ 0) :
    treeSign p hp w (p i) * v i * treeSign p hp w i = |v i| := by
  calc
    _ = (treeSign p hp w (p i) * w i * treeSign p hp w i) * |v i| := by
      conv_lhs => arg 1; arg 2; rw [hv i]
      ring
    _ = |v i| := by rw [treeSign_edge p hp w hw i hi, one_mul]
end Nut8
