import IntervalBase

namespace IntervalWidth
variable {α : Type*} [LE α] {n k r : Nat} {I : Fin n → Interval α}

theorem width_attained (k : Nat) (I : Fin n → Interval α) :
    Nonempty (HeapPartition k I (width k I)) := by
  classical
  exact Nat.find_spec (partition_exists k I)

theorem width_le (P : HeapPartition k I r) : width k I ≤ r := by
  classical
  exact Nat.find_min' (partition_exists k I) ⟨P⟩

theorem width_le_size (k : Nat) (I : Fin n → Interval α) : width k I ≤ n :=
  width_le (singletonPartition k I)

theorem width_empty (k : Nat) (I : Fin 0 → Interval α) : width k I = 0 :=
  Nat.eq_zero_of_le_zero (width_le_size k I)

theorem Path.trans {p : Fin n → Option (Fin n)} {a b c : Fin n}
    (hab : Path p a b) (hbc : Path p b c) : Path p a c := by
  induction hbc with
  | refl => exact hab
  | step _ e ih => exact Path.step ih e

theorem Path.eq_or_lt (P : HeapPartition k I r) {a b : Fin n}
    (h : Path P.parent a b) : a = b ∨ a < b := by
  induction h with
  | refl => exact Or.inl rfl
  | @step i j _ e ih =>
    have hij := (P.edge i j e).1
    exact Or.inr (match ih with
      | Or.inl h => h ▸ hij
      | Or.inr h => lt_trans h hij)

theorem Path.color (P : HeapPartition k I r) {a b : Fin n}
    (h : Path P.parent a b) : P.color a = P.color b := by
  induction h with
  | refl => rfl
  | @step i j _ e ih => exact ih.trans (P.parent_color i j e)

theorem Path.to_root {p : Fin n → Option (Fin n)} {a b : Fin n}
    (h : Path p a b) (hb : p b = none) : a = b := by
  cases h with
  | refl => rfl
  | step _ e => simp [hb] at e

theorem parent_none_iff_root (P : HeapPartition k I r) (j : Fin n) :
    P.parent j = none ↔ j = P.root (P.color j) := by
  constructor
  · intro h; exact (Path.to_root (P.rooted j) h).symm
  · intro h; rw [h]; exact P.root_parent _

/-- Increasing the allowed arity cannot increase the tree partition minimum. -/
def HeapPartition.enlarge (P : HeapPartition k I r) (l : Nat) (h : k ≤ l) :
    HeapPartition l I r := { P with arity := fun i => (P.arity i).trans h }

theorem width_antitone_arity (k l : Nat) (h : k ≤ l) (I : Fin n → Interval α) :
    width l I ≤ width k I := by
  obtain ⟨P⟩ := width_attained k I
  exact width_le (P.enlarge l h)

end IntervalWidth
