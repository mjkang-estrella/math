module
public import GridChecks
@[expose] public section

namespace Grid343536
def labelEquitable (m n : ℕ) (lab : List ℕ) : Prop :=
  ∀ u v : Fin m × Fin n,
    lab[u.1.val*n+u.2.val]?.getD 0 = lab[v.1.val*n+v.2.val]?.getD 0 →
    ∀ w : Fin m × Fin n,
    (Finset.univ.filter (fun x : Fin m × Fin n =>
      (G m n).Adj u x ∧ lab[x.1.val*n+x.2.val]?.getD 0 =
        lab[w.1.val*n+w.2.val]?.getD 0)).card =
    (Finset.univ.filter (fun x : Fin m × Fin n =>
      (G m n).Adj v x ∧ lab[x.1.val*n+x.2.val]?.getD 0 =
        lab[w.1.val*n+w.2.val]?.getD 0)).card

instance labelDec (m n : ℕ) (lab : List ℕ) : Decidable (labelEquitable m n lab) := by
  unfold labelEquitable
  infer_instance

def labelSetoid (m n : ℕ) (lab : List ℕ) : Setoid (Fin m × Fin n) :=
  Setoid.ker (fun x => lab[x.1.val*n+x.2.val]?.getD 0)

theorem labelEquitable_iff (m n : ℕ) (lab : List ℕ) :
    IsEquitable (G m n) (labelSetoid m n lab) ↔ labelEquitable m n lab := by
  classical
  have hrel : ∀ u v : Fin m × Fin n, (labelSetoid m n lab) u v ↔
      lab[u.1.val*n+u.2.val]?.getD 0 = lab[v.1.val*n+v.2.val]?.getD 0 :=
    fun _ _ => Setoid.ker_def
  simp only [IsEquitable, labelEquitable, hrel,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

def labels2 : List (List ℕ) := [[0, 0, 0, 0], [0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [0, 1, 1, 2], [0, 1, 2, 0], [0, 1, 2, 3]]
theorem labels2_distinct : labels2.Nodup := by decide
theorem labels2_count : labels2.length = 7 := by decide
theorem labels2_equitable : labels2.all (fun lab => decide (labelEquitable 2 2 lab)) = true := by decide
def labels3 : List (List ℕ) := [[0, 1, 0, 1, 2, 1, 0, 1, 0], [0, 1, 0, 2, 3, 2, 0, 1, 0], [0, 1, 0, 2, 3, 2, 4, 5, 4], [0, 1, 2, 1, 3, 1, 2, 1, 0], [0, 1, 2, 1, 3, 4, 2, 4, 5], [0, 1, 2, 3, 4, 1, 5, 3, 0], [0, 1, 2, 3, 4, 3, 2, 1, 0], [0, 1, 2, 3, 4, 5, 0, 1, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8]]
theorem labels3_distinct : labels3.Nodup := by decide
theorem labels3_count : labels3.length = 9 := by decide
theorem labels3_equitable : labels3.all (fun lab => decide (labelEquitable 3 3 lab)) = true := by decide
theorem bad_partition : ¬ labelEquitable 2 2 [0,0,1,2] := by decide
theorem refinement_direction : (⊥ : Setoid (Fin 2 × Fin 2)) ≤ ⊤ := bot_le
theorem reversed_direction_false : ¬ (⊤ : Setoid (Fin 2 × Fin 2)) ≤ ⊥ := by
  intro h
  have he : (0,0) = ((0,1) : Fin 2 × Fin 2) := h (by trivial)
  exact (by decide : (0,0) ≠ ((0,1) : Fin 2 × Fin 2)) he
end Grid343536
