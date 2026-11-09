module
public import GridFinal4
@[expose] public section
namespace Grid343536
open SimpleGraph
set_option linter.unusedSimpArgs false

def ladderLayer {n : ℕ} (x : Fin 2 × Fin n) : ℕ := min (x.2.val+1) (n-x.2.val)

theorem ladder_layer_recurrence {n : ℕ} (hn : 3 ≤ n) (x : Fin 2 × Fin n) (k : ℕ) :
    ladderLayer x ≤ k+1 ↔ ladderLayer x = 1 ∨
      ∃ a, (G 2 n).Adj x a ∧ ladderLayer a ≤ k := by
  have hi := x.2.isLt
  have hj := x.1.isLt
  constructor
  · intro h
    by_cases hb : ladderLayer x = 1
    · exact Or.inl hb
    right
    unfold ladderLayer at h hb
    by_cases hleft : x.2.val+1 ≤ n-x.2.val
    · refine ⟨(x.1,⟨x.2.val-1,by omega⟩), ?_, ?_⟩
      · apply (grid_adj_iff _ _).mpr
        exact Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩
      · unfold ladderLayer; dsimp; omega
    · refine ⟨(x.1,⟨x.2.val+1,by omega⟩), ?_, ?_⟩
      · apply (grid_adj_iff _ _).mpr
        exact Or.inl ⟨rfl, Or.inl rfl⟩
      · unfold ladderLayer; dsimp; omega
  · rintro (hb | ⟨a,ha,hk⟩)
    · omega
    · have ha' := (grid_adj_iff _ _).mp ha
      have hai := a.2.isLt
      have haj := a.1.isLt
      simp only [Fin.ext_iff] at ha'
      unfold ladderLayer at hk ⊢
      omega

theorem ladder_layer_one {n : ℕ} (hn : 3 ≤ n) (x : Fin 2 × Fin n) :
    ladderLayer x = 1 ↔ (G 2 n).degree x = 2 := by
  have hi := x.2.isLt
  have hj := x.1.isLt
  rw [grid_degree_formula]
  unfold ladderLayer
  split_ifs <;> omega

theorem ladder_layer_invariant {n : ℕ} (hn : 3 ≤ n)
    (r : Setoid (Fin 2 × Fin n)) (hr : IsEquitable (G 2 n) r) :
    ∀ x y, r x y → ladderLayer x = ladderLayer y := by
  have hbase : ∀ x y, r x y → (ladderLayer x = 1 ↔ ladderLayer y = 1) := by
    intro x y h
    rw [ladder_layer_one hn, ladder_layer_one hn]
    have hd := equitable_degree (G 2 n) r hr h
    have he : (G 2 n).degree x = (G 2 n).degree y := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      convert hd using 1 <;> apply congrArg Finset.card <;> ext a <;> simp
    exact Iff.of_eq (congrArg (· = 2) he)
  have hle : ∀ k x y, r x y → (ladderLayer x ≤ k ↔ ladderLayer y ≤ k) := by
    intro k
    induction k with
    | zero =>
      intro x y h
      have hx := x.2.isLt
      have hy := y.2.isLt
      unfold ladderLayer
      omega
    | succ k ih =>
      intro x y h
      rw [ladder_layer_recurrence hn, ladder_layer_recurrence hn]
      apply or_congr (hbase x y h)
      have hs := saturated_neighbor_preimage hr (fun a b hab => ih a b hab) h
      change (∃ a, ladderLayer a ≤ k ∧ (G 2 n).Adj x a) ↔
        (∃ a, ladderLayer a ≤ k ∧ (G 2 n).Adj y a) at hs
      simpa only [and_comm] using hs
  intro x y h
  exact Nat.le_antisymm ((hle (ladderLayer y) x y h).mpr (Nat.le_refl _))
    ((hle (ladderLayer x) x y h).mp (Nat.le_refl _))

theorem ladder_layer_step {n : ℕ} (w : Fin 2 × Fin n) (hw : 2 ≤ ladderLayer w) :
    ∃ a, (G 2 n).Adj w a ∧ ladderLayer a+1 = ladderLayer w ∧
      ∀ b, (G 2 n).Adj a b → ladderLayer w ≤ ladderLayer b → b = w := by
  have hi := w.2.isLt
  have hj := w.1.isLt
  unfold ladderLayer at hw
  by_cases hleft : w.2.val+1 ≤ n-w.2.val
  · refine ⟨(w.1,⟨w.2.val-1,by omega⟩), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inl ⟨rfl, Or.inr (by dsimp; omega)⟩
    · unfold ladderLayer; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      have bi := b.2.isLt
      have bj := b.1.isLt
      simp only [Fin.ext_iff, Fin.val_mk] at hb'
      unfold ladderLayer at hl
      apply Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · refine ⟨(w.1,⟨w.2.val+1,by omega⟩), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inl ⟨rfl, Or.inl rfl⟩
    · unfold ladderLayer; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      have bi := b.2.isLt
      have bj := b.1.isLt
      simp only [Fin.ext_iff, Fin.val_mk] at hb'
      unfold ladderLayer at hl
      apply Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

end Grid343536
