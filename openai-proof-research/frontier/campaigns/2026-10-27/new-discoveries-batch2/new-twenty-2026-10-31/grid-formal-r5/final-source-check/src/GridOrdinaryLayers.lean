module
public import GridLadderOrbit
@[expose] public section
namespace Grid343536
open SimpleGraph
set_option linter.unusedSimpArgs false

def gridLayer {m n : ℕ} (x : Fin m × Fin n) : ℕ :=
  min (min (x.1.val+1) (m-x.1.val)) (min (x.2.val+1) (n-x.2.val))

theorem grid_layer_positive {m n : ℕ} (x : Fin m × Fin n) : 1 ≤ gridLayer x := by
  have := x.1.isLt
  have := x.2.isLt
  unfold gridLayer
  omega

/-- A predecessor has exactly one neighbour in the next or a deeper layer. -/
theorem grid_layer_step {m n : ℕ} (w : Fin m × Fin n) (hw : 2 ≤ gridLayer w) :
    ∃ a, (G m n).Adj w a ∧ gridLayer a+1 = gridLayer w ∧
      ∀ b, (G m n).Adj a b → gridLayer w ≤ gridLayer b → b = w := by
  have wi := w.1.isLt
  have wj := w.2.isLt
  unfold gridLayer at hw
  by_cases h1 : gridLayer w = w.1.val+1
  · refine ⟨(⟨w.1.val-1,by omega⟩,w.2), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inr ⟨Or.inr (by dsimp; unfold gridLayer at h1; omega),rfl⟩
    · unfold gridLayer at h1 ⊢; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      simp only [Fin.ext_iff,Fin.val_mk] at hb'
      have := b.1.isLt
      have := b.2.isLt
      unfold gridLayer at h1 hl
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  by_cases h2 : gridLayer w = m-w.1.val
  · refine ⟨(⟨w.1.val+1,by unfold gridLayer at h2; omega⟩,w.2), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inr ⟨Or.inl rfl,rfl⟩
    · unfold gridLayer at h2 ⊢; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      simp only [Fin.ext_iff,Fin.val_mk] at hb'
      have := b.1.isLt
      have := b.2.isLt
      unfold gridLayer at h2 hl
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  by_cases h3 : gridLayer w = w.2.val+1
  · refine ⟨(w.1,⟨w.2.val-1,by omega⟩), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inl ⟨rfl,Or.inr (by dsimp; unfold gridLayer at h3; omega)⟩
    · unfold gridLayer at h3 ⊢; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      simp only [Fin.ext_iff,Fin.val_mk] at hb'
      have := b.1.isLt
      have := b.2.isLt
      unfold gridLayer at h3 hl
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have h4 : gridLayer w = n-w.2.val := by unfold gridLayer at *; omega
  refine ⟨(w.1,⟨w.2.val+1,by unfold gridLayer at h4; omega⟩), ?_, ?_, ?_⟩
  · apply (grid_adj_iff _ _).mpr
    exact Or.inl ⟨rfl,Or.inl rfl⟩
  · unfold gridLayer at h4 ⊢; dsimp; omega
  · intro b hb hl
    have hb' := (grid_adj_iff _ _).mp hb
    simp only [Fin.ext_iff,Fin.val_mk] at hb'
    have := b.1.isLt
    have := b.2.isLt
    unfold gridLayer at h4 hl
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem grid_layer_recurrence {m n : ℕ} (x : Fin m × Fin n) (k : ℕ) :
    gridLayer x ≤ k+1 ↔ gridLayer x = 1 ∨
      ∃ a, (G m n).Adj x a ∧ gridLayer a ≤ k := by
  constructor
  · intro h
    by_cases hb : gridLayer x = 1
    · exact Or.inl hb
    have hp := grid_layer_positive x
    obtain ⟨a,ha,hl,_⟩ := grid_layer_step x (by omega)
    exact Or.inr ⟨a,ha,by omega⟩
  · rintro (hb | ⟨a,ha,hk⟩)
    · omega
    have h := (grid_adj_iff _ _).mp ha
    simp only [Fin.ext_iff] at h
    have := x.1.isLt
    have := x.2.isLt
    have := a.1.isLt
    have := a.2.isLt
    unfold gridLayer at hk ⊢
    omega

theorem grid_layer_one {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (x : Fin m × Fin n) : gridLayer x = 1 ↔ (G m n).degree x ≤ 3 := by
  have := x.1.isLt
  have := x.2.isLt
  rw [grid_degree_formula]
  unfold gridLayer
  split_ifs <;> omega

theorem grid_layer_invariant {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (r : Setoid (Fin m × Fin n)) (hr : IsEquitable (G m n) r) :
    ∀ x y, r x y → gridLayer x = gridLayer y := by
  have hbase : ∀ x y, r x y → (gridLayer x = 1 ↔ gridLayer y = 1) := by
    intro x y h
    rw [grid_layer_one hm hn,grid_layer_one hm hn]
    have hd := equitable_degree (G m n) r hr h
    have he : (G m n).degree x = (G m n).degree y := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      convert hd using 1 <;> apply congrArg Finset.card <;> ext a <;> simp
    rw [he]
  have hle : ∀ k x y, r x y → (gridLayer x ≤ k ↔ gridLayer y ≤ k) := by
    intro k
    induction k with
    | zero =>
      intro x y h
      have := grid_layer_positive x
      have := grid_layer_positive y
      omega
    | succ k ih =>
      intro x y h
      rw [grid_layer_recurrence,grid_layer_recurrence]
      apply or_congr (hbase x y h)
      have hs := saturated_neighbor_preimage hr (fun a b hab => ih a b hab) h
      change (∃ a, gridLayer a ≤ k ∧ (G m n).Adj x a) ↔
        (∃ a, gridLayer a ≤ k ∧ (G m n).Adj y a) at hs
      simpa only [and_comm] using hs
  intro x y h
  exact Nat.le_antisymm ((hle (gridLayer y) x y h).mpr (Nat.le_refl _))
    ((hle (gridLayer x) x y h).mp (Nat.le_refl _))

theorem grid_layer_automorphism {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (g : G m n ≃g G m n) (x : Fin m × Fin n) : gridLayer (g x) = gridLayer x :=
  (grid_layer_invariant hm hn (orbitSetoid (G m n) ⊤)
    (orbit_equitable _ _) x (g x) ⟨g,by trivial,rfl⟩).symm
end Grid343536
