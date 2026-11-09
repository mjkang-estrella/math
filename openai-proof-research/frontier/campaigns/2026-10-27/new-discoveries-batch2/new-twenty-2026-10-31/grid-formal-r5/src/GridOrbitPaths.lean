module
public import GridFreeClassification
@[expose] public section
namespace Grid343536
open SimpleGraph
set_option linter.unusedSimpArgs false

def pathLayer {m : ℕ} (x : Fin m × Fin 1) : ℕ := min (x.1.val+1) (m-x.1.val)

theorem path_layer_recurrence {m : ℕ} (hm : 2 ≤ m) (x : Fin m × Fin 1) (k : ℕ) :
    pathLayer x ≤ k+1 ↔ pathLayer x = 1 ∨
      ∃ a, (G m 1).Adj x a ∧ pathLayer a ≤ k := by
  have hi := x.1.isLt
  have hj := x.2.isLt
  constructor
  · intro h
    by_cases hb : pathLayer x = 1
    · exact Or.inl hb
    right
    unfold pathLayer at h hb
    by_cases hleft : x.1.val+1 ≤ m-x.1.val
    · refine ⟨(⟨x.1.val-1,by omega⟩,x.2), ?_, ?_⟩
      · apply (grid_adj_iff _ _).mpr
        exact Or.inr ⟨Or.inr (by dsimp; omega), rfl⟩
      · unfold pathLayer; dsimp; omega
    · refine ⟨(⟨x.1.val+1,by omega⟩,x.2), ?_, ?_⟩
      · apply (grid_adj_iff _ _).mpr
        exact Or.inr ⟨Or.inl rfl,rfl⟩
      · unfold pathLayer; dsimp; omega
  · rintro (hb | ⟨a,ha,hk⟩)
    · omega
    · have ha' := (grid_adj_iff _ _).mp ha
      have hai := a.1.isLt
      have haj := a.2.isLt
      simp only [Fin.ext_iff] at ha'
      unfold pathLayer at hk ⊢
      omega

theorem path_layer_one {m : ℕ} (hm : 2 ≤ m) (x : Fin m × Fin 1) :
    pathLayer x = 1 ↔ (G m 1).degree x = 1 := by
  have hi := x.1.isLt
  have hj := x.2.isLt
  rw [grid_degree_formula]
  unfold pathLayer
  split_ifs <;> omega

theorem path_layer_invariant {m : ℕ} (hm : 2 ≤ m)
    (r : Setoid (Fin m × Fin 1)) (hr : IsEquitable (G m 1) r) :
    ∀ x y, r x y → pathLayer x = pathLayer y := by
  have hbase : ∀ x y, r x y → (pathLayer x = 1 ↔ pathLayer y = 1) := by
    intro x y h
    rw [path_layer_one hm, path_layer_one hm]
    have hd := equitable_degree (G m 1) r hr h
    have he : (G m 1).degree x = (G m 1).degree y := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      convert hd using 1 <;> apply congrArg Finset.card <;> ext a <;> simp
    exact Iff.of_eq (congrArg (· = 1) he)
  have hle : ∀ k x y, r x y → (pathLayer x ≤ k ↔ pathLayer y ≤ k) := by
    intro k
    induction k with
    | zero =>
      intro x y h
      have hx := x.1.isLt
      have hy := y.1.isLt
      unfold pathLayer
      omega
    | succ k ih =>
      intro x y h
      rw [path_layer_recurrence hm, path_layer_recurrence hm]
      apply or_congr (hbase x y h)
      have hs := saturated_neighbor_preimage hr (fun a b hab => ih a b hab) h
      change (∃ a, pathLayer a ≤ k ∧ (G m 1).Adj x a) ↔
        (∃ a, pathLayer a ≤ k ∧ (G m 1).Adj y a) at hs
      simpa only [and_comm] using hs
  intro x y h
  exact Nat.le_antisymm ((hle (pathLayer y) x y h).mpr (Nat.le_refl _))
    ((hle (pathLayer x) x y h).mp (Nat.le_refl _))

theorem path_layer_step {m : ℕ} (w : Fin m × Fin 1) (hw : 2 ≤ pathLayer w) :
    ∃ a, (G m 1).Adj w a ∧ pathLayer a+1 = pathLayer w ∧
      ∀ b, (G m 1).Adj a b → pathLayer w ≤ pathLayer b → b = w := by
  have hi := w.1.isLt
  have hj := w.2.isLt
  unfold pathLayer at hw
  by_cases hleft : w.1.val+1 ≤ m-w.1.val
  · refine ⟨(⟨w.1.val-1,by omega⟩,w.2), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inr ⟨Or.inr (by dsimp; omega), rfl⟩
    · unfold pathLayer; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      have bi := b.1.isLt
      have bj := b.2.isLt
      simp only [Fin.ext_iff, Fin.val_mk] at hb'
      unfold pathLayer at hl
      apply Prod.ext (Fin.ext (by omega)) (Subsingleton.elim _ _)
  · refine ⟨(⟨w.1.val+1,by omega⟩,w.2), ?_, ?_, ?_⟩
    · apply (grid_adj_iff _ _).mpr
      exact Or.inr ⟨Or.inl rfl,rfl⟩
    · unfold pathLayer; dsimp; omega
    · intro b hb hl
      have hb' := (grid_adj_iff _ _).mp hb
      have bi := b.1.isLt
      have bj := b.2.isLt
      simp only [Fin.ext_iff, Fin.val_mk] at hb'
      unfold pathLayer at hl
      apply Prod.ext (Fin.ext (by omega)) (Subsingleton.elim _ _)

theorem main_orbit_column_path (m : ℕ) (hm : 1 ≤ m)
    (r : Setoid (Fin m × Fin 1)) (hr : IsEquitable (G m 1) r) :
    r = orbitSetoid (G m 1) (Hpi r) := by
  by_cases hm1 : m = 1
  · subst m
    apply le_antisymm
    · intro u v h
      exact ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩
    · exact Hpi_orbit_le r
  have hm2 : 2 ≤ m := by omega
  apply positive_layer_propagation r hr pathLayer
  · intro x
    have hi := x.1.isLt
    unfold pathLayer
    omega
  · exact path_layer_invariant hm2 r hr
  · intro g hg x
    exact (path_layer_invariant hm2 (orbitSetoid (G m 1) ⊤)
      (orbit_equitable _ _) x (g x) ⟨g,by trivial,rfl⟩).symm
  · exact path_layer_step
  · intro u v hu huv
    have hv := (path_layer_invariant hm2 r hr u v huv).symm.trans hu
    by_cases he : u = v
    · exact ⟨1,Subgroup.one_mem _,he⟩
    have ui := u.1.isLt
    have vi := v.1.isLt
    have hue : u.1.val = 0 ∨ u.1.val = m-1 := by unfold pathLayer at hu; omega
    have hve : v.1.val = 0 ∨ v.1.val = m-1 := by unfold pathLayer at hv; omega
    have hsum : u.1.val+v.1.val = m-1 := by
      have hn : u.1.val ≠ v.1.val := by
        intro hh
        exact he (Prod.ext (Fin.ext hh) (Subsingleton.elim _ _))
      omega
    have hflip : rowFlip m 1 u = v := by
      apply Prod.ext _ (Subsingleton.elim _ _)
      apply Fin.ext
      change (Fin.rev u.1).val = v.1.val
      rw [Fin.val_rev]
      omega
    have hends : r (⟨m-1,by omega⟩,0) (⟨0,by omega⟩,0) := by
      rcases hue with hue | hue
      · have eu : u = (⟨0,by omega⟩,0) := Prod.ext (Fin.ext hue) (Subsingleton.elim _ _)
        have vv : v.1.val = m-1 := by omega
        have ev : v = (⟨m-1,by omega⟩,0) := Prod.ext (Fin.ext vv) (Subsingleton.elim _ _)
        simpa only [eu,ev] using r.symm huv
      · have eu : u = (⟨m-1,by omega⟩,0) := Prod.ext (Fin.ext hue) (Subsingleton.elim _ _)
        have vv : v.1.val = 0 := by omega
        have ev : v = (⟨0,by omega⟩,0) := Prod.ext (Fin.ext vv) (Subsingleton.elim _ _)
        simpa only [eu,ev] using huv
    refine ⟨rowFlip m 1, ⟨?_, ?_⟩, hflip⟩
    · simp only [A0, dite_eq_right hm1]
      apply Subgroup.subset_closure
      simp
    · apply row_determinism r hr
      intro j h0
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      convert hends using 1
      apply Prod.ext
      · apply Fin.ext
        simp [rowFlip, Fin.val_rev]
      · exact Subsingleton.elim _ _
end Grid343536
