import StackSortSplit
noncomputable section
namespace StackSort

theorem le_fold_max (w : List ℕ) (x : ℕ) (hx : x ∈ w) : x ≤ w.foldr max 0 := by
  induction w with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem s_map_orderEmbedding (φ : ℕ ↪o ℕ) (w : List ℕ) :
    s (w.map φ) = (s w).map φ := by
  have aux : ∀ N : ℕ, ∀ w : List ℕ, w.length = N → s (w.map φ) = (s w).map φ := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro w hw
      cases w with
      | nil => rfl
      | cons x xs =>
        let w := x :: xs
        let m := w.foldr max 0
        let L := w.takeWhile (· != m)
        let R := (w.dropWhile (· != m)).drop 1
        have he : w = L ++ m :: R := split_spec w m (max_mem x xs)
        have hlen := congrArg List.length he
        simp only [List.length_append, List.length_cons] at hlen
        have hL : ∀ z ∈ L, z < m := by
          intro z hz
          have hmem : z ∈ w := by rw [he]; simp [hz]
          have hne : z ≠ m := by
            have hall := List.all_takeWhile (p := fun z => z != m) (l := w)
            have hh := List.all_eq_true.mp hall z hz
            simpa using hh
          exact lt_of_le_of_ne (le_fold_max w z hmem) hne
        have hR : ∀ z ∈ R, z ≤ m := by
          intro z hz
          apply le_fold_max w z
          rw [he]; simp [hz]
        have hl : L.length < N := by change w.length = N at hw; omega
        have hr : R.length < N := by change w.length = N at hw; omega
        have hLm : ∀ z ∈ L.map φ, z < φ m := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          exact φ.strictMono (hL y hy)
        have hRm : ∀ z ∈ R.map φ, z ≤ φ m := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          exact φ.monotone (hR y hy)
        change s (w.map φ) = (s w).map φ
        conv_lhs => rw [he, List.map_append, List.map_cons, s_split _ _ _ hLm hRm]
        rw [ih L.length hl L rfl, ih R.length hr R rfl]
        conv_rhs => rw [he, s_split L R m hL hR]
        simp
  exact aux w.length w rfl
end StackSort
