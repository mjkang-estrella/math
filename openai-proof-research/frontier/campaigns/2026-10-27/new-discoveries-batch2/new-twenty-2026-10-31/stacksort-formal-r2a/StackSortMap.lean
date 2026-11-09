import StackSortBasic
noncomputable section
namespace StackSort

theorem max_mem (x : ℕ) (xs : List ℕ) : (x :: xs).foldr max 0 ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases le_total x (max y (ys.foldr max 0)) with h | h
    · rw [max_eq_right h]
      exact List.mem_cons_of_mem _ (ih y)
    · rw [max_eq_left h]
      exact List.mem_cons_self

theorem split_spec (w : List ℕ) (m : ℕ) (hm : m ∈ w) :
    w = w.takeWhile (· != m) ++ m :: ((w.dropWhile (· != m)).drop 1) := by
  induction w with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases h : x = m
    · subst x; simp
    · have hmem : m ∈ xs := by simpa [h, Ne.symm h] using hm
      simpa [h, List.takeWhile_cons, List.dropWhile_cons] using
        congrArg (List.cons x) (ih hmem)

theorem sortFuel_perm (k : ℕ) (w : List ℕ) (hw : w.length ≤ k) :
    (sortFuel k w).Perm w := by
  induction k generalizing w with
  | zero => have : w = [] := List.length_eq_zero_iff.mp (by omega); subst w; simp
  | succ k ih =>
    cases w with
    | nil => simp
    | cons x xs =>
      let w := x :: xs
      let m := w.foldr max 0
      let l := w.takeWhile (· != m)
      let r := (w.dropWhile (· != m)).drop 1
      have he : w = l ++ m :: r := split_spec w m (max_mem x xs)
      have hlen := congrArg List.length he
      simp only [List.length_append, List.length_cons] at hlen
      simp only [List.length_cons] at hw
      have hl : l.length ≤ k := by simp only [w, List.length_cons] at hlen; omega
      have hr : r.length ≤ k := by simp only [w, List.length_cons] at hlen; omega
      change (sortFuel k l ++ sortFuel k r ++ [m]).Perm w
      rw [he]
      exact ((ih l hl).append (ih r hr) |>.append_right [m]).trans
        (by simpa [List.append_assoc] using
          (List.Perm.refl l).append (List.perm_append_comm (l₁ := r) (l₂ := [m])))

theorem s_perm (w : List ℕ) : (s w).Perm w := sortFuel_perm _ _ le_rfl

theorem s_mem_words {n : ℕ} {w : List ℕ} (h : w ∈ words n) : s w ∈ words n :=
  mem_words.mpr ((s_perm w).trans (mem_words.mp h))

theorem fibre_square_identity (n : ℕ) :
    (∑ w ∈ words n, (fibre n (s w)).card) =
      ∑ y ∈ words n, (fibre n y).card ^ 2 := by
  calc
    _ = ∑ y ∈ words n, ∑ w ∈ (words n).filter (fun w => s w = y),
        (fibre n (s w)).card :=
      (Finset.sum_fiberwise_of_maps_to (fun w hw => s_mem_words hw) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      have he : (∑ w ∈ (words n).filter (fun w => s w = y), (fibre n (s w)).card) =
          ∑ w ∈ fibre n y, (fibre n y).card := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [(Finset.mem_filter.mp hw).2]
      rw [he]
      simp [pow_two]
end StackSort
