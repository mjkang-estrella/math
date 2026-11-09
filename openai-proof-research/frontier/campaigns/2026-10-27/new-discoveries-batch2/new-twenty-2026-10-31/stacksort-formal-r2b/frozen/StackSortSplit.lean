import StackSortMap
noncomputable section
namespace StackSort

theorem fuel_independent (k j : ℕ) (w : List ℕ) (hk : w.length ≤ k) (hj : w.length ≤ j) :
    sortFuel k w = sortFuel j w := by
  induction k generalizing j w with
  | zero =>
    have : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    cases j <;> rfl
  | succ k ih =>
    cases j with
    | zero =>
      have : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst w; rfl
    | succ j =>
      cases w with
      | nil => rfl
      | cons x xs =>
        let w := x :: xs
        let m := w.foldr max 0
        let l := w.takeWhile (· != m)
        let r := (w.dropWhile (· != m)).drop 1
        have he : w = l ++ m :: r := split_spec w m (max_mem x xs)
        have hlen := congrArg List.length he
        simp only [List.length_append, List.length_cons, w] at hlen
        simp only [List.length_cons] at hk hj
        change sortFuel k l ++ sortFuel k r ++ [m] = sortFuel j l ++ sortFuel j r ++ [m]
        rw [ih j l (by omega) (by omega), ih j r (by omega) (by omega)]

theorem fold_max_bound (w : List ℕ) (m : ℕ) (h : ∀ x ∈ w, x ≤ m) :
    w.foldr max 0 ≤ m := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

theorem fold_max_split (L R : List ℕ) (m : ℕ)
    (hL : ∀ x ∈ L, x < m) (hR : ∀ x ∈ R, x ≤ m) :
    (L ++ m :: R).foldr max 0 = m := by
  induction L with
  | nil => simpa using max_eq_left (fold_max_bound R m hR)
  | cons x xs ih =>
    simp only [List.cons_append, List.foldr_cons]
    rw [ih (fun y hy => hL y (by simp [hy]))]
    exact max_eq_right (hL x (by simp)).le

/-- The source's defining equation, on distinct words with maximum m. -/
theorem s_split (L R : List ℕ) (m : ℕ)
    (hL : ∀ x ∈ L, x < m) (hR : ∀ x ∈ R, x ≤ m) :
    s (L ++ m :: R) = s L ++ s R ++ [m] := by
  have htake : (L ++ m :: R).takeWhile (· != m) = L := by
    rw [List.takeWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (hL x hx))]
    simp
  have hdrop : (L ++ m :: R).dropWhile (· != m) = m :: R := by
    rw [List.dropWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (hL x hx))]
    simp
  have hne : L ++ m :: R ≠ [] := by simp
  generalize hw : L ++ m :: R = w at *
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    unfold s
    simp only [List.length_cons, sortFuel_succ_cons]
    have hm : (x :: xs).foldr max 0 = m := by rw [← hw]; exact fold_max_split L R m hL hR
    rw [hm, htake, hdrop]
    simp only [List.drop_succ_cons, List.drop_zero]
    have hlen := congrArg List.length hw
    simp only [List.length_append, List.length_cons] at hlen
    rw [fuel_independent xs.length L.length L (by omega) le_rfl,
      fuel_independent xs.length R.length R (by omega) le_rfl]
end StackSort
