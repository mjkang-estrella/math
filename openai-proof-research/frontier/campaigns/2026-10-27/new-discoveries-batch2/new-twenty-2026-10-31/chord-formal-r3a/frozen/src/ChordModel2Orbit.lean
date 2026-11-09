import ChordRemaining
namespace Chord.Model2

/-- Tracing never loses an already visited point. -/
theorem trace_preserves (f : Nat → Nat) (fuel i x : Nat) (s : List Nat)
    (hx : x ∈ s) : x ∈ trace f fuel i s := by
  induction fuel generalizing i s with
  | zero => exact hx
  | succ fuel ih =>
    change x ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s))
    split
    · exact hx
    · exact ih _ _ (List.mem_cons_of_mem _ hx)

/-- Every newly visited point is an iterate of the starting point. -/
theorem trace_origin (f : Nat → Nat) (fuel i x : Nat) (s : List Nat)
    (hx : x ∈ trace f fuel i s) :
    x ∈ s ∨ ∃ k, k < fuel ∧ x = (f^[k]) i := by
  induction fuel generalizing i s with
  | zero => exact Or.inl hx
  | succ fuel ih =>
    change x ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s)) at hx
    split at hx
    · exact Or.inl hx
    · rcases ih _ _ hx with h | ⟨k, hk, he⟩
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, h⟩
        · exact Or.inl h
      · exact Or.inr ⟨k+1, by omega, by simpa [Function.iterate_succ_apply] using he⟩

/-- In particular a map closed on an interval never traces outside it. -/
theorem trace_bounded (f : Nat → Nat) (size fuel i : Nat) (s : List Nat)
    (hf : ∀ j, j < size → f j < size) (hi : i < size)
    (hs : ∀ j ∈ s, j < size) : ∀ j ∈ trace f fuel i s, j < size := by
  induction fuel generalizing i s with
  | zero => exact hs
  | succ fuel ih =>
    change ∀ j ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s)), j < size
    split
    · exact hs
    · exact ih _ _ (hf _ hi) (by intro j hj; rcases List.mem_cons.mp hj with rfl | h; exact hi; exact hs _ h)

theorem trace_nodup (f : Nat → Nat) (fuel i : Nat) (s : List Nat)
    (hs : s.Nodup) : (trace f fuel i s).Nodup := by
  induction fuel generalizing i s with
  | zero => exact hs
  | succ fuel ih =>
    change (if i ∈ s then s else trace f fuel (f i) (i :: s)).Nodup
    split
    · exact hs
    · rename_i hi
      exact ih _ _ (List.nodup_cons.mpr ⟨hi, hs⟩)

/-- With enough fuel, every outgoing edge from the visited set is visited.
The one permitted unclosed edge in the input ends at the current point. -/
theorem trace_closed (f : Nat → Nat) (size fuel i : Nat) (s : List Nat)
    (hf : ∀ j, j < size → f j < size) (hi : i < size)
    (hs : ∀ j ∈ s, j < size) (hn : s.Nodup)
    (hc : ∀ j ∈ s, f j ∈ s ∨ f j = i)
    (hbudget : size ≤ fuel + s.length) :
    i ∈ trace f fuel i s ∧
    ∀ j ∈ trace f fuel i s, f j ∈ trace f fuel i s := by
  induction fuel generalizing i s with
  | zero =>
    have hsub : s.toFinset ⊆ Finset.range size := by
      intro j hj
      exact Finset.mem_range.mpr (hs j (List.mem_toFinset.mp hj))
    have heq : s.toFinset = Finset.range size := by
      apply Finset.eq_of_subset_of_card_le hsub
      simpa only [Finset.card_range, List.toFinset_card_of_nodup hn, Nat.zero_add] using hbudget
    have hall : ∀ j, j < size → j ∈ s := by
      intro j hj
      apply List.mem_toFinset.mp
      rw [heq]
      exact Finset.mem_range.mpr hj
    exact ⟨hall i hi, fun j hj => hall _ (hf j (hs j hj))⟩
  | succ fuel ih =>
    change i ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s)) ∧
      ∀ j ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s)),
        f j ∈ (if i ∈ s then s else trace f fuel (f i) (i :: s))
    by_cases hin : i ∈ s
    · simp only [ite_eq_left hin]
      exact ⟨hin, fun j hj => (hc j hj).elim id (fun h => h ▸ hin)⟩
    · simp only [ite_eq_right hin]
      have hs' : ∀ j ∈ i :: s, j < size := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hs j hj
      have hc' : ∀ j ∈ i :: s, f j ∈ i :: s ∨ f j = f i := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Or.inr rfl
        · rcases hc j hj with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inl (List.mem_cons.mpr (Or.inl h))
      have hrec := ih (f i) (i :: s) (hf i hi) hs'
        (List.nodup_cons.mpr ⟨hin, hn⟩) hc' (by simp only [List.length_cons]; omega)
      exact ⟨trace_preserves f fuel (f i) i (i :: s) (List.mem_cons_self), hrec.2⟩

/-- A full trace saturates the complete forward orbit, not merely a prefix. -/
theorem trace_contains_iterates (f : Nat → Nat) (size i : Nat) (s : List Nat)
    (hf : ∀ j, j < size → f j < size) (hi : i < size)
    (hs : ∀ j ∈ s, j < size) (hn : s.Nodup)
    (hc : ∀ j ∈ s, f j ∈ s) :
    ∀ k, (f^[k]) i ∈ trace f size i s := by
  have ht := trace_closed f size size i s hf hi hs hn
    (fun j hj => Or.inl (hc j hj)) (by omega)
  intro k
  induction k with
  | zero => exact ht.1
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ht.2 _ ih
end Chord.Model2
