import ChordModel2Counter
namespace Chord.Model2
open Function
attribute [local instance] Classical.propDecidable

/-- Tracing a closed visited set adds precisely the forward orbit. -/
theorem trace_union (f : Nat → Nat) (size i : Nat) (s : List Nat)
    (hf : ∀ j, j < size → f j < size) (hi : i < size)
    (hs : ∀ j ∈ s, j < size) (hn : s.Nodup)
    (hc : ∀ j ∈ s, f j ∈ s) (x : Nat) :
    x ∈ trace f size i s ↔ x ∈ s ∨ ∃ k, (f^[k]) i = x := by
  constructor
  · intro h
    rcases trace_origin f size i x s h with h | ⟨k,_,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k,hk.symm⟩
  · rintro (h | ⟨k,rfl⟩)
    · exact trace_preserves f size i x s h
    · exact trace_contains_iterates f size i s hf hi hs hn hc k

/-- Generic correctness of the ascending scan, for a finite union of cyclic orbits. -/
theorem scan_correct (size : Nat) (f : Nat → Nat) (R : Nat → Nat → Prop)
    (hf : ∀ j, j < size → f j < size)
    (hsymm : ∀ i j, R i j → R j i)
    (htrans : ∀ i j k, R i j → R j k → R i k)
    (hreach : ∀ i, i < size → ∀ j, R i j ↔ ∃ k, (f^[k]) i = j) :
    cycles size f = ((Finset.range size).filter (fun i => ∀ j, R i j → i ≤ j)).card := by
  classical
  let step := fun (s : Nat × List Nat) i =>
    if i ∈ s.2 then s else (s.1+1, trace f size i s.2)
  let state := fun m => (List.range m).foldl step (0,[])
  let minimum := fun i => ∀ j, R i j → i ≤ j
  have inv : ∀ m, m ≤ size →
      (state m).2.Nodup ∧
      (∀ x ∈ (state m).2, x < size) ∧
      (∀ x ∈ (state m).2, f x ∈ (state m).2) ∧
      (∀ x, x ∈ (state m).2 ↔ ∃ j, j < m ∧ R j x) ∧
      (state m).1 = ((Finset.range m).filter minimum).card := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [state, minimum]
    | succ m ih =>
      intro hm
      have hms : m < size := by omega
      obtain ⟨hn,hb,hc,he,hcount⟩ := ih (by omega)
      have hstate : state (m+1) = step (state m) m := by
        simp only [state, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hmin : minimum m ↔ m ∉ (state m).2 := by
        constructor
        · intro h hin
          obtain ⟨j,hj,hjm⟩ := (he m).mp hin
          have := h j (hsymm j m hjm)
          omega
        · intro h j hmj
          by_contra hnle
          have hjm : j < m := by omega
          exact h ((he m).mpr ⟨j,hjm,hsymm m j hmj⟩)
      rw [hstate]
      by_cases hin : m ∈ (state m).2
      · have hmnot : ¬minimum m := by simpa only [hmin, not_not] using hin
        simp only [step, ite_eq_left hin]
        refine ⟨hn,hb,hc,?_,?_⟩
        · intro x
          rw [he x]
          constructor
          · rintro ⟨j,hj,hjx⟩; exact ⟨j,by omega,hjx⟩
          · rintro ⟨j,hj,hjx⟩
            by_cases hjm : j < m
            · exact ⟨j,hjm,hjx⟩
            · have hjm : j = m := by omega
              subst j
              obtain ⟨a,ha,ham⟩ := (he m).mp hin
              exact ⟨a,ha,htrans a m x ham hjx⟩
        · rw [Finset.range_add_one, Finset.filter_insert]
          simp only [hmnot]
          exact hcount
      · have hmmin : minimum m := hmin.mpr hin
        simp only [step, ite_eq_right hin]
        have ht := trace_closed f size size m (state m).2 hf hms hb hn
          (fun j hj => Or.inl (hc j hj)) (by omega)
        refine ⟨trace_nodup f size m _ hn, trace_bounded f size size m _ hf hms hb,
          ht.2, ?_, ?_⟩
        · intro x
          rw [trace_union f size m _ hf hms hb hn hc, he x, ← hreach m hms x]
          constructor
          · rintro (⟨j,hj,hjx⟩ | hmx)
            · exact ⟨j,by omega,hjx⟩
            · exact ⟨m,by omega,hmx⟩
          · rintro ⟨j,hj,hjx⟩
            by_cases hjm : j < m
            · exact Or.inl ⟨j,hjm,hjx⟩
            · have : j = m := by omega
              subst j
              exact Or.inr hjx
        · rw [Finset.range_add_one, Finset.filter_insert]
          simp only [hmmin, ite_eq_left]
          rw [Finset.card_insert_of_notMem (by simp), hcount]
  exact (inv size (by omega)).2.2.2.2
end Chord.Model2
