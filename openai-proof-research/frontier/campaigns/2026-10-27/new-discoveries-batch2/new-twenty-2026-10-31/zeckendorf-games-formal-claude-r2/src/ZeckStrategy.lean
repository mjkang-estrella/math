/-
  The two deterministic strategies of Section 1.2 of
  Li--Li--Miller--Mizgerd--Sun--Xia--Zhou, "Deterministic Zeckendorf Games".

  Split Smallest: splits from smallest to largest, then adding 1's, then
  combining consecutive indices from smallest to largest.
  Combine Smallest: adding 1's, then combining consecutive indices from smallest
  to largest, then splitting from smallest to largest.
-/
import ZeckBase

open Classical

namespace Zeck

/-- The smallest split index `i ≥ 2` with `a i ≥ 2`, if one exists. -/
noncomputable def smallestSplit (a : Pos) : Option ℕ :=
  if h : ∃ i, legalSplit a i then some (Nat.find h) else none

/-- The smallest combine index `i ≥ 2` with `a (i-1) ≥ 1` and `a i ≥ 1`. -/
noncomputable def smallestCons (a : Pos) : Option ℕ :=
  if h : ∃ i, legalCons a i then some (Nat.find h) else none

lemma smallestSplit_none_iff (a : Pos) :
    smallestSplit a = none ↔ ¬ ∃ i, legalSplit a i := by
  unfold smallestSplit
  by_cases h : ∃ i, legalSplit a i
  · simp [h]
  · simp [h]

lemma smallestCons_none_iff (a : Pos) :
    smallestCons a = none ↔ ¬ ∃ i, legalCons a i := by
  unfold smallestCons
  by_cases h : ∃ i, legalCons a i
  · simp [h]
  · simp [h]

lemma smallestSplit_exists (a : Pos) {i : ℕ} (h : smallestSplit a = some i) :
    ∃ j, legalSplit a j := by
  by_contra hc
  unfold smallestSplit at h
  simp [hc] at h

lemma smallestCons_exists (a : Pos) {i : ℕ} (h : smallestCons a = some i) :
    ∃ j, legalCons a j := by
  by_contra hc
  unfold smallestCons at h
  simp [hc] at h

lemma smallestSplit_some_spec (a : Pos) {i : ℕ} (h : smallestSplit a = some i) :
    legalSplit a i ∧ ∀ j < i, ¬ legalSplit a j := by
  have hex := smallestSplit_exists a h
  have hfi : Nat.find hex = i := by
    unfold smallestSplit at h
    simp only [hex] at h
    simpa using h
  subst hfi
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

lemma smallestCons_some_spec (a : Pos) {i : ℕ} (h : smallestCons a = some i) :
    legalCons a i ∧ ∀ j < i, ¬ legalCons a j := by
  have hex := smallestCons_exists a h
  have hfi : Nat.find hex = i := by
    unfold smallestCons at h
    simp only [hex] at h
    simpa using h
  subst hfi
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

lemma smallestSplit_eq_some_of (a : Pos) (i : ℕ) (h : legalSplit a i)
    (hmin : ∀ j < i, ¬ legalSplit a j) : smallestSplit a = some i := by
  have hex : ∃ j, legalSplit a j := ⟨i, h⟩
  have hle : Nat.find hex ≤ i := Nat.find_min' hex h
  have hge : ¬ Nat.find hex < i := by
    intro hlt
    exact hmin (Nat.find hex) hlt (Nat.find_spec hex)
  have hfi : Nat.find hex = i := by omega
  rw [← hfi]
  unfold smallestSplit
  simp only [hex]
  simp

lemma smallestCons_eq_some_of (a : Pos) (i : ℕ) (h : legalCons a i)
    (hmin : ∀ j < i, ¬ legalCons a j) : smallestCons a = some i := by
  have hex : ∃ j, legalCons a j := ⟨i, h⟩
  have hle : Nat.find hex ≤ i := Nat.find_min' hex h
  have hge : ¬ Nat.find hex < i := by
    intro hlt
    exact hmin (Nat.find hex) hlt (Nat.find_spec hex)
  have hfi : Nat.find hex = i := by omega
  rw [← hfi]
  unfold smallestCons
  simp only [hex]
  simp

/-- Split Smallest: smallest split, then `A1`, then smallest combine. -/
noncomputable def stepSS (a : Pos) : Pos :=
  match smallestSplit a with
  | some i => doSplit a i
  | none =>
    if legalA1 a then doA1 a
    else match smallestCons a with
         | some i => doCons a i
         | none => a

/-- Combine Smallest: `A1`, then smallest combine, then smallest split. -/
noncomputable def stepCS (a : Pos) : Pos :=
  if legalA1 a then doA1 a
  else match smallestCons a with
       | some i => doCons a i
       | none => match smallestSplit a with
                 | some i => doSplit a i
                 | none => a

lemma stepSS_stuck (a : Pos) (h : ¬ hasMove a) : stepSS a = a := by
  have h1 : smallestSplit a = none :=
    (smallestSplit_none_iff a).2 (fun ⟨i, hi⟩ => h (Or.inr (Or.inr ⟨i, hi⟩)))
  have h2 : ¬ legalA1 a := fun ha => h (Or.inl ha)
  have h3 : smallestCons a = none :=
    (smallestCons_none_iff a).2 (fun ⟨i, hi⟩ => h (Or.inr (Or.inl ⟨i, hi⟩)))
  simp [stepSS, h1, h2, h3]

lemma stepCS_stuck (a : Pos) (h : ¬ hasMove a) : stepCS a = a := by
  have h1 : smallestSplit a = none :=
    (smallestSplit_none_iff a).2 (fun ⟨i, hi⟩ => h (Or.inr (Or.inr ⟨i, hi⟩)))
  have h2 : ¬ legalA1 a := fun ha => h (Or.inl ha)
  have h3 : smallestCons a = none :=
    (smallestCons_none_iff a).2 (fun ⟨i, hi⟩ => h (Or.inr (Or.inl ⟨i, hi⟩)))
  simp [stepCS, h1, h2, h3]

lemma stepSS_drop (a : Pos) (h : hasMove a) : M (stepSS a) + 1 ≤ M a := by
  unfold stepSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    exact M_doSplit a i (smallestSplit_some_spec a hsp).1
  | none =>
    dsimp only
    split_ifs with ha1
    · exact M_doA1 a ha1
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        exact M_doCons a i (smallestCons_some_spec a hco).1
      | none =>
        dsimp only
        exfalso
        rcases h with ha | hc | hs
        · exact ha1 ha
        · exact (smallestCons_none_iff a).1 hco hc
        · exact (smallestSplit_none_iff a).1 hsp hs

lemma stepCS_drop (a : Pos) (h : hasMove a) : M (stepCS a) + 1 ≤ M a := by
  unfold stepCS
  split_ifs with ha1
  · exact M_doA1 a ha1
  · cases hco : smallestCons a with
    | some i =>
      dsimp only
      exact M_doCons a i (smallestCons_some_spec a hco).1
    | none =>
      dsimp only
      cases hsp : smallestSplit a with
      | some i =>
        dsimp only
        exact M_doSplit a i (smallestSplit_some_spec a hsp).1
      | none =>
        dsimp only
        exfalso
        rcases h with ha | hc | hs
        · exact ha1 ha
        · exact (smallestCons_none_iff a).1 hco hc
        · exact (smallestSplit_none_iff a).1 hsp hs

lemma stepSS_val (a : Pos) : val (stepSS a) = val a := by
  unfold stepSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    exact val_doSplit a i (smallestSplit_some_spec a hsp).1
  | none =>
    dsimp only
    split_ifs with ha1
    · exact val_doA1 a ha1
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        exact val_doCons a i (smallestCons_some_spec a hco).1
      | none => dsimp only

lemma stepCS_val (a : Pos) : val (stepCS a) = val a := by
  unfold stepCS
  split_ifs with ha1
  · exact val_doA1 a ha1
  · cases hco : smallestCons a with
    | some i =>
      dsimp only
      exact val_doCons a i (smallestCons_some_spec a hco).1
    | none =>
      dsimp only
      cases hsp : smallestSplit a with
      | some i =>
        dsimp only
        exact val_doSplit a i (smallestSplit_some_spec a hsp).1
      | none => dsimp only

lemma stepSS_chips_le (a : Pos) : chips (stepSS a) ≤ chips a := by
  unfold stepSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    exact le_of_eq (chips_doSplit a i (smallestSplit_some_spec a hsp).1)
  | none =>
    dsimp only
    split_ifs with ha1
    · have := chips_doA1 a ha1; omega
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        have := chips_doCons a i (smallestCons_some_spec a hco).1; omega
      | none => dsimp only; exact le_rfl

lemma stepCS_chips_le (a : Pos) : chips (stepCS a) ≤ chips a := by
  unfold stepCS
  split_ifs with ha1
  · have := chips_doA1 a ha1; omega
  · cases hco : smallestCons a with
    | some i =>
      dsimp only
      have := chips_doCons a i (smallestCons_some_spec a hco).1; omega
    | none =>
      dsimp only
      cases hsp : smallestSplit a with
      | some i =>
        dsimp only
        exact le_of_eq (chips_doSplit a i (smallestSplit_some_spec a hsp).1)
      | none => dsimp only; exact le_rfl

/-! ### Runs and the exact number of moves -/

noncomputable def run (step : Pos → Pos) (a : Pos) : ℕ → Pos
  | 0 => a
  | k + 1 => step (run step a k)

lemma run_succ (step : Pos → Pos) (a : Pos) (k : ℕ) :
    run step a (k + 1) = step (run step a k) := rfl

lemma M_run_add (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a)
    (a : Pos) : ∀ k, (∀ j < k, hasMove (run step a j)) → M (run step a k) + k ≤ M a := by
  intro k
  induction k with
  | zero => intro _; simp [run]
  | succ k ih =>
    intro h
    have hk : ∀ j < k, hasMove (run step a j) := fun j hj => h j (by omega)
    have ih' := ih hk
    have hm : hasMove (run step a k) := h k (by omega)
    have hd := hstep (run step a k) hm
    rw [run_succ]
    omega

lemma exists_terminal (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a)
    (a : Pos) : ∃ k, ¬ hasMove (run step a k) := by
  by_contra hcon
  have hall : ∀ k, hasMove (run step a k) := by
    intro k
    by_contra hk
    exact hcon ⟨k, hk⟩
  have h := M_run_add step hstep a (M a + 1) (fun j _ => hall j)
  omega

/-- The exact number of moves of a deterministic play. -/
noncomputable def gameLen (step : Pos → Pos)
    (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a) (a : Pos) : ℕ :=
  Nat.find (exists_terminal step hstep a)

lemma gameLen_spec (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a) (a : Pos) :
    ¬ hasMove (run step a (gameLen step hstep a)) :=
  Nat.find_spec (exists_terminal step hstep a)

lemma gameLen_min (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a) (a : Pos) :
    ∀ j < gameLen step hstep a, hasMove (run step a j) := by
  intro j hj
  by_contra hc
  exact Nat.find_min (exists_terminal step hstep a) hj hc

lemma gameLen_eq_of (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a)
    (a : Pos) (k : ℕ) (hterm : ¬ hasMove (run step a k))
    (hmoves : ∀ j < k, hasMove (run step a j)) : gameLen step hstep a = k := by
  have hspec := gameLen_spec step hstep a
  have hmin := gameLen_min step hstep a
  have hle : gameLen step hstep a ≤ k := by
    by_contra hc
    exact hterm (hmin k (by omega))
  have hge : k ≤ gameLen step hstep a := by
    by_contra hc
    exact hspec (hmoves _ (by omega))
  omega

lemma gameLen_le_M (step : Pos → Pos) (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a)
    (a : Pos) : gameLen step hstep a ≤ M a := by
  have h := M_run_add step hstep a (gameLen step hstep a) (gameLen_min step hstep a)
  omega

/-- The start: `n` copies of `F 1`. -/
noncomputable def start (n : ℕ) : Pos := Finsupp.single 1 n

lemma val_start (n : ℕ) : val (start n) = n := by
  simp [start, val]

lemma chips_start (n : ℕ) : chips (start n) = n := by
  simp [start, chips]

lemma start_zero (n : ℕ) : (start n) 0 = 0 := by
  simp [start]

/-- The actual number of moves of the Split Smallest game from `n` ones. -/
noncomputable def SS (n : ℕ) : ℕ := gameLen stepSS stepSS_drop (start n)

/-- The actual number of moves of the Combine Smallest game from `n` ones. -/
noncomputable def CS (n : ℕ) : ℕ := gameLen stepCS stepCS_drop (start n)

lemma runSS_val (n : ℕ) (k : ℕ) : val (run stepSS (start n) k) = n := by
  induction k with
  | zero => simpa [run] using val_start n
  | succ k ih => rw [run_succ, stepSS_val]; exact ih

lemma runCS_val (n : ℕ) (k : ℕ) : val (run stepCS (start n) k) = n := by
  induction k with
  | zero => simpa [run] using val_start n
  | succ k ih => rw [run_succ, stepCS_val]; exact ih

lemma runSS_chips_le (n : ℕ) (k : ℕ) : chips (run stepSS (start n) k) ≤ n := by
  induction k with
  | zero => simpa [run] using le_of_eq (chips_start n)
  | succ k ih => rw [run_succ]; exact le_trans (stepSS_chips_le _) ih

lemma runCS_chips_le (n : ℕ) (k : ℕ) : chips (run stepCS (start n) k) ≤ n := by
  induction k with
  | zero => simpa [run] using le_of_eq (chips_start n)
  | succ k ih => rw [run_succ]; exact le_trans (stepCS_chips_le _) ih

lemma runSS_idx (n : ℕ) (k : ℕ) (i : ℕ) (hi : 1 ≤ (run stepSS (start n) k) i) :
    i ≤ 2 * Nat.log2 n + 1 :=
  idx_bound _ n (runSS_val n k) i hi

lemma runCS_idx (n : ℕ) (k : ℕ) (i : ℕ) (hi : 1 ≤ (run stepCS (start n) k) i) :
    i ≤ 2 * Nat.log2 n + 1 :=
  idx_bound _ n (runCS_val n k) i hi

/-- When Split Smallest combines, every chip count is at most one. -/
lemma stepSS_cons_le_one (a : Pos) (hsp : smallestSplit a = none) (ha1 : ¬ legalA1 a) :
    ∀ j, 1 ≤ j → a j ≤ 1 := by
  intro j hj
  rcases eq_or_lt_of_le hj with h1 | h2
  · have hj1 : j = 1 := by omega
    subst hj1
    have h : ¬ (2 ≤ a 1) := ha1
    omega
  · by_contra hc
    have hge : 2 ≤ a j := by omega
    exact (smallestSplit_none_iff a).1 hsp ⟨j, by omega, hge⟩

lemma doA1_zero (a : Pos) : doA1 a 0 = a 0 := by
  have h1 : 0 ≠ 1 := by omega
  have h2 : 0 ≠ 2 := by omega
  simp [doA1, Finsupp.update_apply, h1, h2]

lemma doCons_zero (a : Pos) (i : ℕ) (hi : 2 ≤ i) : doCons a i 0 = a 0 := by
  have h1 : 0 ≠ i - 1 := by omega
  have h2 : 0 ≠ i := by omega
  simp [doCons, Finsupp.update_apply, h1, h2]

lemma doSplit2_zero (a : Pos) : doSplit2 a 0 = a 0 := by
  have h1 : 0 ≠ 2 := by omega
  have h2 : 0 ≠ 1 := by omega
  have h3 : 0 ≠ 3 := by omega
  simp [doSplit2, Finsupp.update_apply, h1, h2, h3]

lemma doSplitG_zero (a : Pos) (i : ℕ) (hi : 3 ≤ i) : doSplitG a i 0 = a 0 := by
  have h1 : 0 ≠ i := by omega
  have h2 : 0 ≠ i - 2 := by omega
  simp [doSplitG, Finsupp.update_apply, h1, h2]

lemma doSplit_zero (a : Pos) (i : ℕ) (hi : 2 ≤ i) : doSplit a i 0 = a 0 := by
  unfold doSplit
  split_ifs
  · exact doA1_zero a
  · exact doSplit2_zero a
  · exact doSplitG_zero a i (by omega)

lemma stepSS_zero (a : Pos) (h0 : a 0 = 0) : stepSS a 0 = 0 := by
  unfold stepSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    rw [doSplit_zero a i (smallestSplit_some_spec a hsp).1.1]
    exact h0
  | none =>
    dsimp only
    split_ifs with ha1
    · rw [doA1_zero]; exact h0
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        rw [doCons_zero a i (smallestCons_some_spec a hco).1.1]
        exact h0
      | none => dsimp only; exact h0

lemma stepCS_zero (a : Pos) (h0 : a 0 = 0) : stepCS a 0 = 0 := by
  unfold stepCS
  split_ifs with ha1
  · rw [doA1_zero]; exact h0
  · cases hco : smallestCons a with
    | some i =>
      dsimp only
      rw [doCons_zero a i (smallestCons_some_spec a hco).1.1]
      exact h0
    | none =>
      dsimp only
      cases hsp : smallestSplit a with
      | some i =>
        dsimp only
        rw [doSplit_zero a i (smallestSplit_some_spec a hsp).1.1]
        exact h0
      | none => dsimp only; exact h0

lemma runSS_zero (n : ℕ) (k : ℕ) : (run stepSS (start n) k) 0 = 0 := by
  induction k with
  | zero => simpa [run] using start_zero n
  | succ k ih => rw [run_succ]; exact stepSS_zero _ ih

lemma runCS_zero (n : ℕ) (k : ℕ) : (run stepCS (start n) k) 0 = 0 := by
  induction k with
  | zero => simpa [run] using start_zero n
  | succ k ih => rw [run_succ]; exact stepCS_zero _ ih

/-- A position all of whose positive-index counts are at most one has at most
`2 log₂ n + 2` chips when its value is `n` and no chip sits at index `0`. -/
lemma chips_le_of_all_one (a : Pos) (n : ℕ) (hv : val a = n) (h0 : a 0 = 0)
    (h : ∀ j, 1 ≤ j → a j ≤ 1) : chips a ≤ 2 * Nat.log2 n + 2 := by
  have hsub : a.support ⊆ Finset.range (2 * Nat.log2 n + 2) := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj
    rw [Finset.mem_range]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp [h0] at hj
    · have := idx_bound a n hv j (by omega)
      omega
  have hterm : ∀ j ∈ a.support, a j ≤ 1 := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp [h0] at hj
    · exact h j hpos
  have hsum : chips a = Finset.sum a.support (fun j => a j) := by
    simp [chips, Finsupp.sum]
  have h1 : Finset.sum a.support (fun j => a j) ≤ Finset.sum a.support (fun _ => 1) :=
    Finset.sum_le_sum hterm
  have h2 : Finset.sum a.support (fun _ => (1 : ℕ)) = a.support.card := by simp
  have h3 : a.support.card ≤ (Finset.range (2 * Nat.log2 n + 2)).card :=
    Finset.card_le_card hsub
  have h4 : (Finset.range (2 * Nat.log2 n + 2)).card = 2 * Nat.log2 n + 2 :=
    Finset.card_range _
  omega

end Zeck
