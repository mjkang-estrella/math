/-
  Controls for the two deterministic games: small exact values, and the
  literal defect of the MathDB record.

  The record for MathDB 347063 says the game "starts from the Zeckendorf
  decomposition of n".  Under the source's move rules (Definition 1.1 of
  Li--Li--Miller--Mizgerd--Sun--Xia--Zhou) that start would have no legal
  move at all, since a Zeckendorf representation puts at most one chip on
  each index and never on two consecutive indices.  The source starts
  instead at `n` copies of `F 1`, which is what `start` does here.
-/
import ZeckStrategy

open Classical

namespace Zeck

/-! ### Small positions -/

noncomputable def e1 (c : ℕ) : Pos := Finsupp.single 1 c

noncomputable def e2 (c : ℕ) : Pos := Finsupp.single 2 c

noncomputable def e3 (c : ℕ) : Pos := Finsupp.single 3 c

noncomputable def e12 (c1 c2 : ℕ) : Pos := Finsupp.single 1 c1 + Finsupp.single 2 c2

noncomputable def e13 : Pos := Finsupp.single 1 1 + Finsupp.single 3 1

lemma start_eq_e1 (n : ℕ) : start n = e1 n := rfl

lemma e1_apply_self (c : ℕ) : (e1 c) 1 = c := by simp [e1]

lemma e1_apply_ne (c i : ℕ) (h : i ≠ 1) : (e1 c) i = 0 := by simp [e1, h]

lemma e2_apply_self (c : ℕ) : (e2 c) 2 = c := by simp [e2]

lemma e2_apply_ne (c i : ℕ) (h : i ≠ 2) : (e2 c) i = 0 := by simp [e2, h]

lemma e3_apply_self (c : ℕ) : (e3 c) 3 = c := by simp [e3]

lemma e3_apply_ne (c i : ℕ) (h : i ≠ 3) : (e3 c) i = 0 := by simp [e3, h]

lemma e12_apply_1 (c1 c2 : ℕ) : (e12 c1 c2) 1 = c1 := by simp [e12]

lemma e12_apply_2 (c1 c2 : ℕ) : (e12 c1 c2) 2 = c2 := by simp [e12]

lemma e12_apply_ne (c1 c2 i : ℕ) (h1 : i ≠ 1) (h2 : i ≠ 2) : (e12 c1 c2) i = 0 := by
  simp [e12, h1, h2]

lemma e12_zero_left (c : ℕ) : e12 0 c = e2 c := by
  ext i
  simp [e12, e2]

lemma e13_apply_1 : e13 1 = 1 := by simp [e13]

lemma e13_apply_3 : e13 3 = 1 := by simp [e13]

lemma e13_apply_ne (i : ℕ) (h1 : i ≠ 1) (h3 : i ≠ 3) : e13 i = 0 := by
  simp [e13, h1, h3]

/-! ### A sufficient condition for a terminal position -/

lemma noMove_of (a : Pos) (h1 : a 1 ≤ 1) (h2 : ∀ i, 2 ≤ i → a i ≤ 1)
    (h3 : ∀ i, 2 ≤ i → a (i - 1) = 0 ∨ a i = 0) : ¬ hasMove a := by
  rintro (ha | ⟨i, hi⟩ | ⟨i, hi⟩)
  · have h : 2 ≤ a 1 := ha
    omega
  · obtain ⟨hi2, hi1, hi0⟩ := hi
    rcases h3 i hi2 with h | h
    · rw [h] at hi1
      omega
    · rw [h] at hi0
      omega
  · obtain ⟨hi2, hai⟩ := hi
    have := h2 i hi2
    omega

lemma noMove_e2_one : ¬ hasMove (e2 1) := by
  apply noMove_of
  · rw [e2_apply_ne 1 1 (by omega)]
    omega
  · intro i hi
    by_cases h : i = 2
    · subst h; rw [e2_apply_self]
    · rw [e2_apply_ne 1 i h]; omega
  · intro i hi
    by_cases h : i = 2
    · subst h; left; simp [e2]
    · by_cases h3 : i = 3
      · subst h3; right; simp [e2]
      · right; rw [e2_apply_ne 1 i h]

lemma noMove_e3_one : ¬ hasMove (e3 1) := by
  apply noMove_of
  · rw [e3_apply_ne 1 1 (by omega)]
    omega
  · intro i hi
    by_cases h : i = 3
    · subst h; rw [e3_apply_self]
    · rw [e3_apply_ne 1 i h]; omega
  · intro i hi
    by_cases h : i = 2
    · subst h; left; simp [e3]
    · by_cases h3 : i = 3
      · subst h3; left; simp [e3]
      · by_cases h4 : i = 4
        · subst h4; right; simp [e3]
        · right; rw [e3_apply_ne 1 i h3]

lemma noMove_e13 : ¬ hasMove e13 := by
  apply noMove_of
  · rw [e13_apply_1]
  · intro i hi
    by_cases h : i = 3
    · subst h; rw [e13_apply_3]
    · rw [e13_apply_ne i (by omega) h]; omega
  · intro i hi
    by_cases h : i = 2
    · subst h; right; simp [e13]
    · by_cases h3 : i = 3
      · subst h3; left; simp [e13]
      · by_cases h4 : i = 4
        · subst h4; right; simp [e13]
        · right; rw [e13_apply_ne i (by omega) h3]

/-! ### The smallest-move selectors on these positions -/

lemma smallestSplit_start (n : ℕ) : smallestSplit (start n) = none := by
  apply (smallestSplit_none_iff _).2
  rintro ⟨i, hi2, hai⟩
  have h0 : (start n) i = 0 := by
    have hne : i ≠ 1 := by omega
    simp [start, hne]
  omega

lemma smallestCons_start (n : ℕ) : smallestCons (start n) = none := by
  apply (smallestCons_none_iff _).2
  rintro ⟨i, hi2, hi1, hi0⟩
  have h0 : (start n) i = 0 := by
    have hne : i ≠ 1 := by omega
    simp [start, hne]
  omega

lemma legalA1_start (n : ℕ) (hn : 2 ≤ n) : legalA1 (start n) := by
  have h : (start n) 1 = n := by simp [start]
  show 2 ≤ (start n) 1
  omega

lemma legalSplit_e2_2 : legalSplit (e2 2) 2 := by
  refine ⟨le_rfl, ?_⟩
  rw [e2_apply_self]

lemma legalA1_e12_21 : legalA1 (e12 2 1) := by
  have h : (e12 2 1) 1 = 2 := e12_apply_1 2 1
  show 2 ≤ (e12 2 1) 1
  omega

lemma legalCons_e12_11 : legalCons (e12 1 1) 2 := by
  refine ⟨by omega, ?_, ?_⟩
  · show 1 ≤ (e12 1 1) (2 - 1)
    simp [e12]
  · show 1 ≤ (e12 1 1) 2
    rw [e12_apply_2]

lemma smallestSplit_e2_2 : smallestSplit (e2 2) = some 2 := by
  apply smallestSplit_eq_some_of
  · exact legalSplit_e2_2
  · intro j hj
    rintro ⟨hj2, _⟩
    omega

lemma smallestSplit_e12_11 : smallestSplit (e12 1 1) = none := by
  apply (smallestSplit_none_iff _).2
  rintro ⟨i, hi2, hai⟩
  have hle : (e12 1 1) i ≤ 1 := by
    by_cases h1 : i = 1
    · subst h1; omega
    · by_cases h2 : i = 2
      · subst h2; rw [e12_apply_2]
      · rw [e12_apply_ne 1 1 i h1 h2]; omega
  omega

lemma smallestSplit_e12_21 : smallestSplit (e12 2 1) = none := by
  apply (smallestSplit_none_iff _).2
  rintro ⟨i, hi2, hai⟩
  have hle : (e12 2 1) i ≤ 1 := by
    by_cases h1 : i = 1
    · subst h1; omega
    · by_cases h2 : i = 2
      · subst h2; rw [e12_apply_2]
      · rw [e12_apply_ne 2 1 i h1 h2]; omega
  omega

lemma smallestCons_e12_11 : smallestCons (e12 1 1) = some 2 := by
  apply smallestCons_eq_some_of
  · exact legalCons_e12_11
  · intro j hj
    rintro ⟨hj2, _, _⟩
    omega

lemma smallestCons_e2_2 : smallestCons (e2 2) = none := by
  apply (smallestCons_none_iff _).2
  rintro ⟨i, hi2, hi1, hi0⟩
  have hi : i = 2 := by
    by_contra h
    rw [e2_apply_ne 2 i h] at hi0
    omega
  subst hi
  have h1' : (e2 2) (2 - 1) = 0 := by simp [e2]
  omega

lemma not_legalA1_e12_11 : ¬ legalA1 (e12 1 1) := by
  have h : (e12 1 1) 1 = 1 := e12_apply_1 1 1
  show ¬ (2 ≤ (e12 1 1) 1)
  omega

lemma not_legalA1_e2_2 : ¬ legalA1 (e2 2) := by
  have h : (e2 2) 1 = 0 := e2_apply_ne 2 1 (by omega)
  show ¬ (2 ≤ (e2 2) 1)
  omega

/-! ### The move functions on these positions -/

lemma doA1_start (n : ℕ) : doA1 (start n) = e12 (n - 2) 1 := by
  ext i
  simp only [doA1, e12, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply, start]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h2 : i = 2
    · subst h2; simp
    · have e1' : ¬ (1 = i) := fun h => h1 h.symm
      have e2' : ¬ (2 = i) := fun h => h2 h.symm
      simp [h1, h2, e1', e2']

lemma doA1_e12_21 : doA1 (e12 2 1) = e2 2 := by
  ext i
  simp only [doA1, e2, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply, e12]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h2 : i = 2
    · subst h2; simp
    · have e1' : ¬ (1 = i) := fun h => h1 h.symm
      have e2' : ¬ (2 = i) := fun h => h2 h.symm
      simp [h1, h2, e1', e2']

lemma doCons_e12_11 : doCons (e12 1 1) 2 = e3 1 := by
  ext i
  simp only [doCons, e3, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply, e12]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h2 : i = 2
    · subst h2; simp
    · by_cases h3 : i = 3
      · subst h3; simp
      · have e1' : ¬ (1 = i) := fun h => h1 h.symm
        have e2' : ¬ (2 = i) := fun h => h2 h.symm
        have e3' : ¬ (3 = i) := fun h => h3 h.symm
        simp [h1, h2, h3, e1', e2', e3']

lemma doSplit2_e2_2 : doSplit2 (e2 2) = e13 := by
  ext i
  simp only [doSplit2, e13, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply, e2]
  by_cases h1 : i = 1
  · subst h1; simp
  · by_cases h2 : i = 2
    · subst h2; simp
    · by_cases h3 : i = 3
      · subst h3; simp
      · have e1' : ¬ (1 = i) := fun h => h1 h.symm
        have e2' : ¬ (2 = i) := fun h => h2 h.symm
        have e3' : ¬ (3 = i) := fun h => h3 h.symm
        simp [h1, h2, h3, e1', e2', e3']

lemma stepSS_start (n : ℕ) (hn : 2 ≤ n) : stepSS (start n) = e12 (n - 2) 1 := by
  unfold stepSS
  rw [smallestSplit_start]
  dsimp only
  split_ifs with ha1
  · exact doA1_start n
  · exact absurd (legalA1_start n hn) ha1

lemma stepSS_e12_11 : stepSS (e12 1 1) = e3 1 := by
  unfold stepSS
  rw [smallestSplit_e12_11]
  dsimp only
  split_ifs with ha1
  · exact absurd ha1 not_legalA1_e12_11
  · rw [smallestCons_e12_11]
    dsimp only
    exact doCons_e12_11

lemma stepSS_e12_21 : stepSS (e12 2 1) = e2 2 := by
  unfold stepSS
  rw [smallestSplit_e12_21]
  dsimp only
  split_ifs with ha1
  · exact doA1_e12_21
  · exact absurd legalA1_e12_21 ha1

lemma stepSS_e2_2 : stepSS (e2 2) = e13 := by
  unfold stepSS
  rw [smallestSplit_e2_2]
  dsimp only
  simpa [doSplit] using doSplit2_e2_2

lemma stepCS_start (n : ℕ) (hn : 2 ≤ n) : stepCS (start n) = e12 (n - 2) 1 := by
  unfold stepCS
  split_ifs with ha1
  · exact doA1_start n
  · exact absurd (legalA1_start n hn) ha1

lemma stepCS_e12_11 : stepCS (e12 1 1) = e3 1 := by
  unfold stepCS
  split_ifs with ha1
  · exact absurd ha1 not_legalA1_e12_11
  · rw [smallestCons_e12_11]
    dsimp only
    exact doCons_e12_11

lemma stepCS_e12_21 : stepCS (e12 2 1) = e2 2 := by
  unfold stepCS
  split_ifs with ha1
  · exact doA1_e12_21
  · exact absurd legalA1_e12_21 ha1

lemma stepCS_e2_2 : stepCS (e2 2) = e13 := by
  unfold stepCS
  split_ifs with ha1
  · exact absurd ha1 not_legalA1_e2_2
  · rw [smallestCons_e2_2]
    dsimp only
    rw [smallestSplit_e2_2]
    dsimp only
    simpa [doSplit] using doSplit2_e2_2

/-! ### The moves that are available -/

lemma hasMove_start (n : ℕ) (hn : 2 ≤ n) : hasMove (start n) :=
  Or.inl (legalA1_start n hn)

lemma hasMove_e12_11 : hasMove (e12 1 1) :=
  Or.inr (Or.inl ⟨2, legalCons_e12_11⟩)

lemma hasMove_e12_21 : hasMove (e12 2 1) := Or.inl legalA1_e12_21

lemma hasMove_e2_2 : hasMove (e2 2) := Or.inr (Or.inr ⟨2, legalSplit_e2_2⟩)

/-! ### Exact values -/

lemma runSS_one (n : ℕ) (hn : 2 ≤ n) : run stepSS (start n) 1 = e12 (n - 2) 1 := by
  simpa [run] using stepSS_start n hn

lemma runSS_two (n : ℕ) (hn : 2 ≤ n) :
    run stepSS (start n) 2 = stepSS (e12 (n - 2) 1) := by
  simpa [run] using congrArg stepSS (runSS_one n hn)

lemma runSS_3_2 : run stepSS (start 3) 2 = e3 1 := by
  rw [runSS_two 3 (by omega)]
  exact stepSS_e12_11

lemma runSS_4_2 : run stepSS (start 4) 2 = e2 2 := by
  rw [runSS_two 4 (by omega)]
  exact stepSS_e12_21

lemma runSS_4_3 : run stepSS (start 4) 3 = e13 := by
  have h : run stepSS (start 4) 3 = stepSS (run stepSS (start 4) 2) := by simp [run]
  rw [h, runSS_4_2]
  exact stepSS_e2_2

lemma runCS_one (n : ℕ) (hn : 2 ≤ n) : run stepCS (start n) 1 = e12 (n - 2) 1 := by
  simpa [run] using stepCS_start n hn

lemma runCS_two (n : ℕ) (hn : 2 ≤ n) :
    run stepCS (start n) 2 = stepCS (e12 (n - 2) 1) := by
  simpa [run] using congrArg stepCS (runCS_one n hn)

lemma runCS_3_2 : run stepCS (start 3) 2 = e3 1 := by
  rw [runCS_two 3 (by omega)]
  exact stepCS_e12_11

lemma runCS_4_2 : run stepCS (start 4) 2 = e2 2 := by
  rw [runCS_two 4 (by omega)]
  exact stepCS_e12_21

lemma runCS_4_3 : run stepCS (start 4) 3 = e13 := by
  have h : run stepCS (start 4) 3 = stepCS (run stepCS (start 4) 2) := by simp [run]
  rw [h, runCS_4_2]
  exact stepCS_e2_2

lemma SS_two : SS 2 = 1 := by
  have hterm : ¬ hasMove (run stepSS (start 2) 1) := by
    rw [runSS_one 2 (by omega), e12_zero_left 1]
    exact noMove_e2_one
  have hmoves : ∀ j < 1, hasMove (run stepSS (start 2) j) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    change hasMove (start 2)
    exact hasMove_start 2 (by omega)
  exact gameLen_eq_of stepSS stepSS_drop (start 2) 1 hterm hmoves

lemma SS_three : SS 3 = 2 := by
  have hterm : ¬ hasMove (run stepSS (start 3) 2) := by
    rw [runSS_3_2]
    exact noMove_e3_one
  have hmoves : ∀ j < 2, hasMove (run stepSS (start 3) j) := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · change hasMove (start 3)
      exact hasMove_start 3 (by omega)
    · rw [runSS_one 3 (by omega)]
      exact hasMove_e12_11
  exact gameLen_eq_of stepSS stepSS_drop (start 3) 2 hterm hmoves

lemma SS_four : SS 4 = 3 := by
  have hterm : ¬ hasMove (run stepSS (start 4) 3) := by
    rw [runSS_4_3]
    exact noMove_e13
  have hmoves : ∀ j < 3, hasMove (run stepSS (start 4) j) := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · change hasMove (start 4)
      exact hasMove_start 4 (by omega)
    · rw [runSS_one 4 (by omega)]
      exact hasMove_e12_21
    · rw [runSS_4_2]
      exact hasMove_e2_2
  exact gameLen_eq_of stepSS stepSS_drop (start 4) 3 hterm hmoves

lemma CS_two : CS 2 = 1 := by
  have hterm : ¬ hasMove (run stepCS (start 2) 1) := by
    rw [runCS_one 2 (by omega), e12_zero_left 1]
    exact noMove_e2_one
  have hmoves : ∀ j < 1, hasMove (run stepCS (start 2) j) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    change hasMove (start 2)
    exact hasMove_start 2 (by omega)
  exact gameLen_eq_of stepCS stepCS_drop (start 2) 1 hterm hmoves

lemma CS_three : CS 3 = 2 := by
  have hterm : ¬ hasMove (run stepCS (start 3) 2) := by
    rw [runCS_3_2]
    exact noMove_e3_one
  have hmoves : ∀ j < 2, hasMove (run stepCS (start 3) j) := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · change hasMove (start 3)
      exact hasMove_start 3 (by omega)
    · rw [runCS_one 3 (by omega)]
      exact hasMove_e12_11
  exact gameLen_eq_of stepCS stepCS_drop (start 3) 2 hterm hmoves

lemma CS_four : CS 4 = 3 := by
  have hterm : ¬ hasMove (run stepCS (start 4) 3) := by
    rw [runCS_4_3]
    exact noMove_e13
  have hmoves : ∀ j < 3, hasMove (run stepCS (start 4) j) := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · change hasMove (start 4)
      exact hasMove_start 4 (by omega)
    · rw [runCS_one 4 (by omega)]
      exact hasMove_e12_21
    · rw [runCS_4_2]
      exact hasMove_e2_2
  exact gameLen_eq_of stepCS stepCS_drop (start 4) 3 hterm hmoves

/-! ### The literal defect of the MathDB record -/

/-- A position is a Zeckendorf representation when every index carries at most
one chip and no two consecutive indices are both occupied. -/
def ZeckendorfPos (a : Pos) : Prop :=
  (∀ i, a i ≤ 1) ∧ ∀ i, 1 ≤ a i → a (i + 1) = 0

lemma noMove_of_zeckendorf (a : Pos) (h : ZeckendorfPos a) : ¬ hasMove a := by
  obtain ⟨h1, h2⟩ := h
  rintro (ha | ⟨i, hi⟩ | ⟨i, hi⟩)
  · have ha' : 2 ≤ a 1 := ha
    have := h1 1
    omega
  · obtain ⟨hi2, hi1, hi0⟩ := hi
    have hz := h2 (i - 1) hi1
    have he : i - 1 + 1 = i := by omega
    rw [he] at hz
    omega
  · obtain ⟨hi2, hai⟩ := hi
    have := h1 i
    omega

/-- The MathDB record's phrase "starts from the Zeckendorf decomposition of `n`"
is literally wrong: under the source's move rules such a start has no legal
move, hence zero moves.  The source (Definition 1.1) starts at `n` copies of
`F 1`. -/
theorem zeckendorf_start_has_no_move (a : Pos) (h : ZeckendorfPos a) : ¬ hasMove a :=
  noMove_of_zeckendorf a h

lemma gameLen_zero_of_noMove (step : Pos → Pos)
    (hstep : ∀ a, hasMove a → M (step a) + 1 ≤ M a) (a : Pos) (h : ¬ hasMove a) :
    gameLen step hstep a = 0 := by
  apply gameLen_eq_of step hstep a 0
  · simpa [run] using h
  · intro j hj
    omega

/-- A Zeckendorf start has zero Split Smallest moves. -/
theorem SS_zeckendorf_zero (a : Pos) (h : ZeckendorfPos a) :
    gameLen stepSS stepSS_drop a = 0 :=
  gameLen_zero_of_noMove stepSS stepSS_drop a (noMove_of_zeckendorf a h)

/-- A Zeckendorf start has zero Combine Smallest moves. -/
theorem CS_zeckendorf_zero (a : Pos) (h : ZeckendorfPos a) :
    gameLen stepCS stepCS_drop a = 0 :=
  gameLen_zero_of_noMove stepCS stepCS_drop a (noMove_of_zeckendorf a h)

end Zeck
