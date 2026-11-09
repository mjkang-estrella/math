/-
  Part (b) of MathDB 347063: reachability with exact step counts for Combine Smallest,
  and the integer move counter `D`.

  The counter `D a = ∑ a_i * d_i`, `d_i = F_{i-2} - [i even]`, rises by exactly one on every split
  and every even-index combine, and is unchanged by odd-index combines and by `A1`.
-/
import ZeckBound
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-! ### Reachability -/

/-- `Steps a k b`: `k` Combine Smallest moves lead from `a` to `b`. -/
inductive Steps : Pos → ℕ → Pos → Prop
  | refl (a : Pos) : Steps a 0 a
  | head {a : Pos} {k : ℕ} {c : Pos} (hm : hasMove a) (h : Steps (stepCS a) k c) :
      Steps a (k + 1) c

theorem Steps.trans {a b c : Pos} {k l : ℕ} (h₁ : Steps a k b) (h₂ : Steps b l c) :
    Steps a (k + l) c := by
  induction h₁ with
  | refl a => simpa using h₂
  | head hm _ ih =>
    have e : ∀ x : ℕ, x + 1 + l = x + l + 1 := fun x => by omega
    rw [e]
    exact Steps.head hm (ih h₂)

theorem Steps.ofStep {a b c : Pos} {k : ℕ} (hm : hasMove a) (e : stepCS a = b)
    (h : Steps b k c) : Steps a (k + 1) c := by
  subst e
  exact Steps.head hm h

lemma run_succ' (step : Pos → Pos) (a : Pos) (k : ℕ) :
    run step a (k + 1) = run step (step a) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run_succ step a (k + 1), ih, run_succ step (step a) k]

lemma run_add (step : Pos → Pos) (a : Pos) (k t : ℕ) :
    run step a (k + t) = run step (run step a k) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e : k + (t + 1) = (k + t) + 1 := by omega
    rw [e, run_succ, run_succ, ih]

theorem Steps.run_eq {a b : Pos} {k : ℕ} (h : Steps a k b) : run stepCS a k = b := by
  induction h with
  | refl a => rfl
  | head hm _ ih => rw [run_succ']; exact ih

theorem Steps.has {a b : Pos} {k : ℕ} (h : Steps a k b) :
    ∀ j < k, hasMove (run stepCS a j) := by
  induction h with
  | refl a => intro j hj; omega
  | head hm _ ih =>
    intro j hj
    cases j with
    | zero => exact hm
    | succ j =>
      rw [run_succ']
      exact ih j (by omega)

/-- The number of remaining Combine Smallest moves from an arbitrary position. -/
noncomputable def CSfrom (a : Pos) : ℕ := gameLen stepCS stepCS_drop a

lemma CS_eq (n : ℕ) : CS n = CSfrom (start n) := rfl

theorem CSfrom_eq {a b : Pos} {k : ℕ} (h : Steps a k b) : CSfrom a = k + CSfrom b := by
  unfold CSfrom
  apply gameLen_eq_of
  · rw [run_add, h.run_eq]
    exact gameLen_spec stepCS stepCS_drop b
  · intro j hj
    by_cases hjk : j < k
    · exact h.has j hjk
    · have e : j = k + (j - k) := by omega
      rw [e, run_add, h.run_eq]
      exact gameLen_min stepCS stepCS_drop b _ (by omega)

theorem Steps.val_eq {a b : Pos} {k : ℕ} (h : Steps a k b) : val b = val a := by
  induction h with
  | refl a => rfl
  | head hm _ ih => rw [ih, stepCS_val]

/-! ### The potential bound for the remaining moves -/

lemma Phi_stepCS_le (a : Pos) (h : hasMove a) : Phi (stepCS a) ≤ Phi a - 1 := by
  unfold stepCS
  split_ifs with hA
  · rw [Phi_doA1 a hA]
  · cases hco : smallestCons a with
    | some i =>
      dsimp only
      have hl := (smallestCons_some_spec a hco).1
      rw [Phi_doCons a i hl]
      have h2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hl.1
      linarith
    | none =>
      dsimp only
      cases hsp : smallestSplit a with
      | some i =>
        dsimp only
        rw [Phi_doSplit a i (smallestSplit_some_spec a hsp).1]
      | none =>
        dsimp only
        exfalso
        rcases h with ha | hc | hs
        · exact hA ha
        · exact (smallestCons_none_iff a).1 hco hc
        · exact (smallestSplit_none_iff a).1 hsp hs

lemma Phi_run_le (a : Pos) : ∀ j ≤ CSfrom a, Phi (run stepCS a j) + j ≤ Phi a := by
  intro j
  induction j with
  | zero => intro _; simp [run]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hm := gameLen_min stepCS stepCS_drop a j (by unfold CSfrom at hj; omega)
    have h2 := Phi_stepCS_le _ hm
    rw [run_succ]
    push_cast
    linarith

lemma CSfrom_le_Phi (a : Pos) : (CSfrom a : ℝ) ≤ Phi a := by
  have h := Phi_run_le a (CSfrom a) le_rfl
  have h0 := Phi_nonneg (run stepCS a (CSfrom a))
  linarith

/-! ### The move counter -/

/-- The counter weight: `F_{i-2} - [i even]`, with `F (i-2) = fib (i-1)`. -/
def d (i : ℕ) : ℕ := Nat.fib (i - 1) - (if i % 2 = 0 then 1 else 0)

/-- Total move counter of a position. -/
noncomputable def D (a : Pos) : ℕ := a.sum (fun i c => c * d i)

lemma D_add (a b : Pos) : D (a + b) = D a + D b := by
  unfold D
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

lemma D_single (i c : ℕ) : D (single i c) = c * d i := by
  unfold D; simp

lemma val_add (a b : Pos) : val (a + b) = val a + val b := by
  unfold val
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

lemma val_single (i c : ℕ) : val (single i c) = c * F i := by
  unfold val; simp

lemma chips_add (a b : Pos) : chips (a + b) = chips a + chips b := by
  unfold chips
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

lemma chips_single (i c : ℕ) : chips (single i c) = c := by
  unfold chips; simp

lemma Phi_add (a b : Pos) : Phi (a + b) = Phi a + Phi b := by
  unfold Phi
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

lemma Phi_single (i c : ℕ) : Phi (single i c) = (c : ℝ) * w i := by
  unfold Phi; simp

lemma d_odd {i : ℕ} (h : i % 2 = 1) : d i = Nat.fib (i - 1) := by
  have hne : ¬ (i % 2 = 0) := by omega
  unfold d
  simp [hne]

lemma d_even {i : ℕ} (h : i % 2 = 0) (h2 : 2 ≤ i) : d i + 1 = Nat.fib (i - 1) := by
  have hp : 0 < Nat.fib (i - 1) := Nat.fib_pos.2 (by omega)
  have e : (if i % 2 = 0 then 1 else 0 : ℕ) = 1 := by simp [h]
  unfold d
  rw [e]
  omega

/-- Even combine: the counter rises by one. -/
lemma d_cons_even {q : ℕ} (hq : q % 2 = 0) (h2 : 2 ≤ q) : d (q + 1) = d q + d (q - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have h1 : d (m + 2 + 1) = Nat.fib (m + 2) := by
    have := d_odd (i := m + 2 + 1) (by omega)
    simpa using this
  have h2' : d (m + 2) + 1 = Nat.fib (m + 1) := by
    have := d_even (i := m + 2) hq (by omega)
    simpa using this
  have h3 : d (m + 2 - 1) = Nat.fib m := by
    have := d_odd (i := m + 2 - 1) (by omega)
    simpa using this
  rw [h1, h3]
  have hf : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  omega

/-- Odd combine: the counter does not change. -/
lemma d_cons_odd {q : ℕ} (hq : q % 2 = 1) (h3 : 3 ≤ q) : d (q + 1) = d q + d (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have h1 : d (m + 2 + 1) + 1 = Nat.fib (m + 2) := by
    have := d_even (i := m + 2 + 1) (by omega) (by omega)
    simpa using this
  have h2' : d (m + 2) = Nat.fib (m + 1) := by
    have := d_odd (i := m + 2) hq
    simpa using this
  have h3' : d (m + 2 - 1) + 1 = Nat.fib m := by
    have := d_even (i := m + 2 - 1) (by omega) (by omega)
    simpa using this
  rw [h2']
  have hf : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  omega

/-- Even split: the counter rises by one. -/
lemma d_split {q : ℕ} (hq : q % 2 = 0) (h4 : 4 ≤ q) : d (q - 2) + d (q + 1) = 2 * d q + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 4 := ⟨q - 4, by omega⟩
  have h1 : d (m + 4 - 2) + 1 = Nat.fib (m + 1) := by
    have := d_even (i := m + 4 - 2) (by omega) (by omega)
    simpa [show m + 4 - 2 - 1 = m + 1 by omega] using this
  have h2 : d (m + 4 + 1) = Nat.fib (m + 4) := by
    have := d_odd (i := m + 4 + 1) (by omega)
    simpa using this
  have h3 : d (m + 4) + 1 = Nat.fib (m + 3) := by
    have := d_even (i := m + 4) hq (by omega)
    simpa [show m + 4 - 1 = m + 3 by omega] using this
  have f1 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have f2 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  omega

lemma d_split2 : d 1 + d 3 = 2 * d 2 + 1 := by decide

/-! ### Tracked transitions -/

/-- `k` moves from `a` to `b`, the counter rising by exactly `e`. -/
structure Tr (a : Pos) (k e : ℕ) (b : Pos) : Prop where
  st : Steps a k b
  dv : D b = D a + e

theorem Tr.refl (a : Pos) : Tr a 0 0 a := ⟨Steps.refl a, by simp⟩

theorem Tr.trans {a b c : Pos} {k l e f : ℕ} (h₁ : Tr a k e b) (h₂ : Tr b l f c) :
    Tr a (k + l) (e + f) c := by
  refine ⟨h₁.st.trans h₂.st, ?_⟩
  rw [h₂.dv, h₁.dv]
  ring

theorem Tr.ofStep {a b : Pos} {e : ℕ} (hm : hasMove a) (hs : stepCS a = b)
    (hd : D b = D a + e) : Tr a 1 e b :=
  ⟨Steps.ofStep hm hs (Steps.refl b), hd⟩

lemma stepCS_cons (a : Pos) {i : ℕ} (hA : ¬ legalA1 a) (hl : legalCons a i)
    (hmin : ∀ j < i, ¬ legalCons a j) : stepCS a = doCons a i := by
  have h := smallestCons_eq_some_of a i hl hmin
  unfold stepCS
  simp [hA, h]

lemma stepCS_split (a : Pos) {i : ℕ} (hA : ¬ legalA1 a) (hc : ∀ j, ¬ legalCons a j)
    (hl : legalSplit a i) (hmin : ∀ j < i, ¬ legalSplit a j) : stepCS a = doSplit a i := by
  have h1 : smallestCons a = none := (smallestCons_none_iff a).2 (fun ⟨j, hj⟩ => hc j hj)
  have h2 := smallestSplit_eq_some_of a i hl hmin
  unfold stepCS
  simp [hA, h1, h2]

lemma stepCS_A1 (a : Pos) (hA : legalA1 a) : stepCS a = doA1 a := by
  unfold stepCS
  simp [hA]

/-- The combine as an equation on sums of singletons. -/
lemma doCons_add (x : Pos) {i i' : ℕ} (hi : i' + 1 = i) (h2 : 2 ≤ i) :
    doCons (x + single i' 1 + single i 1) i = x + single (i + 1) 1 := by
  subst hi
  ext t
  simp only [doCons, Nat.add_sub_cancel, Finsupp.update_apply, Finsupp.add_apply,
    Finsupp.single_apply]
  have a1 : ∀ m : ℕ, ¬ m = m + 1 + 1 := fun m => by omega
  have a2 : ∀ m : ℕ, ¬ m + 1 + 1 = m := fun m => by omega
  by_cases h1 : t = i' + 1 + 1
  · subst h1; simp [a1, a2]
  · by_cases h3 : t = i' + 1
    · subst h3; simp [a1, a2]
    · by_cases h4 : t = i'
      · subst h4; simp [a1, a2]
      · simp [h1, h3, h4, Ne.symm h1, Ne.symm h3, Ne.symm h4]

/-- The split at an index `≥ 3` as an equation on sums of singletons. -/
lemma doSplitG_add (x : Pos) {i i' : ℕ} (hi : i' + 2 = i) (h3 : 3 ≤ i) :
    doSplitG (x + single i 2) i = x + single i' 1 + single (i + 1) 1 := by
  subst hi
  ext t
  simp only [doSplitG, Nat.add_sub_cancel, Finsupp.update_apply, Finsupp.add_apply,
    Finsupp.single_apply]
  have a1 : ∀ m : ℕ, ¬ m = m + 2 + 1 := fun m => by omega
  have a2 : ∀ m : ℕ, ¬ m + 2 + 1 = m := fun m => by omega
  have a3 : ∀ m : ℕ, ¬ m = m + 2 := fun m => by omega
  have a4 : ∀ m : ℕ, ¬ m + 2 = m := fun m => by omega
  by_cases h1 : t = i' + 2 + 1
  · subst h1; simp [a1, a2, a3, a4]
  · by_cases h2 : t = i' + 2
    · subst h2; simp [a1, a2, a3, a4]
    · by_cases h4 : t = i'
      · subst h4; simp [a1, a2, a3, a4]
      · simp [h1, h2, h4, Ne.symm h1, Ne.symm h2, Ne.symm h4]

lemma doSplit2_add (x : Pos) :
    doSplit2 (x + single 2 2) = x + single 1 1 + single 3 1 := by
  ext t
  simp only [doSplit2, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : t = 3
  · subst h1; simp
  · by_cases h2 : t = 1
    · subst h2; simp
    · by_cases h4 : t = 2
      · subst h4; simp
      · simp [h1, h2, h4, Ne.symm h1, Ne.symm h2, Ne.symm h4]

lemma doA1_add (x : Pos) : doA1 (x + single 1 2) = x + single 2 1 := by
  ext t
  simp only [doA1, Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h2 : t = 2
  · subst h2; simp
  · by_cases h1 : t = 1
    · subst h1; simp
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

end Zeck
