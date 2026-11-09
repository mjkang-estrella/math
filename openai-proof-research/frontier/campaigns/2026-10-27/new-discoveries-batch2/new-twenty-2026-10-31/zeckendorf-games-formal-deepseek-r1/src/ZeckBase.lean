/-
  Zeckendorf games: the literal model.

  Source: R. Li, X. Li, S. J. Miller, C. Mizgerd, C. Sun, D. Xia, Z. Zhou,
  "Deterministic Zeckendorf Games", Fibonacci Quarterly 58(5) (2020), 152--157,
  Definition 1.1 and Section 1.2.

  Indices: F 1 = 1, F 2 = 2, F (i+1) = F i + F (i-1).  A position is a finitely
  supported function `Pos := ℕ →₀ ℕ` with `a i` chips of value `F i`.  The game
  starts at `n` copies of `F 1`, i.e. `single 1 n`.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Zeck

/-- Positions: finitely many chips, `a i` chips of value `F i`. -/
abbrev Pos := ℕ →₀ ℕ

/-- The Fibonacci numbers in the source's indexing. -/
def F (i : ℕ) : ℕ := Nat.fib (i + 1)

@[simp] lemma F_zero : F 0 = 1 := by decide
@[simp] lemma F_one : F 1 = 1 := by decide
@[simp] lemma F_two : F 2 = 2 := by decide
@[simp] lemma F_three : F 3 = 3 := by decide
@[simp] lemma F_four : F 4 = 5 := by decide
@[simp] lemma F_five : F 5 = 8 := by decide
@[simp] lemma F_six : F 6 = 13 := by decide
@[simp] lemma F_seven : F 7 = 21 := by decide
@[simp] lemma F_eight : F 8 = 34 := by decide

lemma F_pos (i : ℕ) : 0 < F i := by
  rw [F]
  exact Nat.fib_pos.2 (by omega)

/-- The recurrence, in the source's indexing (valid for `i ≥ 1`). -/
lemma F_rec {i : ℕ} (hi : 1 ≤ i) : F (i + 1) = F i + F (i - 1) := by
  unfold F
  have h1 : i - 1 + 1 = i := by omega
  rw [h1, show i + 1 + 1 = i + 2 from rfl, Nat.fib_add_two]
  ring

lemma F_mono : Monotone F := fun _ _ hab => Nat.fib_mono (by omega)

/-- `F i ≥ 2 ^ (i/2)`: Fibonacci numbers grow at least like powers of `2`. -/
lemma F_pow_two_mul : ∀ k : ℕ, (1 ≤ k → 2 ^ k ≤ F (2 * k)) ∧ 2 ^ k ≤ F (2 * k + 1) := by
  intro k
  induction k with
  | zero => exact ⟨fun h => absurd h (by omega), by simp⟩
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hk : 2 ^ k ≤ F (2 * k) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · exact ihA hk
    have eA : F (2 * k + 2) = F (2 * k + 1) + F (2 * k) := by
      have h := F_rec (i := 2 * k + 1) (by omega)
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
        show 2 * k + 1 - 1 = 2 * k by omega] at h
      linarith
    have eB : F (2 * k + 3) = F (2 * k + 2) + F (2 * k + 1) := by
      have h := F_rec (i := 2 * k + 2) (by omega)
      rw [show 2 * k + 2 + 1 = 2 * k + 3 by omega,
        show 2 * k + 2 - 1 = 2 * k + 1 by omega] at h
      linarith
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    constructor
    · intro _
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, eA, hpow]
      linarith
    · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, eB, eA, hpow]
      linarith

lemma pow_two_le_F (i : ℕ) (hi : 1 ≤ i) : 2 ^ (i / 2) ≤ F i := by
  have h := F_pow_two_mul (i / 2)
  have hdm := Nat.div_add_mod i 2
  have hlt := Nat.mod_lt i (by norm_num : 0 < 2)
  have hd : 2 * (i / 2) / 2 = i / 2 := Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
  rcases Nat.eq_zero_or_pos (i % 2) with h0 | h0
  · have hi2 : i = 2 * (i / 2) := by omega
    rw [hi2, hd]
    exact h.1 (by omega)
  · have hi2 : i = 2 * (i / 2) + 1 := by omega
    have hd2 : (2 * (i / 2) + 1) / 2 = i / 2 := by omega
    rw [hi2, hd2]
    exact h.2

/-- Split and combine weights used for termination: every legal move lowers
`∑ a i * Wt i` by at least one. -/
def Wt (i : ℕ) : ℕ := if i = 1 then 4 else if i = 2 then 7 else i + 5

@[simp] lemma Wt_one : Wt 1 = 4 := by simp [Wt]
@[simp] lemma Wt_two : Wt 2 = 7 := by simp [Wt]
lemma Wt_of_ge {i : ℕ} (h : 3 ≤ i) : Wt i = i + 5 := by
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  simp [Wt, h1, h2]

lemma Wt_of_ge_two {i : ℕ} (h : 2 ≤ i) : Wt i = i + 5 := by
  rcases eq_or_lt_of_le h with h2 | h3
  · have hi : i = 2 := by omega
    rw [hi]; decide
  · exact Wt_of_ge (by omega)

lemma Wt_add_one {i : ℕ} (h : 2 ≤ i) : Wt (i + 1) = i + 6 := by
  have := Wt_of_ge_two (i := i + 1) (by omega)
  omega

/-- Every combine lowers the measure by at least one. -/
lemma Wt_cons_drop {i : ℕ} (h : 2 ≤ i) : Wt (i + 1) + 1 ≤ Wt (i - 1) + Wt i := by
  rcases eq_or_lt_of_le h with h2 | h3
  · have hi : i = 2 := by omega
    rw [hi]; decide
  · have h1 : Wt (i - 1) = i + 4 := by
      have := Wt_of_ge_two (i := i - 1) (by omega); omega
    have h2' : Wt i = i + 5 := Wt_of_ge (by omega)
    have h3' : Wt (i + 1) = i + 6 := Wt_add_one (by omega)
    omega

/-- Every split lowers the measure by at least one. -/
lemma Wt_split_drop {i : ℕ} (h : 3 ≤ i) : Wt (i - 2) + Wt (i + 1) + 1 ≤ 2 * Wt i := by
  rcases eq_or_lt_of_le h with h3 | h4
  · have hi : i = 3 := by omega
    rw [hi]; decide
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h4) with h4' | h5
    · have hi : i = 4 := by omega
      rw [hi]; decide
    · have h1 : Wt (i - 2) = i + 3 := by
        have := Wt_of_ge (i := i - 2) (by omega); omega
      have h2' : Wt i = i + 5 := Wt_of_ge (by omega)
      have h3' : Wt (i + 1) = i + 6 := Wt_add_one (by omega)
      omega

/-- Total value of a position. -/
def val (a : Pos) : ℕ := a.sum (fun i c => c * F i)

/-- Total number of chips. -/
def chips (a : Pos) : ℕ := a.sum (fun _ c => c)

/-- The termination measure. -/
def M (a : Pos) : ℕ := a.sum (fun i c => c * Wt i)

lemma le_sum_val (a : Pos) (i : ℕ) : a i * F i ≤ val a := by
  have h := Finsupp.single_le_sum (f := a) (g := fun j c => c * F j)
    (fun j m => Nat.zero_le _) i
  have e : (Finsupp.single i (a i)).sum (fun j c => c * F j) = a i * F i := by simp
  unfold val
  rw [e] at h
  exact h

lemma le_chips (a : Pos) (i : ℕ) : a i ≤ chips a := by
  exact Finsupp.single_eval_le_sum (f := a) (g := fun m => m) (by simp)
    (fun m => Nat.zero_le m) i

lemma le_M (a : Pos) (i : ℕ) : a i * Wt i ≤ M a := by
  have h := Finsupp.single_le_sum (f := a) (g := fun j c => c * Wt j)
    (fun j m => Nat.zero_le _) i
  have e : (Finsupp.single i (a i)).sum (fun j c => c * Wt j) = a i * Wt i := by simp
  unfold M
  rw [e] at h
  exact h

lemma sum_update_val (a : Pos) (i v : ℕ) :
    val (a.update i v) + a i * F i = val a + v * F i := by
  unfold val
  exact Finsupp.sum_update_add a i v (fun j c => c * F j) (by intro j; simp)
    (by intro j x y; ring)

lemma sum_update_chips (a : Pos) (i v : ℕ) :
    chips (a.update i v) + a i = chips a + v := by
  unfold chips
  exact Finsupp.sum_update_add a i v (fun _ c => c) (by intro j; simp)
    (by intro j x y; ring)

lemma sum_update_M (a : Pos) (i v : ℕ) :
    M (a.update i v) + a i * Wt i = M a + v * Wt i := by
  unfold M
  exact Finsupp.sum_update_add a i v (fun j c => c * Wt j) (by intro j; simp)
    (by intro j x y; ring)

/-! ### The moves of Definition 1.1 -/

/-- `A1`: `F 1, F 1 → F 2` (adding 1's). -/
def legalA1 (a : Pos) : Prop := 2 ≤ a 1

/-- `Cons i`, `i ≥ 2`: `F (i-1), F i → F (i+1)`. -/
def legalCons (a : Pos) (i : ℕ) : Prop := 2 ≤ i ∧ 1 ≤ a (i - 1) ∧ 1 ≤ a i

/-- `Split i`, `i ≥ 2`: `F i, F i → F (i-2), F (i+1)` (with `i = 2` giving `F 1, F 3`). -/
def legalSplit (a : Pos) (i : ℕ) : Prop := 2 ≤ i ∧ 2 ≤ a i

def hasMove (a : Pos) : Prop := legalA1 a ∨ (∃ i, legalCons a i) ∨ (∃ i, legalSplit a i)

noncomputable def doA1 (a : Pos) : Pos := (a.update 1 (a 1 - 2)).update 2 (a 2 + 1)

noncomputable def doCons (a : Pos) (i : ℕ) : Pos :=
  ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)).update (i + 1) (a (i + 1) + 1)

noncomputable def doSplit2 (a : Pos) : Pos :=
  ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)).update 3 (a 3 + 1)

noncomputable def doSplitG (a : Pos) (i : ℕ) : Pos :=
  ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)).update (i + 1) (a (i + 1) + 1)

noncomputable def doSplit (a : Pos) (i : ℕ) : Pos :=
  if i = 1 then doA1 a else if i = 2 then doSplit2 a else doSplitG a i

/-! ### Value is invariant -/

lemma val_doA1 (a : Pos) (h : legalA1 a) : val (doA1 a) = val a := by
  have ha : 2 ≤ a 1 := h
  have e1 := sum_update_val a 1 (a 1 - 2)
  have e2 := sum_update_val (a.update 1 (a 1 - 2)) 2 (a 2 + 1)
  have h1 : (a.update 1 (a 1 - 2)) 2 = a 2 := by
    have hne : (2 : ℕ) ≠ 1 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  simp only [F_one, F_two, mul_one] at e1 e2
  have hle : a 1 ≤ val a := by
    have := le_sum_val a 1
    simpa using this
  unfold doA1
  omega

lemma val_doCons (a : Pos) (i : ℕ) (h : legalCons a i) : val (doCons a i) = val a := by
  obtain ⟨hi2, hi1, hi0⟩ := h
  have e1 := sum_update_val a (i - 1) (a (i - 1) - 1)
  have e2 := sum_update_val (a.update (i - 1) (a (i - 1) - 1)) i (a i - 1)
  have e3 := sum_update_val ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update (i - 1) (a (i - 1) - 1)) i = a i := by
    have hne : i ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.sub_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  have hrec : F (i + 1) = F i + F (i - 1) := F_rec (by omega)
  have hle1 : a (i - 1) * F (i - 1) ≤ val a := le_sum_val a (i - 1)
  have hle2 : a i * F i ≤ val a := le_sum_val a i
  have hm1 : 1 * F (i - 1) ≤ a (i - 1) * F (i - 1) := Nat.mul_le_mul_right _ hi1
  have hm2 : 1 * F i ≤ a i * F i := Nat.mul_le_mul_right _ hi0
  unfold doCons
  omega

lemma val_doSplit2 (a : Pos) (h : 2 ≤ a 2) : val (doSplit2 a) = val a := by
  have e1 := sum_update_val a 2 (a 2 - 2)
  have e2 := sum_update_val (a.update 2 (a 2 - 2)) 1 (a 1 + 1)
  have e3 := sum_update_val ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 (a 3 + 1)
  have h1 : (a.update 2 (a 2 - 2)) 1 = a 1 := by
    have hne : (1 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 = a 3 := by
    have hne : (3 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  simp only [F_one, F_two, F_three] at e1 e2 e3
  have hle : a 2 * F 2 ≤ val a := le_sum_val a 2
  simp only [F_two] at hle
  unfold doSplit2
  omega

lemma F_two_mul_eq {i : ℕ} (hi : 3 ≤ i) : F (i + 1) + F (i - 2) = 2 * F i := by
  have h1 : F (i + 1) = F i + F (i - 1) := F_rec (by omega)
  have h2 : F i = F (i - 1) + F (i - 2) := by
    have := F_rec (i := i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega, show i - 1 - 1 = i - 2 by omega] at this
  omega

lemma val_doSplitG (a : Pos) (i : ℕ) (hi : 3 ≤ i) (h2 : 2 ≤ a i) : val (doSplitG a i) = val a := by
  have e1 := sum_update_val a i (a i - 2)
  have e2 := sum_update_val (a.update i (a i - 2)) (i - 2) (a (i - 2) + 1)
  have e3 := sum_update_val ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update i (a i - 2)) (i - 2) = a (i - 2) := by
    have hne : i - 2 ≠ i := by omega
    simp [Finsupp.update_apply, hne]
  have h2' : ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 2 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2'] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  have hrec : F (i + 1) + F (i - 2) = 2 * F i := F_two_mul_eq hi
  have hle : a i * F i ≤ val a := le_sum_val a i
  have hm : 2 * F i ≤ a i * F i := Nat.mul_le_mul_right _ h2
  unfold doSplitG
  omega

lemma val_doSplit (a : Pos) (i : ℕ) (h : legalSplit a i) : val (doSplit a i) = val a := by
  obtain ⟨hi, h2⟩ := h
  rcases eq_or_lt_of_le hi with h' | h'
  · have hi2 : i = 2 := by omega
    subst hi2
    have e : doSplit a 2 = doSplit2 a := by simp [doSplit]
    rw [e]
    exact val_doSplit2 a h2
  · have h1 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have e : doSplit a i = doSplitG a i := by simp [doSplit, h1, h3]
    rw [e]
    exact val_doSplitG a i (by omega) h2

/-! ### Chip counts -/

lemma chips_doA1 (a : Pos) (h : legalA1 a) : chips (doA1 a) + 1 = chips a := by
  have ha : 2 ≤ a 1 := h
  have e1 := sum_update_chips a 1 (a 1 - 2)
  have e2 := sum_update_chips (a.update 1 (a 1 - 2)) 2 (a 2 + 1)
  have h1 : (a.update 1 (a 1 - 2)) 2 = a 2 := by
    have hne : (2 : ℕ) ≠ 1 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  have hc : a 1 ≤ chips a := le_chips a 1
  unfold doA1
  omega

lemma chips_doCons (a : Pos) (i : ℕ) (h : legalCons a i) : chips (doCons a i) + 1 = chips a := by
  obtain ⟨hi2, hi1, hi0⟩ := h
  have e1 := sum_update_chips a (i - 1) (a (i - 1) - 1)
  have e2 := sum_update_chips (a.update (i - 1) (a (i - 1) - 1)) i (a i - 1)
  have e3 := sum_update_chips ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update (i - 1) (a (i - 1) - 1)) i = a i := by
    have hne : i ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  have hc : a i ≤ chips (a.update (i - 1) (a (i - 1) - 1)) := by
    rw [← h1]
    exact le_chips _ i
  unfold doCons
  omega

lemma chips_doSplit2 (a : Pos) (h : 2 ≤ a 2) : chips (doSplit2 a) = chips a := by
  have e1 := sum_update_chips a 2 (a 2 - 2)
  have e2 := sum_update_chips (a.update 2 (a 2 - 2)) 1 (a 1 + 1)
  have e3 := sum_update_chips ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 (a 3 + 1)
  have h1 : (a.update 2 (a 2 - 2)) 1 = a 1 := by
    have hne : (1 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 = a 3 := by
    have hne : (3 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  have hc : a 2 ≤ chips a := le_chips a 2
  unfold doSplit2
  omega

lemma chips_doSplitG (a : Pos) (i : ℕ) (hi : 3 ≤ i) (h2 : 2 ≤ a i) : chips (doSplitG a i) = chips a := by
  have e1 := sum_update_chips a i (a i - 2)
  have e2 := sum_update_chips (a.update i (a i - 2)) (i - 2) (a (i - 2) + 1)
  have e3 := sum_update_chips ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update i (a i - 2)) (i - 2) = a (i - 2) := by
    have hne : i - 2 ≠ i := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 2 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  have hc : a i ≤ chips a := le_chips a i
  unfold doSplitG
  omega

lemma chips_doSplit (a : Pos) (i : ℕ) (h : legalSplit a i) : chips (doSplit a i) = chips a := by
  obtain ⟨hi, h2⟩ := h
  rcases eq_or_lt_of_le hi with h' | h'
  · have hi2 : i = 2 := by omega
    subst hi2
    have e : doSplit a 2 = doSplit2 a := by simp [doSplit]
    rw [e]; exact chips_doSplit2 a h2
  · have h1 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have e : doSplit a i = doSplitG a i := by simp [doSplit, h1, h3]
    rw [e]; exact chips_doSplitG a i (by omega) h2

/-! ### The termination measure decreases -/

lemma M_doA1 (a : Pos) (h : legalA1 a) : M (doA1 a) + 1 ≤ M a := by
  have ha : 2 ≤ a 1 := h
  have e1 := sum_update_M a 1 (a 1 - 2)
  have e2 := sum_update_M (a.update 1 (a 1 - 2)) 2 (a 2 + 1)
  have h1 : (a.update 1 (a 1 - 2)) 2 = a 2 := by
    have hne : (2 : ℕ) ≠ 1 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  simp only [Wt_one, Wt_two] at e1 e2
  have hle : a 1 * Wt 1 ≤ M a := le_M a 1
  simp only [Wt_one] at hle
  unfold doA1
  omega

lemma M_doCons (a : Pos) (i : ℕ) (h : legalCons a i) : M (doCons a i) + 1 ≤ M a := by
  obtain ⟨hi2, hi1, hi0⟩ := h
  have e1 := sum_update_M a (i - 1) (a (i - 1) - 1)
  have e2 := sum_update_M (a.update (i - 1) (a (i - 1) - 1)) i (a i - 1)
  have e3 := sum_update_M ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update (i - 1) (a (i - 1) - 1)) i = a i := by
    have hne : i ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.sub_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  have hm1 : 1 * Wt (i - 1) ≤ a (i - 1) * Wt (i - 1) := Nat.mul_le_mul_right _ hi1
  have hm2 : 1 * Wt i ≤ a i * Wt i := Nat.mul_le_mul_right _ hi0
  have hl1 : a (i - 1) * Wt (i - 1) ≤ M a := le_M a (i - 1)
  have hl2 : a i * Wt i ≤ M (a.update (i - 1) (a (i - 1) - 1)) := by
    have := le_M (a.update (i - 1) (a (i - 1) - 1)) i
    rwa [h1] at this
  have hdrop : Wt (i + 1) + 1 ≤ Wt (i - 1) + Wt i := Wt_cons_drop hi2
  unfold doCons
  omega

lemma M_doSplit2 (a : Pos) (h : 2 ≤ a 2) : M (doSplit2 a) + 1 ≤ M a := by
  have e1 := sum_update_M a 2 (a 2 - 2)
  have e2 := sum_update_M (a.update 2 (a 2 - 2)) 1 (a 1 + 1)
  have e3 := sum_update_M ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 (a 3 + 1)
  have h1 : (a.update 2 (a 2 - 2)) 1 = a 1 := by
    have hne : (1 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 = a 3 := by
    have hne : (3 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  simp only [Wt_one, Wt_two] at e1 e2
  have hW3 : Wt 3 = 8 := by decide
  rw [hW3] at e3
  have hle : a 2 * Wt 2 ≤ M a := le_M a 2
  simp only [Wt_two] at hle
  unfold doSplit2
  omega

lemma M_doSplitG (a : Pos) (i : ℕ) (hi : 3 ≤ i) (h2 : 2 ≤ a i) :
    M (doSplitG a i) + 1 ≤ M a := by
  have e1 := sum_update_M a i (a i - 2)
  have e2 := sum_update_M (a.update i (a i - 2)) (i - 2) (a (i - 2) + 1)
  have e3 := sum_update_M ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update i (a i - 2)) (i - 2) = a (i - 2) := by
    have hne : i - 2 ≠ i := by omega
    simp [Finsupp.update_apply, hne]
  have h2b : ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)) (i + 1) = a (i + 1) := by
    have hne : i + 1 ≠ i - 2 := by omega
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  rw [h2b] at e3
  rw [Nat.sub_mul] at e1
  rw [Nat.add_mul, one_mul] at e2
  rw [Nat.add_mul, one_mul] at e3
  have hm : 2 * Wt i ≤ a i * Wt i := Nat.mul_le_mul_right _ h2
  have hl : a i * Wt i ≤ M a := le_M a i
  have hdrop : Wt (i - 2) + Wt (i + 1) + 1 ≤ 2 * Wt i := Wt_split_drop hi
  unfold doSplitG
  omega

lemma M_doSplit (a : Pos) (i : ℕ) (h : legalSplit a i) : M (doSplit a i) + 1 ≤ M a := by
  obtain ⟨hi, h2⟩ := h
  rcases eq_or_lt_of_le hi with h' | h'
  · have hi2 : i = 2 := by omega
    subst hi2
    have e : doSplit a 2 = doSplit2 a := by simp [doSplit]
    rw [e]; exact M_doSplit2 a h2
  · have h1 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have e : doSplit a i = doSplitG a i := by simp [doSplit, h1, h3]
    rw [e]; exact M_doSplitG a i (by omega) h2

/-! ### Terminal positions and the index bound -/

/-- A terminal position has at most one chip of every positive value. -/
lemma terminal_le_one (a : Pos) (h : ¬ hasMove a) {i : ℕ} (hi : 1 ≤ i) : a i ≤ 1 := by
  by_contra hc
  have hge : 2 ≤ a i := by omega
  rcases eq_or_lt_of_le hi with h1 | h2
  · have h1' : i = 1 := by omega
    have : 2 ≤ a 1 := by rw [← h1']; exact hge
    exact h (Or.inl this)
  · exact h (Or.inr (Or.inr ⟨i, by omega, hge⟩))

lemma idx_bound (a : Pos) (n : ℕ) (hv : val a = n) (i : ℕ) (hi : 1 ≤ a i) :
    i ≤ 2 * Nat.log2 n + 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · omega
  · have hFi : F i ≤ n := by
      have h3 := le_sum_val a i
      rw [hv] at h3
      calc F i = 1 * F i := (one_mul _).symm
        _ ≤ a i * F i := Nat.mul_le_mul_right (F i) hi
        _ ≤ n := h3
    have h4 : 2 ^ (i / 2) ≤ n := le_trans (pow_two_le_F i hi1) hFi
    have h5 : i / 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h4
    rw [← Nat.log2_eq_log_two] at h5
    have hdm := Nat.div_add_mod i 2
    have hlt := Nat.mod_lt i (by norm_num : 0 < 2)
    omega

end Zeck
