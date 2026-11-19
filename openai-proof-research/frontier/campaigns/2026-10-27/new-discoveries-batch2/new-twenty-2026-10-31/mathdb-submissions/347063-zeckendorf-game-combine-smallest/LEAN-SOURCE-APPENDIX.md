# Lean source appendix — MathDB 347063, Zeckendorf games (formal lane r2)


Every `.lean` file of `zeckendorf-games-formal-claude-r2/src/`, in dependency (import) order — ties broken alphabetically — reproduced byte for byte. Each file appears under a heading with its file name, inside a ```lean fenced block. The companion script `verify-appendix.py` (same directory) re-extracts each fenced block from this file, checks it equals the corresponding source file byte for byte, checks that every file's imports precede it, and prints the SHA-256 and byte size of each source.


Module dependency (import) order, as realized below:


1. `ZeckBase.lean` — imports: *(no local imports; Mathlib only)*
2. `ZeckStrategy.lean` — imports: `ZeckBase.lean`
3. `ZeckControls.lean` — imports: `ZeckStrategy.lean`
4. `ZeckPotential.lean` — imports: `ZeckControls.lean`
5. `ZeckBound.lean` — imports: `ZeckPotential.lean`
6. `ZeckAudit.lean` — imports: `ZeckBound.lean`
7. `ZeckMoves.lean` — imports: `ZeckBound.lean`
8. `ZeckWindow.lean` — imports: `ZeckMoves.lean`
9. `ZeckLow.lean` — imports: `ZeckWindow.lean`
10. `ZeckMacro.lean` — imports: `ZeckLow.lean`
11. `ZeckExit.lean` — imports: `ZeckMacro.lean`
12. `ZeckLevel.lean` — imports: `ZeckExit.lean`
13. `ZeckConst.lean` — imports: `ZeckLevel.lean`
14. `ZeckRotation.lean` — imports: `ZeckLevel.lean`
15. `ZeckChain.lean` — imports: `ZeckConst.lean`
16. `ZeckCS.lean` — imports: `ZeckChain.lean`
17. `ZeckSS.lean` — imports: `ZeckChain.lean`
18. `ZeckEndpoint.lean` — imports: `ZeckCS.lean`, `ZeckSS.lean`
19. `ZeckAudit2.lean` — imports: `ZeckEndpoint.lean`
20. `ZeckAudit3.lean` — imports: `ZeckEndpoint.lean`, `ZeckRotation.lean`

## `ZeckBase.lean`

```lean
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
```

## `ZeckStrategy.lean`

```lean
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
```

## `ZeckControls.lean`

```lean
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
```

## `ZeckPotential.lean`

```lean
/-
  Part (a) of MathDB 347063: the exact potential.

  With phi = (1 + sqrt 5)/2 and psi = 1/phi = phi - 1, the reviewer's weight is
  w i = i + 2 + psi * (-psi)^i, and -psi = 1 - phi.  Every A1 and every split
  lowers Phi = sum a_i w_i by exactly 1, every Cons i lowers it by exactly i.
-/
import ZeckControls
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

namespace Zeck

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def psi : ℝ := phi - 1

noncomputable def s : ℝ := 1 - phi

noncomputable def w (i : ℕ) : ℝ := (i : ℝ) + 2 + psi * s ^ i

lemma phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma phi_pos : 0 < phi := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma psi_def : psi = phi - 1 := rfl

lemma s_def : s = 1 - phi := rfl

lemma s_sq : s ^ 2 = s + 1 := by
  unfold s
  have := phi_sq
  nlinarith

lemma s_cb : s ^ 3 = 2 * s + 1 := by
  have h := s_sq
  nlinarith

lemma psi_phi : psi * phi = 1 := by
  unfold psi
  have := phi_sq
  nlinarith

lemma psi_one_sub_s : psi * (1 - s) = 1 := by
  unfold psi s
  have := phi_sq
  nlinarith

lemma psi_s_eq : psi * s = psi - 1 := by
  have h := psi_one_sub_s
  nlinarith

lemma psi_s2_eq : psi * s ^ 2 = 2 * psi - 1 := by
  have h := psi_s_eq
  have h2 := s_sq
  calc psi * s ^ 2 = psi * (s + 1) := by rw [h2]
    _ = psi * s + psi := by ring
    _ = (psi - 1) + psi := by rw [h]
    _ = 2 * psi - 1 := by ring

lemma psi_s3_eq : psi * s ^ 3 = 3 * psi - 2 := by
  have h := psi_s_eq
  have h2 := s_cb
  calc psi * s ^ 3 = psi * (2 * s + 1) := by rw [h2]
    _ = 2 * (psi * s) + psi := by ring
    _ = 2 * (psi - 1) + psi := by rw [h]
    _ = 3 * psi - 2 := by ring

lemma w_one : w 1 = phi ^ 2 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

lemma w_two : w 2 = phi ^ 2 + phi := by
  unfold w
  rw [psi_s2_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `A1` lowers the potential by exactly one. -/
lemma w_drop_A1 : 2 * w 1 - w 2 = 1 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq, psi_s2_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `Cons i` lowers the potential by exactly `i`. -/
lemma w_drop_cons (i : ℕ) (hi : 2 ≤ i) : w (i - 1) + w i - w (i + 1) = (i : ℝ) := by
  have h1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (show (1 : ℕ) ≤ i by omega)]
    norm_num
  have h2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hp1 : s ^ (i - 1) * s = s ^ i := by
    rw [← pow_succ]
    congr 1
    omega
  have hp2 : s ^ (i - 1) * s ^ 2 = s ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hz : 1 + s - s ^ 2 = 0 := by
    have := s_sq
    nlinarith
  have hpsi : psi * s ^ (i - 1) + psi * s ^ i - psi * s ^ (i + 1) = 0 := by
    have e : psi * s ^ (i - 1) + psi * s ^ i - psi * s ^ (i + 1)
        = psi * (s ^ (i - 1) * (1 + s - s ^ 2)) := by
      rw [mul_sub, mul_add, mul_one, ← hp1, ← hp2]
      ring
    rw [e, hz]
    simp
  unfold w
  rw [h1, h2]
  linarith [hpsi]

/-- `Split 2` lowers the potential by exactly one. -/
lemma w_drop_split2 : 2 * w 2 - w 1 - w 3 = 1 := by
  unfold w
  simp only [pow_one]
  rw [psi_s_eq, psi_s2_eq, psi_s3_eq]
  norm_num
  nlinarith [psi_def, phi_sq]

/-- `Split i` for `i ≥ 3` lowers the potential by exactly one. -/
lemma w_drop_splitG (i : ℕ) (hi : 3 ≤ i) : 2 * w i - w (i - 2) - w (i + 1) = 1 := by
  have h1 : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have h2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hp1 : s ^ (i - 2) * s ^ 2 = s ^ i := by
    rw [← pow_add]
    congr 1
    omega
  have hp2 : s ^ (i - 2) * s ^ 3 = s ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hz : 2 * s ^ 2 - 1 - s ^ 3 = 0 := by
    have h1 := s_sq
    have h2 := s_cb
    nlinarith
  have hpsi : 2 * (psi * s ^ i) - psi * s ^ (i - 2) - psi * s ^ (i + 1) = 0 := by
    have e1 : psi * s ^ i = psi * s ^ (i - 2) * s ^ 2 := by
      rw [← hp1]; ring
    have e2 : psi * s ^ (i + 1) = psi * s ^ (i - 2) * s ^ 3 := by
      rw [← hp2]; ring
    rw [e1, e2]
    have e3 : 2 * (psi * s ^ (i - 2) * s ^ 2) - psi * s ^ (i - 2) - psi * s ^ (i - 2) * s ^ 3
        = psi * s ^ (i - 2) * (2 * s ^ 2 - 1 - s ^ 3) := by ring
    rw [e3, hz]
    ring
  unfold w
  rw [h1, h2]
  linarith [hpsi]

/-! ### The potential -/

/-- The exact potential `Phi a = sum_i a_i * w i`. -/
noncomputable def Phi (a : Pos) : ℝ := a.sum (fun i c => (c : ℝ) * w i)

lemma sum_update_Phi (a : Pos) (i v : ℕ) :
    Phi (a.update i v) + (a i : ℝ) * w i = Phi a + (v : ℝ) * w i := by
  unfold Phi
  exact Finsupp.sum_update_add a i v (fun j c => (c : ℝ) * w j) (by intro j; simp)
    (by intro j x y; push_cast; ring)

lemma Phi_start (n : ℕ) : Phi (start n) = (n : ℝ) * phi ^ 2 := by
  have h : Phi (start n) = (n : ℝ) * w 1 := by simp [Phi, start]
  rw [h, w_one]

lemma Phi_doA1 (a : Pos) (h : legalA1 a) : Phi (doA1 a) = Phi a - 1 := by
  have ha : 2 ≤ a 1 := h
  have e1 := sum_update_Phi a 1 (a 1 - 2)
  have e2 := sum_update_Phi (a.update 1 (a 1 - 2)) 2 (a 2 + 1)
  have h1 : (a.update 1 (a 1 - 2)) 2 = a 2 := by
    have hne : (2 : ℕ) ≠ 1 := by norm_num
    simp [Finsupp.update_apply, hne]
  rw [h1] at e2
  have hc : ((a 1 - 2 : ℕ) : ℝ) = (a 1 : ℝ) - 2 := by
    rw [Nat.cast_sub ha]; norm_num
  have hc2 : ((a 2 + 1 : ℕ) : ℝ) = (a 2 : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  unfold doA1
  linarith [e1, e2, w_drop_A1]

lemma Phi_doCons (a : Pos) (i : ℕ) (h : legalCons a i) : Phi (doCons a i) = Phi a - (i : ℝ) := by
  obtain ⟨hi2, hi1, hi0⟩ := h
  have e1 := sum_update_Phi a (i - 1) (a (i - 1) - 1)
  have e2 := sum_update_Phi (a.update (i - 1) (a (i - 1) - 1)) i (a i - 1)
  have e3 := sum_update_Phi ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update (i - 1) (a (i - 1) - 1)) i = a i := by
    have hne : i ≠ i - 1 := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update (i - 1) (a (i - 1) - 1)).update i (a i - 1)) (i + 1) = a (i + 1) := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc1 : ((a (i - 1) - 1 : ℕ) : ℝ) = (a (i - 1) : ℝ) - 1 := by
    rw [Nat.cast_sub hi1]; norm_num
  have hc2 : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by
    rw [Nat.cast_sub hi0]; norm_num
  have hc3 : ((a (i + 1) + 1 : ℕ) : ℝ) = (a (i + 1) : ℝ) + 1 := by push_cast; ring
  rw [hc1] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doCons
  linarith [e1, e2, e3, w_drop_cons i hi2]

lemma Phi_doSplit2 (a : Pos) (h : 2 ≤ a 2) : Phi (doSplit2 a) = Phi a - 1 := by
  have e1 := sum_update_Phi a 2 (a 2 - 2)
  have e2 := sum_update_Phi (a.update 2 (a 2 - 2)) 1 (a 1 + 1)
  have e3 := sum_update_Phi ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 (a 3 + 1)
  have h1 : (a.update 2 (a 2 - 2)) 1 = a 1 := by
    have hne : (1 : ℕ) ≠ 2 := by norm_num
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update 2 (a 2 - 2)).update 1 (a 1 + 1)) 3 = a 3 := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc : ((a 2 - 2 : ℕ) : ℝ) = (a 2 : ℝ) - 2 := by
    rw [Nat.cast_sub h]; norm_num
  have hc2 : ((a 1 + 1 : ℕ) : ℝ) = (a 1 : ℝ) + 1 := by push_cast; ring
  have hc3 : ((a 3 + 1 : ℕ) : ℝ) = (a 3 : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doSplit2
  linarith [e1, e2, e3, w_drop_split2]

lemma Phi_doSplitG (a : Pos) (i : ℕ) (hi : 3 ≤ i) (hge : 2 ≤ a i) :
    Phi (doSplitG a i) = Phi a - 1 := by
  have e1 := sum_update_Phi a i (a i - 2)
  have e2 := sum_update_Phi (a.update i (a i - 2)) (i - 2) (a (i - 2) + 1)
  have e3 := sum_update_Phi ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1))
    (i + 1) (a (i + 1) + 1)
  have h1 : (a.update i (a i - 2)) (i - 2) = a (i - 2) := by
    have hne : i - 2 ≠ i := by omega
    simp [Finsupp.update_apply, hne]
  have h2 : ((a.update i (a i - 2)).update (i - 2) (a (i - 2) + 1)) (i + 1) = a (i + 1) := by
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  rw [h1] at e2
  rw [h2] at e3
  have hc : ((a i - 2 : ℕ) : ℝ) = (a i : ℝ) - 2 := by
    rw [Nat.cast_sub hge]; norm_num
  have hc2 : ((a (i - 2) + 1 : ℕ) : ℝ) = (a (i - 2) : ℝ) + 1 := by push_cast; ring
  have hc3 : ((a (i + 1) + 1 : ℕ) : ℝ) = (a (i + 1) : ℝ) + 1 := by push_cast; ring
  rw [hc] at e1
  rw [hc2] at e2
  rw [hc3] at e3
  unfold doSplitG
  linarith [e1, e2, e3, w_drop_splitG i hi]

lemma Phi_doSplit (a : Pos) (i : ℕ) (h : legalSplit a i) : Phi (doSplit a i) = Phi a - 1 := by
  obtain ⟨hi, h2⟩ := h
  rcases eq_or_lt_of_le hi with h' | h'
  · have hi2 : i = 2 := by omega
    subst hi2
    have e : doSplit a 2 = doSplit2 a := by simp [doSplit]
    rw [e]
    exact Phi_doSplit2 a h2
  · have h1 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have e : doSplit a i = doSplitG a i := by simp [doSplit, h1, h3]
    rw [e]
    exact Phi_doSplitG a i (by omega) h2

/-! ### The drop of a Split Smallest step -/

noncomputable def dropSS (a : Pos) : ℕ :=
  match smallestSplit a with
  | some _ => 1
  | none =>
    if legalA1 a then 1
    else match smallestCons a with
         | some i => i
         | none => 0

lemma Phi_stepSS (a : Pos) : Phi (stepSS a) = Phi a - (dropSS a : ℝ) := by
  unfold stepSS dropSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    rw [Phi_doSplit a i (smallestSplit_some_spec a hsp).1]
    norm_num
  | none =>
    dsimp only
    split_ifs with ha1
    · rw [Phi_doA1 a ha1]
      norm_num
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        rw [Phi_doCons a i (smallestCons_some_spec a hco).1]
      | none =>
        dsimp only
        ring

lemma Phi_run (n : ℕ) (k : ℕ) :
    Phi (run stepSS (start n) k) =
      Phi (start n) - Finset.sum (Finset.range k) (fun j => (dropSS (run stepSS (start n) j) : ℝ)) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [run_succ, Phi_stepSS, ih, Finset.sum_range_succ]
    ring

end Zeck
```

## `ZeckBound.lean`

```lean
/-
  Part (a) of MathDB 347063, the exact Split Smallest count.

  Every Phase-1 move (A1 or split) lowers Phi by exactly 1; every Cons i lowers it
  by exactly i >= 2.  Hence the number of moves is at most phi^2 * n, with the gap
  Phi(final) + (extra drops of combining moves).
-/
import ZeckPotential

open Classical

namespace Zeck

lemma phi_gt_one : 1 < phi := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma phi_lt_two : phi < 2 := by
  unfold phi
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma psi_pos : 0 < psi := by
  unfold psi
  linarith [phi_gt_one]

lemma psi_lt_one : psi < 1 := by
  unfold psi
  linarith [phi_lt_two]

lemma abs_s_lt_one : |s| < 1 := by
  unfold s
  rw [abs_lt]
  constructor <;> linarith [phi_gt_one, phi_lt_two]

lemma abs_s_pow_le_one (i : ℕ) : |s ^ i| ≤ 1 := by
  rw [abs_pow]
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h0 : 0 ≤ |s| := abs_nonneg s
    nlinarith [abs_s_lt_one, ih, h0]

lemma w_pos (i : ℕ) : 0 < w i := by
  have hle : |psi * s ^ i| ≤ psi := by
    rw [abs_mul, abs_of_pos psi_pos]
    nlinarith [abs_s_pow_le_one i, psi_pos]
  have h2 : -psi ≤ psi * s ^ i := by
    linarith [neg_abs_le (psi * s ^ i), hle]
  unfold w
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith [psi_lt_one, h2, hi]

lemma Phi_nonneg (a : Pos) : 0 ≤ Phi a := by
  unfold Phi
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (w_pos i)))

/-- A move always drops the potential by at least one. -/
lemma dropSS_ge_one (a : Pos) (h : hasMove a) : 1 ≤ dropSS a := by
  unfold dropSS
  cases hsp : smallestSplit a with
  | some _ => simp
  | none =>
    dsimp only
    split_ifs with ha1
    · simp
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        have h2 : 2 ≤ i := (smallestCons_some_spec a hco).1.1
        omega
      | none =>
        dsimp only
        exfalso
        have hs : ¬ ∃ i, legalSplit a i := (smallestSplit_none_iff a).1 hsp
        have hc : ¬ ∃ i, legalCons a i := (smallestCons_none_iff a).1 hco
        rcases h with hA | hC | hS
        · exact ha1 hA
        · obtain ⟨i, hi⟩ := hC
          exact hc ⟨i, hi⟩
        · obtain ⟨i, hi⟩ := hS
          exact hs ⟨i, hi⟩

lemma SS_move_ge_one (n : ℕ) (j : ℕ) (hj : j < SS n) :
    (1 : ℝ) ≤ (dropSS (run stepSS (start n) j) : ℝ) := by
  have hmove : hasMove (run stepSS (start n) j) := gameLen_min stepSS stepSS_drop (start n) j hj
  exact_mod_cast dropSS_ge_one _ hmove

lemma sum_one_range (k : ℕ) : Finset.sum (Finset.range k) (fun _ => (1 : ℝ)) = (k : ℝ) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The exact Split Smallest identity. -/
lemma SS_eq (n : ℕ) :
    (SS n : ℝ) = phi ^ 2 * n - Phi (run stepSS (start n) (SS n))
      - Finset.sum (Finset.range (SS n))
          (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  have h := Phi_run n (SS n)
  have hstart := Phi_start n
  have h1 := sum_one_range (SS n)
  have hsplit : Finset.sum (Finset.range (SS n))
        (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1)
      = Finset.sum (Finset.range (SS n)) (fun j => (dropSS (run stepSS (start n) j) : ℝ)) - (SS n : ℝ) := by
    rw [Finset.sum_sub_distrib, h1]
  linarith [h, hstart, hsplit]

/-- Every drop is at least one, so the gap is nonnegative. -/
lemma SS_excess_nonneg (n : ℕ) :
    0 ≤ Finset.sum (Finset.range (SS n))
      (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  apply Finset.sum_nonneg
  intro j hj
  have hj' : j < SS n := Finset.mem_range.1 hj
  linarith [SS_move_ge_one n j hj']

/-- Part (a), upper half: `SS n ≤ phi^2 n`. -/
theorem SS_le_phi_sq (n : ℕ) : (SS n : ℝ) ≤ phi ^ 2 * n := by
  have hid := SS_eq n
  have hex := SS_excess_nonneg n
  have hpos := Phi_nonneg (run stepSS (start n) (SS n))
  linarith

/-- The same bound, in the shape used by the reviewer: the deficit from `phi^2 n`
is exactly the final potential plus the extra drops. -/
lemma SS_deficit (n : ℕ) :
    phi ^ 2 * n - (SS n : ℝ) = Phi (run stepSS (start n) (SS n))
      + Finset.sum (Finset.range (SS n))
          (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) := by
  have hid := SS_eq n
  linarith

end Zeck
```

## `ZeckAudit.lean`

```lean
/-
  Axiom audit for the main theorems of MathDB 347063.
  Only propext, Classical.choice and Quot.sound are permitted.
-/
import ZeckBound

#print axioms Zeck.exists_terminal
#print axioms Zeck.gameLen_spec
#print axioms Zeck.gameLen_min
#print axioms Zeck.Phi_stepSS
#print axioms Zeck.Phi_doCons
#print axioms Zeck.Phi_doSplit
#print axioms Zeck.SS_eq
#print axioms Zeck.SS_le_phi_sq
#print axioms Zeck.SS_deficit
#print axioms Zeck.SS_two
#print axioms Zeck.SS_three
#print axioms Zeck.SS_four
#print axioms Zeck.CS_two
#print axioms Zeck.CS_three
#print axioms Zeck.CS_four
#print axioms Zeck.zeckendorf_start_has_no_move
#print axioms Zeck.SS_zeckendorf_zero
#print axioms Zeck.CS_zeckendorf_zero
```

## `ZeckMoves.lean`

```lean
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
```

## `ZeckWindow.lean`

```lean
/-
  Part (b) of MathDB 347063: window positions and the atomic Combine Smallest moves.

  A position is a low part plus six consecutive counts at indices `q+1, …, q+6`.  The pool of the
  level `p = q + 2` sits at index `q+2`.
-/
import ZeckMoves

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- A low part with no two adjacent indices and no pending `A1`. -/
structure LowQ (L : Pos) (t : ℕ) : Prop where
  adj : ∀ i, L i = 0 ∨ L (i + 1) = 0
  one1 : L 1 ≤ 1
  zero : L 0 = 0
  top : ∀ i, t < i → L i = 0

/-- A Zeckendorf low part of top index at most `t`. -/
structure Zk (z : Pos) (t : ℕ) : Prop where
  one : ∀ i, z i ≤ 1
  adj : ∀ i, z i = 0 ∨ z (i + 1) = 0
  zero : z 0 = 0
  top : ∀ i, t < i → z i = 0

lemma Zk.lowQ {z : Pos} {t : ℕ} (h : Zk z t) : LowQ z t :=
  ⟨h.adj, h.one 1, h.zero, h.top⟩

lemma Zk.mono {z : Pos} {t t' : ℕ} (h : Zk z t) (ht : t ≤ t') : Zk z t' :=
  ⟨h.one, h.adj, h.zero, fun i hi => h.top i (by omega)⟩

lemma decompose_at (z : Pos) (i : ℕ) (h : z i = 1) : z = z.update i 0 + single i 1 := by
  ext t
  simp only [Finsupp.update_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : t = i
  · subst h1; simp [h]
  · simp [h1, Ne.symm h1]

lemma Zk.erase {z : Pos} {t : ℕ} (hz : Zk z t) (i t' : ℕ)
    (h : ∀ x, t' < x → x ≠ i → z x = 0) : Zk (z.update i 0) t' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finsupp.update_apply]
    split_ifs
    · omega
    · exact hz.one x
  · intro x
    rw [Finsupp.update_apply, Finsupp.update_apply]
    split_ifs with h1 h2
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hz.adj x
  · rw [Finsupp.update_apply]
    split_ifs
    · rfl
    · exact hz.zero
  · intro x hx
    rw [Finsupp.update_apply]
    split_ifs with h1
    · rfl
    · exact h x hx h1

lemma Zk.addAt {z : Pos} {t t' i : ℕ} (hz : Zk z t) (hi : 1 ≤ i) (h0 : z i = 0)
    (h1 : z (i - 1) = 0) (h2 : z (i + 1) = 0) (ht : t ≤ t') (hit : i ≤ t') :
    Zk (z + single i 1) t' := by
  have ev : ∀ x, (z + single i 1 : Pos) x = z x + (if i = x then 1 else 0) := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [ev]
    have := hz.one x
    by_cases hx : i = x
    · subst hx; simp [h0]
    · simp [hx]; omega
  · intro x
    rw [ev, ev]
    by_cases hx : i = x
    · subst hx
      refine Or.inr ?_
      have : ¬ i = i + 1 := by omega
      simp [this, h2]
    · by_cases hx1 : i = x + 1
      · refine Or.inl ?_
        have e : x = i - 1 := by omega
        rw [e]
        have : ¬ i = i - 1 := by omega
        simp [this, h1]
      · simp only [hx, hx1, ite_false, add_zero]
        exact hz.adj x
  · rw [ev]
    have : ¬ i = 0 := by omega
    simp [this, hz.zero]
  · intro x hx
    rw [ev]
    have hne : ¬ i = x := by omega
    simp [hne]
    exact hz.top x (by omega)

/-! ### Window -/

/-- Six consecutive chip counts at indices `q+1, …, q+6`. -/
noncomputable def W (q c0 c1 c2 c3 c4 c5 : ℕ) : Pos :=
  single (q + 1) c0 + single (q + 2) c1 + single (q + 3) c2 + single (q + 4) c3
    + single (q + 5) c4 + single (q + 6) c5

lemma W_apply (q c0 c1 c2 c3 c4 c5 t : ℕ) :
    W q c0 c1 c2 c3 c4 c5 t =
      (if q + 1 = t then c0 else 0) + (if q + 2 = t then c1 else 0)
      + (if q + 3 = t then c2 else 0) + (if q + 4 = t then c3 else 0)
      + (if q + 5 = t then c4 else 0) + (if q + 6 = t then c5 else 0) := by
  simp only [W, Finsupp.add_apply, Finsupp.single_apply]

lemma W_below {q c0 c1 c2 c3 c4 c5 t : ℕ} (h : t ≤ q) : W q c0 c1 c2 c3 c4 c5 t = 0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_above {q c0 c1 c2 c3 c4 c5 t : ℕ} (h : q + 6 < t) : W q c0 c1 c2 c3 c4 c5 t = 0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at1 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 1) = c0 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at2 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 2) = c1 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at3 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 3) = c2 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at4 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 4) = c3 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at5 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 5) = c4 := by
  rw [W_apply]; split_ifs <;> omega

lemma W_at6 {q c0 c1 c2 c3 c4 c5 : ℕ} : W q c0 c1 c2 c3 c4 c5 (q + 6) = c5 := by
  rw [W_apply]; split_ifs <;> omega

lemma D_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    D (W q c0 c1 c2 c3 c4 c5) = c0 * d (q + 1) + c1 * d (q + 2) + c2 * d (q + 3)
      + c3 * d (q + 4) + c4 * d (q + 5) + c5 * d (q + 6) := by
  simp only [W, D_add, D_single]

lemma val_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    val (W q c0 c1 c2 c3 c4 c5) = c0 * F (q + 1) + c1 * F (q + 2) + c2 * F (q + 3)
      + c3 * F (q + 4) + c4 * F (q + 5) + c5 * F (q + 6) := by
  simp only [W, val_add, val_single]

lemma chips_W (q c0 c1 c2 c3 c4 c5 : ℕ) :
    chips (W q c0 c1 c2 c3 c4 c5) = c0 + c1 + c2 + c3 + c4 + c5 := by
  simp only [W, chips_add, chips_single]

/-- Shifting the window up two indices once the two lowest counts vanish. -/
lemma W_shift (q c2 c3 c4 c5 : ℕ) :
    W q 0 0 c2 c3 c4 c5 = W (q + 2) c2 c3 c4 c5 0 0 := by
  ext t
  simp only [W_apply]
  split_ifs <;> omega

/-! ### Legality helpers -/

lemma legalCons_mk (a : Pos) {i i' : ℕ} (hi : i' + 1 = i) (h2 : 2 ≤ i) (h1 : 1 ≤ a i')
    (h0 : 1 ≤ a i) : legalCons a i := by
  subst hi
  refine ⟨h2, ?_, h0⟩
  simpa using h1

lemma not_cons_of_zero (a : Pos) {i i' : ℕ} (hi : i' + 1 = i) (h : a i' = 0 ∨ a i = 0) :
    ¬ legalCons a i := by
  subst hi
  rintro ⟨_, h1, h0⟩
  have e : i' + 1 - 1 = i' := by omega
  rw [e] at h1
  omega

lemma not_A1 {L : Pos} {q c0 c1 c2 c3 c4 c5 : ℕ} (hL : LowQ L q) (h : 1 ≤ q ∨ c0 ≤ 1) :
    ¬ legalA1 (L + W q c0 c1 c2 c3 c4 c5) := by
  intro hh
  have hh' : 2 ≤ (L + W q c0 c1 c2 c3 c4 c5 : Pos) 1 := hh
  rw [Finsupp.add_apply] at hh'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hL1 : L 1 = 0 := hL.top 1 (by omega)
    have hW : W 0 c0 c1 c2 c3 c4 c5 1 = c0 := by
      rw [W_apply]; split_ifs <;> omega
    rw [hL1, hW] at hh'
    omega
  · rw [W_below (show 1 ≤ q by omega)] at hh'
    have := hL.one1
    omega

lemma not_cons_low {L : Pos} {q : ℕ} (hL : LowQ L q) (c0 c1 c2 c3 c4 c5 : ℕ)
    (h : L q = 0 ∨ c0 = 0) {k : ℕ} (hk : k ≤ q + 1) :
    ¬ legalCons (L + W q c0 c1 c2 c3 c4 c5) k := by
  rintro ⟨hk2, h1, h0⟩
  rw [Finsupp.add_apply] at h1 h0
  rw [W_below (show k - 1 ≤ q by omega)] at h1
  have hadj := hL.adj (k - 1)
  rw [show k - 1 + 1 = k by omega] at hadj
  by_cases hk' : k ≤ q
  · rw [W_below hk'] at h0
    omega
  · have hk1 : k = q + 1 := by omega
    subst hk1
    rw [show q + 1 - 1 = q by omega] at h1
    rw [hL.top (q + 1) (by omega), W_at1] at h0
    omega

/-- All non-adjacency checks for a quiet window. -/
lemma not_cons_quiet {L : Pos} {q : ℕ} (hL : LowQ L q) (c1 c3 c5 : ℕ) (k : ℕ) :
    ¬ legalCons (L + W q 0 c1 0 c3 0 c5) k := by
  by_cases hk : k ≤ q + 1
  · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk
  · have top : ∀ x, q < x → L x = 0 := hL.top
    by_cases hk2 : k = q + 2
    · subst hk2
      refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
      rw [Finsupp.add_apply, W_at1, top _ (by omega)]
    · by_cases hk3 : k = q + 3
      · subst hk3
        refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inr ?_)
        rw [Finsupp.add_apply, W_at3, top _ (by omega)]
      · by_cases hk4 : k = q + 4
        · subst hk4
          refine not_cons_of_zero _ (i' := q + 3) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at3, top _ (by omega)]
        · by_cases hk5 : k = q + 5
          · subst hk5
            refine not_cons_of_zero _ (i' := q + 4) rfl (Or.inr ?_)
            rw [Finsupp.add_apply, W_at5, top _ (by omega)]
          · by_cases hk6 : k = q + 6
            · subst hk6
              refine not_cons_of_zero _ (i' := q + 5) rfl (Or.inl ?_)
              rw [Finsupp.add_apply, W_at5, top _ (by omega)]
            · refine not_cons_of_zero _ (i' := k - 1) (by omega) (Or.inr ?_)
              rw [Finsupp.add_apply, W_above (by omega), top _ (by omega)]

theorem Tr.ofCons {a b : Pos} {i e : ℕ} (hA : ¬ legalA1 a) (hl : legalCons a i)
    (hmin : ∀ j < i, ¬ legalCons a j) (hdo : doCons a i = b) (hd : D b = D a + e) :
    Tr a 1 e b :=
  Tr.ofStep (Or.inr (Or.inl ⟨i, hl⟩)) ((stepCS_cons a hA hl hmin).trans hdo) hd

theorem Tr.ofSplit {a b : Pos} {i e : ℕ} (hA : ¬ legalA1 a) (hc : ∀ j, ¬ legalCons a j)
    (hl : legalSplit a i) (hmin : ∀ j < i, ¬ legalSplit a j) (hdo : doSplit a i = b)
    (hd : D b = D a + e) : Tr a 1 e b :=
  Tr.ofStep (Or.inr (Or.inr ⟨i, hl⟩)) ((stepCS_split a hA hc hl hmin).trans hdo) hd

theorem Tr.ofA1 {a b : Pos} {e : ℕ} (hA : legalA1 a) (hdo : doA1 a = b)
    (hd : D b = D a + e) : Tr a 1 e b :=
  Tr.ofStep (Or.inl hA) ((stepCS_A1 a hA).trans hdo) hd

/-! ### The four window combines -/

/-- `C_p`: the chip at `p-1` meets the pool. Counter `+1`. -/
lemma Tr_Cp {L : Pos} {q : ℕ} (hL : LowQ L q) (hL0 : L q = 0) (hq : q % 2 = 0)
    (c0 c1 c2 c3 c4 c5 : ℕ) (hA : 1 ≤ q ∨ c0 = 0) :
    Tr (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) 1 1 (L + W q c0 c1 (c2 + 1) c3 c4 c5) := by
  have hl : legalCons (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) (q + 2) := by
    refine legalCons_mk _ (i' := q + 1) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at1]; omega
    · rw [Finsupp.add_apply, W_at2]; omega
  have hmin : ∀ k < q + 2, ¬ legalCons (L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5) k := by
    intro k hk
    exact not_cons_low hL _ _ _ _ _ _ (Or.inl hL0) (by omega)
  refine Tr.ofCons (not_A1 hL ?_) hl hmin ?_ ?_
  · rcases hA with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · have e : L + W q (c0 + 1) (c1 + 1) c2 c3 c4 c5
        = (L + W q c0 c1 c2 c3 c4 c5) + single (q + 1) 1 + single (q + 2) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q c0 c1 c2 c3 c4 c5) (i := q + 2) (i' := q + 1) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 2 + 1 = q + 3 from rfl]
    abel
  · have hd : d (q + 3) = d (q + 2) + d (q + 1) + 1 := by
      have := d_cons_even (q := q + 2) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+1}`: the output combine. Counter unchanged. -/
lemma Tr_Cp1 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c1 c2 c3 c4 c5 : ℕ) :
    Tr (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) 1 0 (L + W q 0 c1 c2 (c3 + 1) c4 c5) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) (q + 3) := by
    refine legalCons_mk _ (i' := q + 2) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at2]; omega
    · rw [Finsupp.add_apply, W_at3]; omega
  have hmin : ∀ k < q + 3, ¬ legalCons (L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · have e : k = q + 2 := by omega
      subst e
      refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
      rw [Finsupp.add_apply, W_at1, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 (c1 + 1) (c2 + 1) c3 c4 c5
        = (L + W q 0 c1 c2 c3 c4 c5) + single (q + 2) 1 + single (q + 3) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 c1 c2 c3 c4 c5) (i := q + 3) (i' := q + 2) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 3 + 1 = q + 4 from rfl]
    abel
  · have hd : d (q + 4) = d (q + 3) + d (q + 2) := by
      have := d_cons_odd (q := q + 3) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+2}`: the chip at `p+1` meets the output pile. Counter `+1`. -/
lemma Tr_Cp2 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c2 c3 c4 c5 : ℕ) :
    Tr (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) 1 1 (L + W q 0 0 c2 c3 (c4 + 1) c5) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) (q + 4) := by
    refine legalCons_mk _ (i' := q + 3) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at3]; omega
    · rw [Finsupp.add_apply, W_at4]; omega
  have hmin : ∀ k < q + 4, ¬ legalCons (L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · by_cases hk2 : k = q + 2
      · subst hk2
        refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at1, top _ (by omega)]
      · have e : k = q + 3 := by omega
        subst e
        refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at2, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 0 (c2 + 1) (c3 + 1) c4 c5
        = (L + W q 0 0 c2 c3 c4 c5) + single (q + 3) 1 + single (q + 4) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 0 c2 c3 c4 c5) (i := q + 4) (i' := q + 3) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 4 + 1 = q + 5 from rfl]
    abel
  · have hd : d (q + 5) = d (q + 4) + d (q + 3) + 1 := by
      have := d_cons_even (q := q + 4) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

/-- `C_{p+3}`: the second output combine. Counter unchanged. -/
lemma Tr_Cp3 {L : Pos} {q : ℕ} (hL : LowQ L q) (hq : q % 2 = 0)
    (c3 c4 c5 : ℕ) :
    Tr (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) 1 0 (L + W q 0 0 0 c3 c4 (c5 + 1)) := by
  have top : ∀ x, q < x → L x = 0 := hL.top
  have hl : legalCons (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) (q + 5) := by
    refine legalCons_mk _ (i' := q + 4) rfl (by omega) ?_ ?_
    · rw [Finsupp.add_apply, W_at4]; omega
    · rw [Finsupp.add_apply, W_at5]; omega
  have hmin : ∀ k < q + 5, ¬ legalCons (L + W q 0 0 0 (c3 + 1) (c4 + 1) c5) k := by
    intro k hk
    by_cases hk' : k ≤ q + 1
    · exact not_cons_low hL _ _ _ _ _ _ (Or.inr rfl) hk'
    · by_cases hk2 : k = q + 2
      · subst hk2
        refine not_cons_of_zero _ (i' := q + 1) rfl (Or.inl ?_)
        rw [Finsupp.add_apply, W_at1, top _ (by omega)]
      · by_cases hk3 : k = q + 3
        · subst hk3
          refine not_cons_of_zero _ (i' := q + 2) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at2, top _ (by omega)]
        · have e : k = q + 4 := by omega
          subst e
          refine not_cons_of_zero _ (i' := q + 3) rfl (Or.inl ?_)
          rw [Finsupp.add_apply, W_at3, top _ (by omega)]
  refine Tr.ofCons (not_A1 hL (Or.inr (by omega))) hl hmin ?_ ?_
  · have e : L + W q 0 0 0 (c3 + 1) (c4 + 1) c5
        = (L + W q 0 0 0 c3 c4 c5) + single (q + 4) 1 + single (q + 5) 1 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e, doCons_add (L + W q 0 0 0 c3 c4 c5) (i := q + 5) (i' := q + 4) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 5 + 1 = q + 6 from rfl]
    abel
  · have hd : d (q + 6) = d (q + 5) + d (q + 4) := by
      have := d_cons_odd (q := q + 5) (by omega) (by omega)
      simpa using this
    rw [D_add, D_add, D_W, D_W, hd]
    ring

end Zeck
```

## `ZeckLow.lean`

```lean
/-
  Part (b) of MathDB 347063: the split at the pool, low moves, the insertion cascade.
-/
import ZeckWindow

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- `S_p` for `p = q + 2 ≥ 4`. -/
lemma Tr_Sp {z : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 2 = 0) (hz : Zk z q) (c1 c3 : ℕ) :
    Tr (z + W q 0 (c1 + 2) 0 c3 0 0) 1 1 (z + single q 1 + W q 0 c1 1 c3 0 0) := by
  have hL := hz.lowQ
  have hl : legalSplit (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2) := by
    refine ⟨by omega, ?_⟩
    rw [Finsupp.add_apply, W_at2]; omega
  have hmin : ∀ k < q + 2, ¬ legalSplit (z + W q 0 (c1 + 2) 0 c3 0 0) k := by
    rintro k hk ⟨_, h2⟩
    rw [Finsupp.add_apply] at h2
    by_cases hk' : k ≤ q
    · rw [W_below hk'] at h2
      have := hz.one k
      omega
    · have e : k = q + 1 := by omega
      subst e
      rw [W_at1, hz.top _ (by omega)] at h2
      omega
  refine Tr.ofSplit (not_A1 hL (Or.inl (by omega))) (not_cons_quiet hL _ _ _) hl hmin ?_ ?_
  · have e0 : doSplit (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2)
        = doSplitG (z + W q 0 (c1 + 2) 0 c3 0 0) (q + 2) := by
      have h1 : q + 2 ≠ 1 := by omega
      have h2 : q + 2 ≠ 2 := by omega
      simp [doSplit, h1, h2, show q ≠ 0 by omega]
    have e : z + W q 0 (c1 + 2) 0 c3 0 0 = (z + W q 0 c1 0 c3 0 0) + single (q + 2) 2 := by
      simp only [W, Finsupp.single_add]
      abel
    rw [e0, e, doSplitG_add (z + W q 0 c1 0 c3 0 0) (i := q + 2) (i' := q) rfl (by omega)]
    simp only [W, Finsupp.single_add, show q + 2 + 1 = q + 3 from rfl, Finsupp.single_zero,
      add_zero]
    abel
  · have hd : d q + d (q + 3) = 2 * d (q + 2) + 1 := by
      have := d_split (q := q + 2) (by omega) (by omega)
      simpa using this
    simp only [D_add, D_W, D_single]
    nlinarith [hd]

/-- `S_2`, the first split of level `p = 2`. -/
lemma Tr_S2 (c1 c3 : ℕ) :
    Tr (0 + W 0 0 (c1 + 2) 0 c3 0 0) 1 1 (0 + W 0 1 c1 1 c3 0 0) := by
  have hL : LowQ (0 : Pos) 0 := ⟨fun i => Or.inl rfl, by simp, by simp, fun _ _ => rfl⟩
  have h2 : W 0 0 (c1 + 2) 0 c3 0 0 2 = c1 + 2 := by
    rw [W_apply]; split_ifs <;> omega
  have h1 : W 0 0 (c1 + 2) 0 c3 0 0 1 = 0 := by
    rw [W_apply]; split_ifs <;> omega
  have hl : legalSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) 2 := by
    refine ⟨le_refl 2, ?_⟩
    rw [Finsupp.add_apply, h2]; simp
  have hmin : ∀ k < 2, ¬ legalSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) k := by
    rintro k hk ⟨h2', _⟩
    omega
  refine Tr.ofSplit (not_A1 hL (Or.inr (by omega))) (not_cons_quiet hL _ _ _) hl hmin ?_ ?_
  · have e0 : doSplit (0 + W 0 0 (c1 + 2) 0 c3 0 0) 2
        = doSplit2 (0 + W 0 0 (c1 + 2) 0 c3 0 0) := by simp [doSplit]
    have e : (0 : Pos) + W 0 0 (c1 + 2) 0 c3 0 0 = W 0 0 c1 0 c3 0 0 + single 2 2 := by
      simp only [W, zero_add, Finsupp.single_add]
      abel
    rw [e0, e, doSplit2_add]
    simp only [W, zero_add, Finsupp.single_add, Finsupp.single_zero, add_zero]
    abel
  · have hd := d_split2
    simp only [D_add, D_W, D_single, zero_add]
    nlinarith [hd]

/-- `A1`, the first phase. -/
lemma Tr_A1 (c0 c1 c2 c3 c4 c5 : ℕ) :
    Tr (W 0 (c0 + 2) c1 c2 c3 c4 c5) 1 0 (W 0 c0 (c1 + 1) c2 c3 c4 c5) := by
  have h1 : W 0 (c0 + 2) c1 c2 c3 c4 c5 1 = c0 + 2 := by
    rw [W_apply]; split_ifs <;> omega
  have hA : legalA1 (W 0 (c0 + 2) c1 c2 c3 c4 c5) := by
    show 2 ≤ W 0 (c0 + 2) c1 c2 c3 c4 c5 1
    rw [h1]; omega
  refine Tr.ofA1 hA ?_ ?_
  · have e : W 0 (c0 + 2) c1 c2 c3 c4 c5 = W 0 c0 c1 c2 c3 c4 c5 + single 1 2 := by
      simp only [W, zero_add, Finsupp.single_add]
      abel
    rw [e, doA1_add]
    simp only [W, zero_add, Finsupp.single_add]
    abel
  · have d1 : d 1 = 0 := by decide
    have d2 : d 2 = 0 := by decide
    simp only [D_W, zero_add, d1, d2]
    ring

/-! ### Low moves -/

/-- A combine in the low state. -/
lemma Tr_low_cons {z H : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 2 = 0) (hz : Zk z q)
    (h1 : z (q - 1) = 1) (hH : ∀ i, i ≤ q → H i = 0) :
    Tr (z + single q 1 + H) 1 1 (z.update (q - 1) 0 + single (q + 1) 1 + H) := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single q 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single q 1 + H : Pos) 1 := h
    rw [ev, hH 1 (by omega)] at h'
    have h3 := hz.one 1
    have hne : ¬ q = 1 := by omega
    simp [hne] at h'
    omega
  have hl : legalCons (z + single q 1 + H) q := by
    refine ⟨hq2, ?_, ?_⟩
    · rw [ev, h1]; omega
    · rw [ev]
      simp
      omega
  have hmin : ∀ j < q, ¬ legalCons (z + single q 1 + H) j := by
    rintro j hj ⟨hj2, h3, h4⟩
    rw [ev, hH (j - 1) (by omega)] at h3
    rw [ev, hH j (by omega)] at h4
    have hadj := hz.adj (j - 1)
    rw [show j - 1 + 1 = j by omega] at hadj
    have hne1 : ¬ q = j - 1 := by omega
    have hne2 : ¬ q = j := by omega
    simp [hne1] at h3
    simp [hne2] at h4
    omega
  refine Tr.ofCons hA hl hmin ?_ ?_
  · have e : z + single q 1 + H
        = (z.update (q - 1) 0 + H) + single (q - 1) 1 + single q 1 := by
      conv_lhs => rw [decompose_at z (q - 1) h1]
      abel
    rw [e, doCons_add (z.update (q - 1) 0 + H) (i := q) (i' := q - 1) (by omega) hq2]
    abel
  · have hDz : D z = D (z.update (q - 1) 0) + d (q - 1) := by
      conv_lhs => rw [decompose_at z (q - 1) h1]
      rw [D_add, D_single, one_mul]
    have hd := d_cons_even hq hq2
    simp only [D_add, D_single]
    omega

/-- When `z q = 1`, adjacency only occurs among `H` if at all. -/
lemma not_cons_splitpos {z H : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hz : Zk z q) (h1 : z q = 1)
    (hH0 : ∀ i, i ≤ q + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) (k : ℕ) :
    ¬ legalCons (z + single q 1 + H) k := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  rintro ⟨hk2, h3, h4⟩
  rw [ev] at h3 h4
  have hzq1 : z (q - 1) = 0 := by
    have := hz.adj (q - 1)
    rw [show q - 1 + 1 = q by omega] at this
    omega
  by_cases hk : k < q
  · rw [hH0 (k - 1) (by omega)] at h3
    rw [hH0 k (by omega)] at h4
    have hne1 : ¬ q = k - 1 := by omega
    have hne2 : ¬ q = k := by omega
    simp [hne1] at h3
    simp [hne2] at h4
    have ha := hz.adj (k - 1)
    rw [show k - 1 + 1 = k by omega] at ha
    omega
  · by_cases hk1 : k = q
    · subst hk1
      rw [hH0 (k - 1) (by omega), hzq1] at h3
      have hne1 : ¬ k = k - 1 := by omega
      simp [hne1] at h3
    · by_cases hk2' : k = q + 1
      · subst hk2'
        rw [hH0 (q + 1) (by omega), hz.top (q + 1) (by omega)] at h4
        have hne : ¬ q = q + 1 := by omega
        simp [hne] at h4
      · by_cases hk3 : k = q + 2
        · subst hk3
          rw [show q + 2 - 1 = q + 1 by omega, hH0 (q + 1) (by omega),
            hz.top (q + 1) (by omega)] at h3
          have hne : ¬ q = q + 1 := by omega
          simp [hne] at h3
        · rw [hz.top (k - 1) (by omega)] at h3
          rw [hz.top k (by omega)] at h4
          have hne1 : ¬ q = k - 1 := by omega
          have hne2 : ¬ q = k := by omega
          simp [hne1] at h3
          simp [hne2] at h4
          have ha := hadj (k - 1)
          rw [show k - 1 + 1 = k by omega] at ha
          omega

/-- A split in the low state, at an index `≥ 4`. -/
lemma Tr_low_split {z H : Pos} {q : ℕ} (hq4 : 4 ≤ q) (hq : q % 2 = 0) (hz : Zk z q)
    (h1 : z q = 1) (hH0 : ∀ i, i ≤ q + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) :
    Tr (z + single q 1 + H) 1 1 (z.update q 0 + single (q - 2) 1 + single (q + 1) 1 + H) := by
  have ev : ∀ x, (z + single q 1 + H : Pos) x = z x + (if q = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single q 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single q 1 + H : Pos) 1 := h
    rw [ev, hH0 1 (by omega)] at h'
    have h3 := hz.one 1
    have hne : ¬ q = 1 := by omega
    simp [hne] at h'
    omega
  have hl : legalSplit (z + single q 1 + H) q := by
    refine ⟨by omega, ?_⟩
    rw [ev, h1]
    simp
  have hmin : ∀ j < q, ¬ legalSplit (z + single q 1 + H) j := by
    rintro j hj ⟨hj2, h3⟩
    rw [ev, hH0 j (by omega)] at h3
    have hne : ¬ q = j := by omega
    simp [hne] at h3
    have := hz.one j
    omega
  refine Tr.ofSplit hA (not_cons_splitpos (by omega) hz h1 hH0 hadj) hl hmin ?_ ?_
  · have e0 : doSplit (z + single q 1 + H) q = doSplitG (z + single q 1 + H) q := by
      have h1 : q ≠ 1 := by omega
      have h2 : q ≠ 2 := by omega
      simp [doSplit, h1, h2]
    have e2 : (single q 2 : Pos) = single q 1 + single q 1 := Finsupp.single_add q 1 1
    have e : z + single q 1 + H = (z.update q 0 + H) + single q 2 := by
      rw [e2]
      conv_lhs => rw [decompose_at z q h1]
      abel
    rw [e0, e, doSplitG_add (z.update q 0 + H) (i := q) (i' := q - 2) (by omega) (by omega)]
    abel
  · have hDz : D z = D (z.update q 0) + d q := by
      conv_lhs => rw [decompose_at z q h1]
      rw [D_add, D_single, one_mul]
    have hd := d_split hq hq4
    simp only [D_add, D_single]
    omega

/-- `S_2` in the low state. -/
lemma Tr_low_split2 {z H : Pos} (hz : Zk z 2) (h1 : z 2 = 1)
    (hH0 : ∀ i, i ≤ 2 + 1 → H i = 0) (hadj : ∀ i, H i = 0 ∨ H (i + 1) = 0) :
    Tr (z + single 2 1 + H) 1 1 (z.update 2 0 + single 1 1 + single 3 1 + H) := by
  have ev : ∀ x, (z + single 2 1 + H : Pos) x = z x + (if 2 = x then 1 else 0) + H x := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  have hA : ¬ legalA1 (z + single 2 1 + H) := by
    intro h
    have h' : 2 ≤ (z + single 2 1 + H : Pos) 1 := h
    rw [ev, hH0 1 (by omega)] at h'
    have h3 := hz.one 1
    norm_num at h'
    omega
  have hl : legalSplit (z + single 2 1 + H) 2 := by
    refine ⟨le_refl 2, ?_⟩
    rw [ev, h1]
    simp
  have hmin : ∀ j < 2, ¬ legalSplit (z + single 2 1 + H) j := by
    rintro j hj ⟨hj2, _⟩
    omega
  refine Tr.ofSplit hA (not_cons_splitpos (le_refl 2) hz h1 hH0 hadj) hl hmin ?_ ?_
  · have e0 : doSplit (z + single 2 1 + H) 2 = doSplit2 (z + single 2 1 + H) := by simp [doSplit]
    have e2 : (single 2 2 : Pos) = single 2 1 + single 2 1 := Finsupp.single_add 2 1 1
    have e : z + single 2 1 + H = (z.update 2 0 + H) + single 2 2 := by
      rw [e2]
      conv_lhs => rw [decompose_at z 2 h1]
      abel
    rw [e0, e, doSplit2_add]
    abel
  · have hDz : D z = D (z.update 2 0) + d 2 := by
      conv_lhs => rw [decompose_at z 2 h1]
      rw [D_add, D_single, one_mul]
    have hd := d_split2
    simp only [D_add, D_single]
    omega

/-! ### The quiet insertion cascade -/

/-- The high part is out of reach of the insertion at `q`. -/
structure Inert (H : Pos) (q : ℕ) : Prop where
  low : ∀ i, i ≤ q + 2 → H i = 0
  adj : ∀ i, H i = 0 ∨ H (i + 1) = 0

lemma Inert.zero1 {H : Pos} {q : ℕ} (h : Inert H q) : ∀ i, i ≤ q + 1 → H i = 0 :=
  fun i hi => h.low i (by omega)

/-- Insertion of one chip at the even index `q` in a Zeckendorf low state, with a frozen
high part. All moves are even-index moves, so the counter records every move. -/
theorem cascade : ∀ (q : ℕ), q % 2 = 0 → 2 ≤ q → ∀ (z H : Pos), Zk z q → Inert H q →
    ∃ z' k, Zk z' (q + 1) ∧ Tr (z + single q 1 + H) k k (z' + H) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hq2 z H hz hH
    by_cases hz1 : z q = 1
    · -- Case (iii): a repeat at `q`.
      have hq1 : z (q - 1) = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      by_cases hq3 : q = 2
      · subst hq3
        have h2 := Tr_low_split2 hz hz1 hH.zero1 hH.adj
        refine ⟨z.update 2 0 + single 1 1 + single 3 1, 1, ?_, h2⟩
        have ha : Zk (z.update 2 0) 0 := by
          refine hz.erase 2 0 ?_
          intro x hx hx2
          have hx3 : x = 1 ∨ 3 ≤ x := by omega
          rcases hx3 with rfl | hx3
          · exact hq1
          · exact hz.top x (by omega)
        have hb : Zk (z.update 2 0 + single 1 1) 2 := by
          refine ha.addAt (le_refl 1) ?_ ?_ ?_ (by omega) (by omega)
          · exact ha.top 1 (by omega)
          · exact ha.zero
          · exact ha.top 2 (by omega)
        refine hb.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl 3)
        · exact hb.top 3 (by omega)
        · simp [Finsupp.add_apply, Finsupp.single_apply, Finsupp.update_apply]
        · exact hb.top 4 (by omega)
      · have hq4 : 4 ≤ q := by omega
        have ha : Zk (z.update q 0) (q - 2) := by
          refine hz.erase q (q - 2) ?_
          intro x hx hx2
          have hx3 : x = q - 1 ∨ q < x := by omega
          rcases hx3 with rfl | hx3
          · exact hq1
          · exact hz.top x hx3
        have hH' : Inert (single (q + 1) 1 + H) (q - 2) := by
          constructor
          · intro i hi
            have hne : ¬ q + 1 = i := by omega
            rw [Finsupp.add_apply, hH.low i (by omega)]
            simp [Finsupp.single_apply, hne]
          · intro i
            by_cases h1 : i = q + 1
            · subst h1
              refine Or.inr ?_
              have hne : ¬ q + 1 = q + 1 + 1 := by omega
              rw [Finsupp.add_apply, hH.low (q + 1 + 1) (by omega)]
              simp [Finsupp.single_apply, hne]
            · by_cases h2 : i = q
              · subst h2
                refine Or.inl ?_
                have hne : ¬ i + 1 = i := by omega
                rw [Finsupp.add_apply, hH.low i (by omega)]
                simp [Finsupp.single_apply, hne]
              · have hne1 : ¬ q + 1 = i := by omega
                have hne2 : ¬ q + 1 = i + 1 := by omega
                simp only [Finsupp.add_apply, Finsupp.single_apply, hne1, hne2, ite_false,
                  zero_add]
                exact hH.adj i
        obtain ⟨z'', k, hz'', hTr⟩ := ih (q - 2) (by omega) (by omega) (by omega) _ _ ha hH'
        refine ⟨z'' + single (q + 1) 1, 1 + k, ?_, ?_⟩
        · refine hz''.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
          · exact hz''.top _ (by omega)
          · exact hz''.top _ (by omega)
          · exact hz''.top _ (by omega)
        · have h1' := Tr_low_split hq4 hq hz hz1 hH.zero1 hH.adj
          have e : z.update q 0 + single (q - 2) 1 + single (q + 1) 1 + H
              = z.update q 0 + single (q - 2) 1 + (single (q + 1) 1 + H) := by abel
          rw [e] at h1'
          have h2' := h1'.trans hTr
          have e2 : z'' + (single (q + 1) 1 + H) = z'' + single (q + 1) 1 + H := by abel
          rw [e2] at h2'
          exact h2'
    · have hz0 : z q = 0 := by
        have := hz.one q
        omega
      by_cases h1 : z (q - 1) = 1
      · -- Case (ii): the combine at `q` fires.
        have h2 := Tr_low_cons hq2 hq hz h1 (fun i hi => hH.low i (by omega))
        refine ⟨z.update (q - 1) 0 + single (q + 1) 1, 1, ?_, h2⟩
        have ha : Zk (z.update (q - 1) 0) q := by
          refine hz.erase (q - 1) q ?_
          intro x hx _
          exact hz.top x hx
        refine ha.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
        · have hne : q + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
        · rw [show q + 1 - 1 = q by omega]
          have hne : q ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne, hz0]
        · have hne : q + 1 + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
      · -- Case (i): nothing to do.
        have h0 : z (q - 1) = 0 := by
          have := hz.one (q - 1)
          omega
        refine ⟨z + single q 1, 0, ?_, Tr.refl _⟩
        exact hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (by omega) (by omega)

/-- The window with no pending low interaction is inert for lower insertions. -/
lemma W_quiet_adj (q c1 c3 c5 x : ℕ) :
    W q 0 c1 0 c3 0 c5 x = 0 ∨ W q 0 c1 0 c3 0 c5 (x + 1) = 0 := by
  by_cases h2 : x = q + 2
  · subst h2
    exact Or.inr W_at3
  · by_cases h4 : x = q + 4
    · subst h4
      exact Or.inr W_at5
    · by_cases h6 : x = q + 6
      · subst h6
        exact Or.inr (W_above (by omega))
      · refine Or.inl ?_
        rw [W_apply]
        split_ifs <;> omega

lemma Inert_W {q' q : ℕ} (h : q' + 2 ≤ q) (c1 c3 c5 : ℕ) : Inert (W q 0 c1 0 c3 0 c5) q' :=
  ⟨fun i hi => W_below (by omega), fun x => W_quiet_adj q c1 c3 c5 x⟩

lemma Inert_W0 (q c3 c5 : ℕ) : Inert (W q 0 0 0 c3 0 c5) q := by
  constructor
  · intro i hi
    by_cases h : i ≤ q
    · exact W_below h
    · have e : i = q + 1 ∨ i = q + 2 := by omega
      rcases e with rfl | rfl
      · exact W_at1
      · exact W_at2
  · intro x
    exact W_quiet_adj q 0 c3 c5 x

/-- A chip added at `q` to a Zeckendorf part keeps non-adjacency when `z (q-1) = 0`. -/
lemma Zk.lowQ_add {z : Pos} {q : ℕ} (hq2 : 2 ≤ q) (hz : Zk z q) (h1 : z (q - 1) = 0) :
    LowQ (z + single q 1) q := by
  have ev : ∀ x, (z + single q 1 : Pos) x = z x + (if q = x then 1 else 0) := by
    intro x
    simp [Finsupp.add_apply, Finsupp.single_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [ev, ev]
    by_cases hx : x = q
    · subst hx
      refine Or.inr ?_
      have hne : ¬ x = x + 1 := by omega
      simp [hne, hz.top (x + 1) (by omega)]
    · by_cases hx2 : x + 1 = q
      · refine Or.inl ?_
        have e : x = q - 1 := by omega
        rw [e]
        have hne : ¬ q = q - 1 := by omega
        simp [hne, h1]
      · have hne1 : ¬ q = x := by omega
        have hne2 : ¬ q = x + 1 := by omega
        simp only [hne1, hne2, ite_false, add_zero]
        exact hz.adj x
  · rw [ev]
    have hne : ¬ q = 1 := by omega
    simp [hne, hz.one 1]
  · rw [ev]
    have hne : ¬ q = 0 := by omega
    simp [hne, hz.zero]
  · intro x hx
    rw [ev]
    have hne : ¬ q = x := by omega
    simp [hne, hz.top x hx]

lemma LowQ.mono {L : Pos} {t t' : ℕ} (h : LowQ L t) (ht : t ≤ t') : LowQ L t' :=
  ⟨h.adj, h.one1, h.zero, fun i hi => h.top i (by omega)⟩

/-- A pending high transition around a low insertion at `q`. -/
theorem pending {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) {y H0 H1 : Pos} {r e : ℕ}
    (hy : Zk y q) (hH1 : Inert H1 q) (hH0 : ∀ i, i ≤ q → H0 i = 0)
    (hhigh : ∀ L, LowQ L (q + 1) → Tr (L + H0) r e (L + H1)) :
    ∃ z' k', Zk z' (q + 1) ∧ Tr (y + single q 1 + H0) (k' + r) (k' + e) (z' + H1) := by
  by_cases h1 : y (q - 1) = 1
  · have hy0 : y q = 0 := by
      have := hy.adj (q - 1)
      rw [show q - 1 + 1 = q by omega] at this
      omega
    have h2 := Tr_low_cons hq2 hq hy h1 hH0
    have hz' : Zk (y.update (q - 1) 0 + single (q + 1) 1) (q + 1) := by
      have ha : Zk (y.update (q - 1) 0) q :=
        hy.erase (q - 1) q (fun x hx _ => hy.top x hx)
      refine ha.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
      · have hne : q + 1 ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne]
        exact hy.top _ (by omega)
      · rw [show q + 1 - 1 = q by omega]
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hy0]
      · have hne : q + 1 + 1 ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne]
        exact hy.top _ (by omega)
    have h3 := hhigh _ hz'.lowQ
    exact ⟨_, 1, hz', h2.trans h3⟩
  · have h0 : y (q - 1) = 0 := by
      have := hy.one (q - 1)
      omega
    have h3 := hhigh (y + single q 1) ((hy.lowQ_add hq2 h0).mono (by omega))
    obtain ⟨z', k, hz', h4⟩ := cascade q hq hq2 y H1 hy hH1
    refine ⟨z', k, hz', ?_⟩
    have h5 := h3.trans h4
    rwa [Nat.add_comm r, Nat.add_comm e] at h5

end Zeck
```

## `ZeckMacro.lean`

```lean
/-
  Part (b) of MathDB 347063: the READY state and the macro step of the rotation.

  `B z q m h` has a Zeckendorf low state `z` of top index at most `q`, a pool of `m` chips at
  index `p = q + 2` and `h` chips at `p + 2`.  Every macro step sends the low value
  `L = val z` to the rotation `L + F_{p-2} mod F_{p-1}`, the counter records it exactly,
  and the output pile records the odd combines.
-/
import ZeckLow

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- The READY state at level `p = q + 2`. -/
noncomputable def B (z : Pos) (q m h : ℕ) : Pos := z + W q 0 m 0 h 0 0

lemma reshape_c0 (L : Pos) (q c1 c2 c3 c4 c5 : ℕ) :
    L + single (q + 1) 1 + W q 0 c1 c2 c3 c4 c5 = L + W q 1 c1 c2 c3 c4 c5 := by
  simp only [W, Finsupp.single_zero]
  abel

lemma W_le1 {q c1 c2 c3 c4 c5 i : ℕ} (hi : i ≤ q + 1) : W q 0 c1 c2 c3 c4 c5 i = 0 := by
  rw [W_apply]
  split_ifs <;> omega

lemma Zk_zero' (t : ℕ) : Zk (0 : Pos) t :=
  ⟨fun _ => by simp, fun _ => by simp, by simp, fun _ _ => by simp⟩

lemma Zk_zero {z : Pos} (h : Zk z 0) : z = 0 := by
  ext i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using h.zero
  · simpa using h.top i hi

lemma Zk.single {i t : ℕ} (hi : 1 ≤ i) (ht : i ≤ t) : Zk (single i 1 : Pos) t := by
  have h := (Zk_zero' t).addAt (i := i) (t' := t) hi (by simp) (by simp) (by simp) (le_refl _) ht
  simpa using h

lemma high_m5 {L : Pos} {q : ℕ} (hq : q % 2 = 0) (hq1 : 1 ≤ q) (hL : LowQ L q) (hL0 : L q = 0)
    (m h : ℕ) :
    Tr (L + W q 1 (m + 2) 0 h 0 0) 2 1 (L + W q 0 m 0 (h + 1) 0 0) := by
  have s1 : Tr (L + W q 1 (m + 2) 0 h 0 0) 1 1 (L + W q 0 (m + 1) 1 h 0 0) :=
    Tr_Cp hL hL0 hq 0 (m + 1) 0 h 0 0 (Or.inl hq1)
  have s2 : Tr (L + W q 0 (m + 1) 1 h 0 0) 1 0 (L + W q 0 m 0 (h + 1) 0 0) :=
    Tr_Cp1 hL hq m 0 h 0 0
  exact s1.trans s2

/-- The macro step at level `p = q + 2 ≥ 4`. -/
theorem macro_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      ((m' = m + 2 ∧ h' = h + 1 ∧ k = e + 1) ∨ (m' = m ∧ h' = h + 2 ∧ k = e + 2)) := by
  have s1 : Tr (B z q (m + 5) h) 1 1 (z + single q 1 + W q 0 (m + 3) 1 h 0 0) :=
    Tr_Sp hq2 hq hz (m + 3) h
  by_cases h1 : z (q - 1) = 1
  · -- Case 2: `C_{p-2}` creates the chip at `p-1`.
    have hq0 : z q = 0 := by
      have := hz.adj (q - 1)
      rw [show q - 1 + 1 = q by omega] at this
      omega
    have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
    have hL0 : (z.update (q - 1) 0) q = 0 := by
      have hne : q ≠ q - 1 := by omega
      simp [Finsupp.update_apply, hne, hq0]
    have s2 := Tr_low_cons (H := W q 0 (m + 3) 1 h 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
    rw [reshape_c0] at s2
    have s3 : Tr (z.update (q - 1) 0 + W q 1 (m + 3) 1 h 0 0) 1 1
        (z.update (q - 1) 0 + W q 0 (m + 2) 2 h 0 0) :=
      Tr_Cp hz1.lowQ hL0 hq 0 (m + 2) 1 h 0 0 (Or.inl (by omega))
    have s4 : Tr (z.update (q - 1) 0 + W q 0 (m + 2) 2 h 0 0) 1 0
        (z.update (q - 1) 0 + W q 0 (m + 1) 1 (h + 1) 0 0) :=
      Tr_Cp1 hz1.lowQ hq (m + 1) 1 h 0 0
    have s5 : Tr (z.update (q - 1) 0 + W q 0 (m + 1) 1 (h + 1) 0 0) 1 0
        (z.update (q - 1) 0 + W q 0 m 0 (h + 2) 0 0) :=
      Tr_Cp1 hz1.lowQ hq m 0 (h + 1) 0 0
    exact ⟨z.update (q - 1) 0, 5, 3, m, h + 2, hz1, ((((s1.trans s2).trans s3).trans s4).trans s5),
      Or.inr ⟨rfl, rfl, rfl⟩⟩
  · have h0 : z (q - 1) = 0 := by
      have := hz.one (q - 1)
      omega
    have hLq : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
    have s2 : Tr (z + single q 1 + W q 0 (m + 3) 1 h 0 0) 1 0
        (z + single q 1 + W q 0 (m + 2) 0 (h + 1) 0 0) :=
      Tr_Cp1 hLq hq (m + 2) 0 h 0 0
    by_cases hzq : z q = 1
    · -- Case 3: a split `S_{p-2}` after the output combine.
      by_cases hq3 : q = 2
      · subst hq3
        have s3 := Tr_low_split2 (H := W 2 0 (m + 2) 0 (h + 1) 0 0) hz hzq (fun i hi => W_le1 hi)
          (fun x => W_quiet_adj 2 (m + 2) (h + 1) 0 x)
        have e : z.update 2 0 + single 1 1 + single 3 1 + W 2 0 (m + 2) 0 (h + 1) 0 0
            = (z.update 2 0 + single 1 1) + W 2 1 (m + 2) 0 (h + 1) 0 0 := by
          simp only [W, Nat.reduceAdd, Finsupp.single_zero]
          abel
        rw [e] at s3
        have ha : Zk (z.update 2 0) 0 := by
          refine hz.erase 2 0 ?_
          intro x hx hx2
          have hx3 : x = 1 ∨ 3 ≤ x := by omega
          rcases hx3 with rfl | hx3
          · exact h0
          · exact hz.top x (by omega)
        have hb : Zk (z.update 2 0 + single 1 1) 2 := by
          refine ha.addAt (le_refl 1) ?_ ?_ ?_ (by omega) (by omega)
          · exact ha.top 1 (by omega)
          · exact ha.zero
          · exact ha.top 2 (by omega)
        have hL0 : (z.update 2 0 + single 1 1 : Pos) 2 = 0 := by
          simp [Finsupp.add_apply, Finsupp.update_apply, Finsupp.single_apply]
        have s4 := high_m5 (q := 2) (by norm_num) (by norm_num) hb.lowQ hL0 m (h + 1)
        exact ⟨z.update 2 0 + single 1 1, 5, 3, m, h + 2, hb,
          (((s1.trans s2).trans s3).trans s4), Or.inr ⟨rfl, rfl, rfl⟩⟩
      · have hq4 : 4 ≤ q := by omega
        have s3 := Tr_low_split (H := W q 0 (m + 2) 0 (h + 1) 0 0) hq4 hq hz hzq
          (fun i hi => W_le1 hi) (fun x => W_quiet_adj q (m + 2) (h + 1) 0 x)
        rw [reshape_c0] at s3
        have hzz : Zk (z.update q 0) (q - 2) := by
          refine hz.erase q (q - 2) ?_
          intro x hx hx2
          have hx3 : x = q - 1 ∨ q < x := by omega
          rcases hx3 with rfl | hx3
          · exact h0
          · exact hz.top x hx3
        have hInert : Inert (W q 0 m 0 (h + 2) 0 0) (q - 2) := Inert_W (by omega) m (h + 2) 0
        obtain ⟨z', k', hz', hT⟩ := pending (q := q - 2) (by omega) (by omega) hzz hInert
          (H0 := W q 1 (m + 2) 0 (h + 1) 0 0) (r := 2) (e := 1)
          (fun i hi => W_below (by omega))
          (fun L hL => high_m5 hq (by omega) (hL.mono (by omega)) (hL.top q (by omega)) m (h + 1))
        have hzq' : Zk z' q := hz'.mono (by omega)
        refine ⟨z', 1 + 1 + 1 + (k' + 2), 1 + 0 + 1 + (k' + 1), m, h + 2, hzq',
          ((s1.trans s2).trans s3).trans hT, Or.inr ⟨rfl, rfl, by omega⟩⟩
    · -- Case 1: no low move at all.
      have hz0 : z q = 0 := by
        have := hz.one q
        omega
      have hzz : Zk (z + single q 1) q :=
        hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (le_refl _) (le_refl _)
      exact ⟨z + single q 1, 2, 1, m + 2, h + 1, hzz, s1.trans s2, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The macro step at level `p = 2`, where the low state is empty. -/
theorem macro_step0 (m h : ℕ) : Tr (B 0 0 (m + 5) h) 4 2 (B 0 0 m (h + 2)) := by
  have hL : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  have hL0 : (0 : Pos) 0 = 0 := rfl
  have s1 : Tr (B 0 0 (m + 5) h) 1 1 (0 + W 0 1 (m + 3) 1 h 0 0) := Tr_S2 (m + 3) h
  have s2 : Tr ((0 : Pos) + W 0 1 (m + 3) 1 h 0 0) 1 1 (0 + W 0 0 (m + 2) 2 h 0 0) :=
    Tr_Cp hL hL0 (by norm_num) 0 (m + 2) 1 h 0 0 (Or.inr rfl)
  have s3 : Tr ((0 : Pos) + W 0 0 (m + 2) 2 h 0 0) 1 0 (0 + W 0 0 (m + 1) 1 (h + 1) 0 0) :=
    Tr_Cp1 hL (by norm_num) (m + 1) 1 h 0 0
  have s4 : Tr ((0 : Pos) + W 0 0 (m + 1) 1 (h + 1) 0 0) 1 0 (0 + W 0 0 m 0 (h + 2) 0 0) :=
    Tr_Cp1 hL (by norm_num) m 0 (h + 1) 0 0
  exact (((s1.trans s2).trans s3).trans s4)

/-- The whole pool of level `p = q + 2 ≥ 4` is consumed by macro steps. -/
theorem macro_loop {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) :
    ∀ (m : ℕ) (z : Pos) (h : ℕ), Zk z q →
      ∃ z1 m1 M K E, Zk z1 q ∧ m1 ≤ 4 ∧ Tr (B z q m h) K E (B z1 q m1 M) ∧
        K = E + (M - h) ∧ h ≤ M ∧ m ≤ m1 + 5 * (M - h) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro z h hz
    by_cases hm : m ≤ 4
    · exact ⟨z, m, h, 0, 0, hz, hm, Tr.refl _, by omega, le_refl _, by omega⟩
    · obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
      obtain ⟨z', k, e, m', h', hz', hT, hcase⟩ := macro_step hq hq2 hz m0 h
      have hm' : m' < m0 + 5 := by
        rcases hcase with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> omega
      obtain ⟨z1, m1, M, K, E, hz1, hm1, hT', hKE, hhM, hbound⟩ := ih m' hm' z' h' hz'
      refine ⟨z1, m1, M, k + K, e + E, hz1, hm1, hT.trans hT', ?_, ?_, ?_⟩
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

/-- The loop at level `p = 2`. -/
theorem macro_loop0 : ∀ (m h : ℕ),
    ∃ m1 M K E, m1 ≤ 4 ∧ Tr (B 0 0 m h) K E (B 0 0 m1 M) ∧
      K = E + (M - h) ∧ h ≤ M ∧ m ≤ m1 + 5 * (M - h) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    by_cases hm : m ≤ 4
    · exact ⟨m, h, 0, 0, hm, Tr.refl _, by omega, le_refl _, by omega⟩
    · obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
      obtain ⟨m1, M, K, E, hm1, hT', hKE, hhM, hbound⟩ := ih m0 (by omega) (h + 2)
      refine ⟨m1, M, 4 + K, 2 + E, hm1, (macro_step0 m0 h).trans hT', by omega, by omega, by omega⟩

end Zeck
```

## `ZeckExit.lean`

```lean
/-
  Part (b) of MathDB 347063: the endgame of a level, split by the pool size `K = m` and by the
  Case 1 / 2 / 3 trichotomy of the reviewer's erratum.  Combines outrank splits, so the order of
  the high and low moves differs between cases; a repeat at `p - 2` fires only after the
  high combines.

  Case 2 is `z (q-1) = 1`, where the combine `C_{p-2}` fires at once.  Cases 1 and 3 are
  `z (q-1) = 0` with `z q = 0` or `z q = 1`.
-/
import ZeckMacro

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma W_shift1 (q c3 : ℕ) : W q 0 1 0 c3 0 0 = single (q + 2) 1 + W (q + 2) 0 c3 0 0 0 0 := by
  ext t
  simp only [Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

lemma high_m4 {L : Pos} {q : ℕ} (hq : q % 2 = 0) (hq1 : 1 ≤ q) (hL : LowQ L q) (hL0 : L q = 0)
    (hL2 : L (q + 2) = 0) (m : ℕ) :
    Tr (L + W q 1 1 0 (m + 2) 0 0) 3 2 (L + W (q + 2) 0 m 0 1 0 0) := by
  have hLq : LowQ L (q + 2) := hL.mono (by omega)
  have s1 : Tr (L + W q 1 1 0 (m + 2) 0 0) 1 1 (L + W q 0 0 1 (m + 2) 0 0) :=
    Tr_Cp hL hL0 hq 0 0 0 (m + 2) 0 0 (Or.inl hq1)
  have e : W q 0 0 1 (m + 2) 0 0 = W (q + 2) 1 (m + 2) 0 0 0 0 := W_shift q 1 (m + 2) 0 0
  rw [e] at s1
  have s2 : Tr (L + W (q + 2) 1 (m + 2) 0 0 0 0) 1 1 (L + W (q + 2) 0 (m + 1) 1 0 0 0) :=
    Tr_Cp hLq hL2 (by omega) 0 (m + 1) 0 0 0 0 (Or.inl (by omega))
  have s3 : Tr (L + W (q + 2) 0 (m + 1) 1 0 0 0) 1 0 (L + W (q + 2) 0 m 0 1 0 0) :=
    Tr_Cp1 hLq (by omega) m 0 0 0 0
  exact (s1.trans s2).trans s3

/-- The endgame at a level `p = q + 2 ≥ 4`. -/
theorem exit_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q)
    (m M0 : ℕ) (hm : m ≤ 4) :
    ∃ z' k e m' h', Zk z' (q + 2) ∧ h' ≤ 2 ∧
      Tr (B z q m (M0 + 4)) k e (B z' (q + 2) m' h') ∧
      e ≤ k ∧ k ≤ e + 2 ∧ M0 ≤ m' ∧ m' ≤ M0 + 5 := by
  have hq2' : (q + 2) % 2 = 0 := by omega
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl
  · -- `K = 0`: the pool is empty, relabel.
    have e : B z q 0 (M0 + 4) = B z (q + 2) (M0 + 4) 0 := by
      show z + W q 0 0 0 (M0 + 4) 0 0 = z + W (q + 2) 0 (M0 + 4) 0 0 0 0
      rw [W_shift]
    refine ⟨z, 0, 0, M0 + 4, 0, hz.mono (by omega), by omega, ?_, by omega, by omega, by omega,
      by omega⟩
    rw [e]
    exact Tr.refl _
  · -- `K = 1`: the single pool chip stays in the low state.
    have e : B z q 1 (M0 + 4) = B (z + single (q + 2) 1) (q + 2) (M0 + 4) 0 := by
      show z + W q 0 1 0 (M0 + 4) 0 0 = (z + single (q + 2) 1) + W (q + 2) 0 (M0 + 4) 0 0 0 0
      rw [W_shift1, add_assoc]
    have hzz : Zk (z + single (q + 2) 1) (q + 2) :=
      hz.addAt (by omega) (hz.top _ (by omega)) (hz.top _ (by omega)) (hz.top _ (by omega))
        (by omega) (le_refl _)
    refine ⟨_, 0, 0, M0 + 4, 0, hzz, by omega, ?_, by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · -- `K = 2`: `S_p` leaves the pool empty.
    have s1 : Tr (B z q 2 (M0 + 4)) 1 1 (z + single q 1 + W q 0 0 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 0 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2: the chip at `p - 1` stays low because `a_p = 0`.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 0 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hZ : Zk (z.update (q - 1) 0 + single (q + 1) 1) (q + 1) := by
        refine hz1.addAt (by omega) ?_ ?_ ?_ (by omega) (le_refl _)
        · have hne : q + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
        · rw [show q + 1 - 1 = q by omega]
          have hne : q ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne, hq0]
        · have hne : q + 1 + 1 ≠ q - 1 := by omega
          simp [Finsupp.update_apply, hne]
          exact hz.top _ (by omega)
      have hLq := (hZ.mono (show q + 1 ≤ q + 2 by omega)).lowQ
      have hL0 : (z.update (q - 1) 0 + single (q + 1) 1 : Pos) (q + 2) = 0 :=
        hZ.top _ (by omega)
      have e : W q 0 0 1 (M0 + 4) 0 0 = W (q + 2) 1 (M0 + 4) 0 0 0 0 := W_shift q 1 (M0 + 4) 0 0
      rw [e] at s1 s2
      have s3 : Tr (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 1 (M0 + 4) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq hL0 hq2' 0 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s4 : Tr (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) 1 0
          (z.update (q - 1) 0 + single (q + 1) 1 + W (q + 2) 0 (M0 + 2) 0 1 0 0) :=
        Tr_Cp1 hLq hq2' (M0 + 2) 0 0 0 0
      exact ⟨_, 4, 3, M0 + 2, 1, hZ.mono (by omega), by omega,
        (((s1.trans s2).trans s3).trans s4), by omega, by omega, by omega, by omega⟩
    · -- Cases 1 and 3: the high combines first, then the quiet insertion.
      have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have hLq := hLq0.mono (show q ≤ q + 2 by omega)
      have hL0 : (z + single q 1 : Pos) (q + 2) = 0 := hLq0.top _ (by omega)
      have e : W q 0 0 1 (M0 + 4) 0 0 = W (q + 2) 1 (M0 + 4) 0 0 0 0 := W_shift q 1 (M0 + 4) 0 0
      rw [e] at s1
      have s3 : Tr (z + single q 1 + W (q + 2) 1 (M0 + 4) 0 0 0 0) 1 1
          (z + single q 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq hL0 hq2' 0 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s4 : Tr (z + single q 1 + W (q + 2) 0 (M0 + 3) 1 0 0 0) 1 0
          (z + single q 1 + W (q + 2) 0 (M0 + 2) 0 1 0 0) :=
        Tr_Cp1 hLq hq2' (M0 + 2) 0 0 0 0
      have hI : Inert (W (q + 2) 0 (M0 + 2) 0 1 0 0) q := Inert_W (by omega) (M0 + 2) 1 0
      obtain ⟨z', k', hz', hT⟩ := cascade q hq hq2 z _ hz hI
      refine ⟨z', 1 + 1 + 1 + k', 1 + 1 + 0 + k', M0 + 2, 1, hz'.mono (by omega), by omega,
        ((s1.trans s3).trans s4).trans hT, by omega, by omega, by omega, by omega⟩
  · -- `K = 3`.
    have s1 : Tr (B z q 3 (M0 + 4)) 1 1 (z + single q 1 + W q 0 1 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 1 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2: `C_{p-2}`, then `C_p`, then the doubled exit.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 1 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      rw [reshape_c0] at s2
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hL0 : (z.update (q - 1) 0) q = 0 := by
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hq0]
      have hLq2 := hz1.mono (show q ≤ q + 2 by omega)
      have hL2 : (z.update (q - 1) 0) (q + 2) = 0 := hz1.top _ (by omega)
      have s3 : Tr (z.update (q - 1) 0 + W q 1 1 1 (M0 + 4) 0 0) 1 1
          (z.update (q - 1) 0 + W q 0 0 2 (M0 + 4) 0 0) :=
        Tr_Cp hz1.lowQ hL0 hq 0 0 1 (M0 + 4) 0 0 (Or.inl (by omega))
      have e : W q 0 0 2 (M0 + 4) 0 0 = W (q + 2) 2 (M0 + 4) 0 0 0 0 := W_shift q 2 (M0 + 4) 0 0
      rw [e] at s3
      have s4 : Tr (z.update (q - 1) 0 + W (q + 2) 2 (M0 + 4) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 3) 1 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 1 (M0 + 3) 0 0 0 0 (Or.inl (by omega))
      have s5 : Tr (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 3) 1 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 2) 2 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 0 (M0 + 2) 1 0 0 0 (Or.inl (by omega))
      have s6 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 2) 2 0 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 1) 1 1 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' (M0 + 1) 1 0 0 0
      have s7 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 1) 1 1 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 M0 0 2 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' M0 0 1 0 0
      exact ⟨_, 7, 5, M0, 2, hLq2, by omega,
        (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7,
        by omega, by omega, by omega, by omega⟩
    · -- Cases 1 and 3: the corrected entry, `C_{p+1}` before `S_{p-2}`.
      have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have s2 : Tr (z + single q 1 + W q 0 1 1 (M0 + 4) 0 0) 1 0
          (z + single q 1 + W q 0 0 0 (M0 + 5) 0 0) :=
        Tr_Cp1 hLq0 hq 0 0 (M0 + 4) 0 0
      have e : W q 0 0 0 (M0 + 5) 0 0 = W (q + 2) 0 (M0 + 5) 0 0 0 0 := W_shift q 0 (M0 + 5) 0 0
      rw [e] at s2
      have hI : Inert (W (q + 2) 0 (M0 + 5) 0 0 0 0) q := Inert_W (by omega) (M0 + 5) 0 0
      obtain ⟨z', k', hz', hT⟩ := cascade q hq hq2 z _ hz hI
      refine ⟨z', 1 + 1 + k', 1 + 0 + k', M0 + 5, 0, hz'.mono (by omega), by omega,
        (s1.trans s2).trans hT, by omega, by omega, by omega, by omega⟩
  · -- `K = 4`.
    have s1 : Tr (B z q 4 (M0 + 4)) 1 1 (z + single q 1 + W q 0 2 1 (M0 + 4) 0 0) :=
      Tr_Sp hq2 hq hz 2 (M0 + 4)
    by_cases h1 : z (q - 1) = 1
    · -- Case 2.
      have hq0 : z q = 0 := by
        have := hz.adj (q - 1)
        rw [show q - 1 + 1 = q by omega] at this
        omega
      have s2 := Tr_low_cons (H := W q 0 2 1 (M0 + 4) 0 0) hq2 hq hz h1 (fun i hi => W_below hi)
      rw [reshape_c0] at s2
      have hz1 : Zk (z.update (q - 1) 0) q := hz.erase (q - 1) q (fun x hx _ => hz.top x hx)
      have hL0 : (z.update (q - 1) 0) q = 0 := by
        have hne : q ≠ q - 1 := by omega
        simp [Finsupp.update_apply, hne, hq0]
      have hLq2 := hz1.mono (show q ≤ q + 2 by omega)
      have hL2 : (z.update (q - 1) 0) (q + 2) = 0 := hz1.top _ (by omega)
      have s3 : Tr (z.update (q - 1) 0 + W q 1 2 1 (M0 + 4) 0 0) 1 1
          (z.update (q - 1) 0 + W q 0 1 2 (M0 + 4) 0 0) :=
        Tr_Cp hz1.lowQ hL0 hq 0 1 1 (M0 + 4) 0 0 (Or.inl (by omega))
      have s4 : Tr (z.update (q - 1) 0 + W q 0 1 2 (M0 + 4) 0 0) 1 0
          (z.update (q - 1) 0 + W q 0 0 1 (M0 + 5) 0 0) :=
        Tr_Cp1 hz1.lowQ hq 0 1 (M0 + 4) 0 0
      have e : W q 0 0 1 (M0 + 5) 0 0 = W (q + 2) 1 (M0 + 5) 0 0 0 0 := W_shift q 1 (M0 + 5) 0 0
      rw [e] at s4
      have s5 : Tr (z.update (q - 1) 0 + W (q + 2) 1 (M0 + 5) 0 0 0 0) 1 1
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 4) 1 0 0 0) :=
        Tr_Cp hLq2.lowQ hL2 hq2' 0 (M0 + 4) 0 0 0 0 (Or.inl (by omega))
      have s6 : Tr (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 4) 1 0 0 0) 1 0
          (z.update (q - 1) 0 + W (q + 2) 0 (M0 + 3) 0 1 0 0) :=
        Tr_Cp1 hLq2.lowQ hq2' (M0 + 3) 0 0 0 0
      exact ⟨_, 6, 4, M0 + 3, 1, hLq2, by omega,
        (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6),
        by omega, by omega, by omega, by omega⟩
    · have h0 : z (q - 1) = 0 := by
        have := hz.one (q - 1)
        omega
      have hLq0 : LowQ (z + single q 1) q := hz.lowQ_add hq2 h0
      have s2 : Tr (z + single q 1 + W q 0 2 1 (M0 + 4) 0 0) 1 0
          (z + single q 1 + W q 0 1 0 (M0 + 5) 0 0) :=
        Tr_Cp1 hLq0 hq 1 0 (M0 + 4) 0 0
      by_cases hzq : z q = 1
      · -- Case 3: the split `S_{p-2}` fires after `C_{p+1}`.
        by_cases hq3 : q = 2
        · subst hq3
          have s3 := Tr_low_split2 (H := W 2 0 1 0 (M0 + 5) 0 0) hz hzq (fun i hi => W_le1 hi)
            (fun x => W_quiet_adj 2 1 (M0 + 5) 0 x)
          have e : z.update 2 0 + single 1 1 + single 3 1 + W 2 0 1 0 (M0 + 5) 0 0
              = (z.update 2 0 + single 1 1) + W 2 1 1 0 (M0 + 5) 0 0 := by
            simp only [W, Nat.reduceAdd, Finsupp.single_zero]
            abel
          rw [e] at s3
          have ha : Zk (z.update 2 0) 0 := by
            refine hz.erase 2 0 ?_
            intro x hx hx2
            have hx3 : x = 1 ∨ 3 ≤ x := by omega
            rcases hx3 with rfl | hx3
            · exact h0
            · exact hz.top x (by omega)
          have hb : Zk (z.update 2 0 + single 1 1) 2 := by
            refine ha.addAt (le_refl 1) ?_ ?_ ?_ (by omega) (by omega)
            · exact ha.top 1 (by omega)
            · exact ha.zero
            · exact ha.top 2 (by omega)
          have hL0 : (z.update 2 0 + single 1 1 : Pos) 2 = 0 := by
            simp [Finsupp.add_apply, Finsupp.update_apply, Finsupp.single_apply]
          have hL2 : (z.update 2 0 + single 1 1 : Pos) (2 + 2) = 0 := hb.top _ (by omega)
          have s4 := high_m4 (q := 2) (by norm_num) (by norm_num) hb.lowQ hL0 hL2 (M0 + 3)
          exact ⟨z.update 2 0 + single 1 1, 6, 4, M0 + 3, 1, hb.mono (by omega), by omega,
            ((((s1.trans s2).trans s3).trans s4)), by omega, by omega, by omega, by omega⟩
        · have hq4 : 4 ≤ q := by omega
          have s3 := Tr_low_split (H := W q 0 1 0 (M0 + 5) 0 0) hq4 hq hz hzq
            (fun i hi => W_le1 hi) (fun x => W_quiet_adj q 1 (M0 + 5) 0 x)
          rw [reshape_c0] at s3
          have hzz : Zk (z.update q 0) (q - 2) := by
            refine hz.erase q (q - 2) ?_
            intro x hx hx2
            have hx3 : x = q - 1 ∨ q < x := by omega
            rcases hx3 with rfl | hx3
            · exact h0
            · exact hz.top x hx3
          have hInert : Inert (W (q + 2) 0 (M0 + 3) 0 1 0 0) (q - 2) :=
            Inert_W (by omega) (M0 + 3) 1 0
          obtain ⟨z', k', hz', hT⟩ := pending (q := q - 2) (by omega) (by omega) hzz hInert
            (H0 := W q 1 1 0 (M0 + 5) 0 0) (r := 3) (e := 2)
            (fun i hi => W_below (by omega))
            (fun L hL => high_m4 hq (by omega) (hL.mono (by omega)) (hL.top q (by omega))
              (hL.top (q + 2) (by omega)) (M0 + 3))
          refine ⟨z', 1 + 1 + 1 + (k' + 3), 1 + 0 + 1 + (k' + 2), M0 + 3, 1,
            hz'.mono (by omega), by omega, ((s1.trans s2).trans s3).trans hT,
            by omega, by omega, by omega, by omega⟩
      · -- Case 1.
        have hz0 : z q = 0 := by
          have := hz.one q
          omega
        have e : W q 0 1 0 (M0 + 5) 0 0 = single (q + 2) 1 + W (q + 2) 0 (M0 + 5) 0 0 0 0 :=
          W_shift1 q (M0 + 5)
        rw [e, ← add_assoc] at s2
        have hzz : Zk (z + single q 1) q :=
          hz.addAt (by omega) hz0 h0 (hz.top _ (by omega)) (le_refl _) (le_refl _)
        have hzz2 : Zk (z + single q 1 + single (q + 2) 1) (q + 2) :=
          hzz.addAt (by omega) (hzz.top _ (by omega)) (hzz.top _ (by omega))
            (hzz.top _ (by omega)) (by omega) (le_refl _)
        exact ⟨_, 2, 1, M0 + 5, 0, hzz2, by omega, s1.trans s2, by omega, by omega, by omega,
          by omega⟩

end Zeck
```

## `ZeckLevel.lean`

```lean
/-
  Part (b) of MathDB 347063: the endgame at level `p = 2`, the start phase, a whole level,
  and the bounds on a Zeckendorf low state.
-/
import ZeckExit

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma W_shift00 (c2 c3 : ℕ) : W 0 0 0 c2 c3 0 0 = W 2 c2 c3 0 0 0 0 := by
  ext t
  simp only [W_apply]
  split_ifs <;> omega

lemma W_shift01 (c3 : ℕ) : W 0 0 1 0 c3 0 0 = single 2 1 + W 2 0 c3 0 0 0 0 := by
  ext t
  simp only [Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

lemma W_split01 (c : ℕ) : (0 : Pos) + W 0 1 0 1 c 0 0 = single 1 1 + W 2 1 c 0 0 0 0 := by
  ext t
  simp only [Finsupp.zero_apply, zero_add, Finsupp.add_apply, Finsupp.single_apply, W_apply]
  split_ifs <;> omega

/-- The endgame at level `p = 2`. -/
theorem exit_step0 (m M0 : ℕ) (hm : m ≤ 4) :
    ∃ z' k e m' h', Zk z' 2 ∧ h' ≤ 2 ∧ Tr (B 0 0 m (M0 + 4)) k e (B z' 2 m' h') ∧
      e ≤ k ∧ k ≤ e + 2 ∧ M0 ≤ m' ∧ m' ≤ M0 + 5 := by
  have hL : LowQ (0 : Pos) 2 := (Zk_zero' 2).lowQ
  have hL0' : (0 : Pos) 2 = 0 := rfl
  have hL00 : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl
  · have e : B 0 0 0 (M0 + 4) = B 0 2 (M0 + 4) 0 := by
      show (0 : Pos) + W 0 0 0 0 (M0 + 4) 0 0 = 0 + W 2 0 (M0 + 4) 0 0 0 0
      rw [W_shift00]
    refine ⟨0, 0, 0, M0 + 4, 0, Zk_zero' 2, by omega, ?_, by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · have e : B 0 0 1 (M0 + 4) = B (single 2 1) 2 (M0 + 4) 0 := by
      show (0 : Pos) + W 0 0 1 0 (M0 + 4) 0 0 = single 2 1 + W 2 0 (M0 + 4) 0 0 0 0
      rw [W_shift01, zero_add]
    refine ⟨single 2 1, 0, 0, M0 + 4, 0, Zk.single (by norm_num) (by norm_num), by omega, ?_,
      by omega, by omega, by omega, by omega⟩
    rw [e]
    exact Tr.refl _
  · have s1 : Tr (B 0 0 2 (M0 + 4)) 1 1 (0 + W 0 1 0 1 (M0 + 4) 0 0) := Tr_S2 0 (M0 + 4)
    rw [W_split01] at s1
    have hZ : Zk (single 1 1 : Pos) 2 := Zk.single (by norm_num) (by norm_num)
    have hL1 := hZ.lowQ
    have hL10 : (single 1 1 : Pos) 2 = 0 := by simp [Finsupp.single_apply]
    have s2 : Tr (single 1 1 + W 2 1 (M0 + 4) 0 0 0 0) 1 1 (single 1 1 + W 2 0 (M0 + 3) 1 0 0 0) :=
      Tr_Cp hL1 hL10 (by norm_num) 0 (M0 + 3) 0 0 0 0 (Or.inl (by norm_num))
    have s3 : Tr (single 1 1 + W 2 0 (M0 + 3) 1 0 0 0) 1 0 (single 1 1 + W 2 0 (M0 + 2) 0 1 0 0) :=
      Tr_Cp1 hL1 (by norm_num) (M0 + 2) 0 0 0 0
    exact ⟨single 1 1, 3, 2, M0 + 2, 1, hZ, by omega, ((s1.trans s2).trans s3), by omega, by omega,
      by omega, by omega⟩
  · have s1 : Tr (B 0 0 3 (M0 + 4)) 1 1 (0 + W 0 1 1 1 (M0 + 4) 0 0) := Tr_S2 1 (M0 + 4)
    have s2 : Tr ((0 : Pos) + W 0 1 1 1 (M0 + 4) 0 0) 1 1 (0 + W 0 0 0 2 (M0 + 4) 0 0) :=
      Tr_Cp hL00 rfl (by norm_num) 0 0 1 (M0 + 4) 0 0 (Or.inr rfl)
    rw [W_shift00] at s2
    have s3 : Tr ((0 : Pos) + W 2 2 (M0 + 4) 0 0 0 0) 1 1 (0 + W 2 1 (M0 + 3) 1 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 1 (M0 + 3) 0 0 0 0 (Or.inl (by norm_num))
    have s4 : Tr ((0 : Pos) + W 2 1 (M0 + 3) 1 0 0 0) 1 1 (0 + W 2 0 (M0 + 2) 2 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 0 (M0 + 2) 1 0 0 0 (Or.inl (by norm_num))
    have s5 : Tr ((0 : Pos) + W 2 0 (M0 + 2) 2 0 0 0) 1 0 (0 + W 2 0 (M0 + 1) 1 1 0 0) :=
      Tr_Cp1 hL (by norm_num) (M0 + 1) 1 0 0 0
    have s6 : Tr ((0 : Pos) + W 2 0 (M0 + 1) 1 1 0 0) 1 0 (0 + W 2 0 M0 0 2 0 0) :=
      Tr_Cp1 hL (by norm_num) M0 0 1 0 0
    exact ⟨0, 6, 4, M0, 2, Zk_zero' 2, by omega,
      ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, by omega, by omega, by omega,
      by omega⟩
  · have s1 : Tr (B 0 0 4 (M0 + 4)) 1 1 (0 + W 0 1 2 1 (M0 + 4) 0 0) := Tr_S2 2 (M0 + 4)
    have s2 : Tr ((0 : Pos) + W 0 1 2 1 (M0 + 4) 0 0) 1 1 (0 + W 0 0 1 2 (M0 + 4) 0 0) :=
      Tr_Cp hL00 rfl (by norm_num) 0 1 1 (M0 + 4) 0 0 (Or.inr rfl)
    have s3 : Tr ((0 : Pos) + W 0 0 1 2 (M0 + 4) 0 0) 1 0 (0 + W 0 0 0 1 (M0 + 5) 0 0) :=
      Tr_Cp1 hL00 (by norm_num) 0 1 (M0 + 4) 0 0
    rw [W_shift00] at s3
    have s4 : Tr ((0 : Pos) + W 2 1 (M0 + 5) 0 0 0 0) 1 1 (0 + W 2 0 (M0 + 4) 1 0 0 0) :=
      Tr_Cp hL hL0' (by norm_num) 0 (M0 + 4) 0 0 0 0 (Or.inl (by norm_num))
    have s5 : Tr ((0 : Pos) + W 2 0 (M0 + 4) 1 0 0 0) 1 0 (0 + W 2 0 (M0 + 3) 0 1 0 0) :=
      Tr_Cp1 hL (by norm_num) (M0 + 3) 0 0 0 0
    exact ⟨0, 5, 3, M0 + 3, 1, Zk_zero' 2, by omega,
      (((s1.trans s2).trans s3).trans s4).trans s5, by omega, by omega, by omega, by omega⟩

/-- A whole level: from a pool of at least `24` chips to the next READY state. -/
theorem level_step {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hz : Zk z q) (m h : ℕ) (hm : 24 ≤ m)
    (hh : h ≤ 2) :
    ∃ z' k e m' h', Zk z' (q + 2) ∧ h' ≤ 2 ∧ Tr (B z q m h) k e (B z' (q + 2) m' h') ∧
      e + m' ≤ k + 3 ∧ k ≤ e + m' + 6 := by
  by_cases hq0 : q = 0
  · subst hq0
    have hz0 : z = 0 := Zk_zero hz
    subst hz0
    obtain ⟨m1, M, K, E, hm1, hT, hKE, hhM, hbound⟩ := macro_loop0 m h
    have hM4 : 4 ≤ M := by omega
    obtain ⟨M0, rfl⟩ : ∃ M0, M = M0 + 4 := ⟨M - 4, by omega⟩
    obtain ⟨z', k, e, m', h', hz', hh', hT', h1, h2, h3, h4⟩ := exit_step0 m1 M0 hm1
    exact ⟨z', K + k, E + e, m', h', hz', hh', hT.trans hT', by omega, by omega⟩
  · have hq2 : 2 ≤ q := by omega
    obtain ⟨z1, m1, M, K, E, hz1, hm1, hT, hKE, hhM, hbound⟩ := macro_loop hq hq2 m z h hz
    have hM4 : 4 ≤ M := by omega
    obtain ⟨M0, rfl⟩ : ∃ M0, M = M0 + 4 := ⟨M - 4, by omega⟩
    obtain ⟨z', k, e, m', h', hz', hh', hT', h1, h2, h3, h4⟩ := exit_step hq hq2 hz1 m1 M0 hm1
    exact ⟨z', K + k, E + e, m', h', hz', hh', hT.trans hT', by omega, by omega⟩

/-! ### The start -/

lemma start_eq_W (n : ℕ) : start n = W 0 n 0 0 0 0 0 := by
  simp [start, W]

lemma A1_phase : ∀ (i r : ℕ), Tr (W 0 (r + 2 * i) 0 0 0 0 0) i 0 (W 0 r i 0 0 0 0) := by
  intro i
  induction i with
  | zero =>
    intro r
    have e : r + 2 * 0 = r := by ring
    rw [e]
    exact Tr.refl _
  | succ i ih =>
    intro r
    have e : r + 2 * (i + 1) = (r + 2) + 2 * i := by ring
    rw [e]
    have s1 := ih (r + 2)
    have s2 : Tr (W 0 (r + 2) i 0 0 0 0) 1 0 (W 0 r (i + 1) 0 0 0 0) := Tr_A1 r i 0 0 0 0
    exact s1.trans s2

theorem start_phase (n : ℕ) (hn : 5 ≤ n) :
    ∃ m h k e, h ≤ 2 ∧ Tr (start n) k e (B 0 0 m h) ∧ 2 * e + n ≤ 2 * k ∧ 2 * k ≤ 2 * e + n + 1 := by
  have hL : LowQ (0 : Pos) 0 := (Zk_zero' 0).lowQ
  rcases Nat.even_or_odd' n with ⟨s, rfl | rfl⟩
  · refine ⟨s, 0, s, 0, by omega, ?_, by omega, by omega⟩
    have s1 := A1_phase s 0
    rw [zero_add, ← start_eq_W] at s1
    have e : B 0 0 s 0 = W 0 0 s 0 0 0 0 := by
      show (0 : Pos) + W 0 0 s 0 0 0 0 = W 0 0 s 0 0 0 0
      rw [zero_add]
    rw [e]
    exact s1
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    have s1 := A1_phase (t + 2) 1
    rw [show 1 + 2 * (t + 2) = 2 * (t + 2) + 1 by ring, ← start_eq_W] at s1
    rw [show W 0 1 (t + 2) 0 0 0 0 = (0 : Pos) + W 0 1 (t + 2) 0 0 0 0 from (zero_add _).symm]
      at s1
    have s2 : Tr ((0 : Pos) + W 0 1 (t + 2) 0 0 0 0) 1 1 (0 + W 0 0 (t + 1) 1 0 0 0) :=
      Tr_Cp hL rfl (by norm_num) 0 (t + 1) 0 0 0 0 (Or.inr rfl)
    have s3 : Tr ((0 : Pos) + W 0 0 (t + 1) 1 0 0 0) 1 0 (0 + W 0 0 t 0 1 0 0) :=
      Tr_Cp1 hL (by norm_num) t 0 0 0 0
    exact ⟨t, 1, t + 2 + 1 + 1, 0 + 1 + 0, by omega, (s1.trans s2).trans s3, by omega, by omega⟩

/-! ### Bounds for Zeckendorf low states -/

lemma Zk.val_lt : ∀ (t : ℕ) (z : Pos), Zk z t → val z < F (t + 1) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro z hz
    by_cases hzero : z t = 0
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [Zk_zero hz]
        simp [val]
      · have hz' : Zk z (t - 1) := by
          refine ⟨hz.one, hz.adj, hz.zero, ?_⟩
          intro i hi
          by_cases hit : i = t
          · subst hit; exact hzero
          · exact hz.top i (by omega)
        have h1 := ih (t - 1) (by omega) z hz'
        have h2 : F (t - 1 + 1) ≤ F (t + 1) := F_mono (by omega)
        omega
    · have h1 : z t = 1 := by
        have := hz.one t
        omega
      have hzt : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · exact absurd hz.zero hzero
        · exact ht
      have hadj : z (t - 1) = 0 := by
        have := hz.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      have hz1 : Zk (z.update t 0) (t - 2) := by
        refine hz.erase t (t - 2) ?_
        intro x hx hxt
        have hx3 : x = t - 1 ∨ t < x := by omega
        rcases hx3 with rfl | hx3
        · exact hadj
        · exact hz.top x hx3
      have h2 := ih (t - 2) (by omega) _ hz1
      have hval : val z = val (z.update t 0) + F t := by
        conv_lhs => rw [decompose_at z t h1]
        rw [val_add, val_single, one_mul]
      have hrec : F (t + 1) = F t + F (t - 1) := F_rec hzt
      have hle : F (t - 2 + 1) ≤ F (t - 1) := by
        rcases Nat.lt_or_ge t 2 with ht2 | ht2
        · have e : t = 1 := by omega
          subst e
          simp
        · have e : t - 2 + 1 = t - 1 := by omega
          rw [e]
      omega

lemma Zk.chips_le : ∀ (t : ℕ) (z : Pos), Zk z t → chips z ≤ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro z hz
    by_cases hzero : z t = 0
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [Zk_zero hz]
        simp [chips]
      · have hz' : Zk z (t - 1) := by
          refine ⟨hz.one, hz.adj, hz.zero, ?_⟩
          intro i hi
          by_cases hit : i = t
          · subst hit; exact hzero
          · exact hz.top i (by omega)
        have h1 := ih (t - 1) (by omega) z hz'
        omega
    · have h1 : z t = 1 := by
        have := hz.one t
        omega
      have hzt : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · exact absurd hz.zero hzero
        · exact ht
      have hadj : z (t - 1) = 0 := by
        have := hz.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      have hz1 : Zk (z.update t 0) (t - 2) := by
        refine hz.erase t (t - 2) ?_
        intro x hx hxt
        have hx3 : x = t - 1 ∨ t < x := by omega
        rcases hx3 with rfl | hx3
        · exact hadj
        · exact hz.top x hx3
      have h2 := ih (t - 2) (by omega) _ hz1
      have hval : chips z = chips (z.update t 0) + 1 := by
        conv_lhs => rw [decompose_at z t h1]
        rw [chips_add, chips_single]
      omega

/-- The value in a READY state is the conserved game value. -/
lemma val_B (z : Pos) (q m h : ℕ) : val (B z q m h) = val z + m * F (q + 2) + h * F (q + 4) := by
  unfold B
  rw [val_add, val_W]
  omega

lemma chips_B (z : Pos) (q m h : ℕ) : chips (B z q m h) = chips z + m + h := by
  unfold B
  rw [chips_add, chips_W]
  omega

lemma F_add_two_le (q : ℕ) : F (q + 4) ≤ 3 * F (q + 2) := by
  have h1 : F (q + 4) = F (q + 3) + F (q + 2) := by
    have := F_rec (i := q + 3) (by omega)
    simpa using this
  have h2 : F (q + 3) = F (q + 2) + F (q + 1) := by
    have := F_rec (i := q + 2) (by omega)
    simpa using this
  have h3 : F (q + 1) ≤ F (q + 2) := F_mono (by omega)
  omega

end Zeck
```

## `ZeckConst.lean`

```lean
/-
  Part (b) of MathDB 347063: the constant `c = 5/2 - phi + ∑_{j≥2} 1/F_{2j}`, as a tsum,
  and the bracket `1.206 < c < 1.207`.
-/
import ZeckLevel
import Mathlib.Analysis.SpecificLimits.Basic

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

/-- The reciprocals of the even-indexed Fibonacci numbers `F_{2i+4}`. -/
noncomputable def aT (i : ℕ) : ℝ := 1 / (F (2 * i + 4) : ℝ)

/-- Partial sums of the series. -/
noncomputable def Ssum (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, aT i

/-- The constant of the Combine Smallest theorem. -/
noncomputable def combC : ℝ := 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)

lemma F_cast_pos (i : ℕ) : (0 : ℝ) < (F i : ℝ) := by
  exact_mod_cast F_pos i

lemma aT_pos (i : ℕ) : 0 < aT i := by
  unfold aT
  have := F_cast_pos (2 * i + 4)
  positivity

lemma aT_nonneg (i : ℕ) : 0 ≤ aT i := le_of_lt (aT_pos i)

lemma Ssum_zero : Ssum 0 = 0 := by simp [Ssum]

lemma Ssum_succ (j : ℕ) : Ssum (j + 1) = Ssum j + aT j := by
  simp [Ssum, Finset.sum_range_succ]

lemma F_double_le (i : ℕ) : 2 * F (2 * i + 4) ≤ F (2 * i + 6) := by
  have h1 : F (2 * i + 6) = F (2 * i + 5) + F (2 * i + 4) := by
    have := F_rec (i := 2 * i + 5) (by omega)
    simpa using this
  have h2 : F (2 * i + 4) ≤ F (2 * i + 5) := F_mono (by omega)
  omega

lemma aT_succ_le (i : ℕ) : aT (i + 1) ≤ aT i / 2 := by
  unfold aT
  have e : 2 * (i + 1) + 4 = 2 * i + 6 := by ring
  rw [e]
  have h1 := F_double_le i
  have h2 : (2 : ℝ) * (F (2 * i + 4) : ℝ) ≤ (F (2 * i + 6) : ℝ) := by exact_mod_cast h1
  have h3 := F_cast_pos (2 * i + 4)
  have h4 := F_cast_pos (2 * i + 6)
  rw [div_div, div_le_div_iff₀ h4 (by positivity)]
  linarith

lemma aT_geo (J t : ℕ) : aT (J + t) ≤ aT J * (1 / 2 : ℝ) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := aT_succ_le (J + t)
    rw [show J + (t + 1) = (J + t) + 1 by ring, pow_succ]
    nlinarith

lemma aT_summable : Summable aT := by
  have hg : Summable (fun t : ℕ => aT 0 * (1 / 2 : ℝ) ^ t) := summable_geometric_two.mul_left _
  refine Summable.of_nonneg_of_le aT_nonneg (fun t => ?_) hg
  have h := aT_geo 0 t
  simpa using h

lemma aT_split (J : ℕ) : ∑' i, aT i = Ssum J + ∑' t, aT (t + J) :=
  (aT_summable.sum_add_tsum_nat_add J).symm

lemma aT_tail_le (J : ℕ) : ∑' t, aT (t + J) ≤ 2 * aT J := by
  have hsum : Summable (fun t => aT (t + J)) := (summable_nat_add_iff J).2 aT_summable
  have hg : Summable (fun t : ℕ => aT J * (1 / 2 : ℝ) ^ t) := summable_geometric_two.mul_left _
  have hle : ∀ t, aT (t + J) ≤ aT J * (1 / 2 : ℝ) ^ t := by
    intro t
    rw [add_comm]
    exact aT_geo J t
  calc ∑' t, aT (t + J) ≤ ∑' t : ℕ, aT J * (1 / 2 : ℝ) ^ t := hsum.tsum_le_tsum hle hg
    _ = aT J * 2 := by rw [tsum_mul_left, tsum_geometric_two]
    _ = 2 * aT J := by ring

lemma aT_tail_nonneg (J : ℕ) : 0 ≤ ∑' t, aT (t + J) := by
  exact tsum_nonneg (fun t => aT_nonneg _)

lemma combC_eq : combC = 5 / 2 - phi + ∑' i, aT i := by
  unfold combC
  congr 1

lemma phi_lt : phi < 1.6181 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma phi_gt : 1.618 < phi := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-- The bracket of Conjecture 1.4 for the Combine Smallest constant. -/
theorem combC_bracket : (1.206 : ℝ) < combC ∧ combC < 1.207 := by
  have hphi1 := phi_lt
  have hphi2 := phi_gt
  have hS7 : Ssum 7 = 1 / 5 + 1 / 13 + 1 / 34 + 1 / 89 + 1 / 233 + 1 / 610 + 1 / 1597 := by
    simp only [Ssum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, aT]
    have e0 : F (2 * 0 + 4) = 5 := by decide
    have e1 : F (2 * 1 + 4) = 13 := by decide
    have e2 : F (2 * 2 + 4) = 34 := by decide
    have e3 : F (2 * 3 + 4) = 89 := by decide
    have e4 : F (2 * 4 + 4) = 233 := by decide
    have e5 : F (2 * 5 + 4) = 610 := by decide
    have e6 : F (2 * 6 + 4) = 1597 := by decide
    rw [e0, e1, e2, e3, e4, e5, e6]
    norm_num
  have ha7 : aT 7 = 1 / 4181 := by
    unfold aT
    have e7 : F (2 * 7 + 4) = 4181 := by decide
    rw [e7]
    norm_num
  have hsplit := aT_split 7
  have htail := aT_tail_le 7
  have hnn := aT_tail_nonneg 7
  rw [combC_eq, hsplit, hS7]
  rw [ha7] at htail
  constructor
  · norm_num at *
    linarith
  · norm_num at *
    linarith

end Zeck
```

## `ZeckRotation.lean`

```lean
/-
  Part (b) of MathDB 347063: the rotation of the low state and the chip balance of a cycle.

  These statements are not used by the endpoint theorems (the counter `D` replaces them),
  but they are what the proof plan asked for: a macro step acts on the low value `L = val z`
  as the rotation `L ↦ L + F_{p-2} mod F_{p-1}`, a full cycle of `F_{p-1}` macros returns the
  low state, and a cycle consists of exactly `F_{p+2} - 1` moves, of which exactly `F_p - 1`
  are splits.  Here `q = p - 2`.
-/
import ZeckLevel

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

lemma F_add_four (q : ℕ) : F (q + 4) = 2 * F (q + 2) + F (q + 1) := by
  have h1 : F (q + 4) = F (q + 3) + F (q + 2) := by
    have := F_rec (i := q + 3) (by omega)
    simpa using this
  have h2 : F (q + 3) = F (q + 2) + F (q + 1) := by
    have := F_rec (i := q + 2) (by omega)
    simpa using this
  omega

lemma F_add_two (q : ℕ) : F (q + 2) = F (q + 1) + F q := by
  have := F_rec (i := q + 1) (by omega)
  simpa using this

/-- A macro step as a rotation of the low value. -/
theorem macro_rot {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      ((m' = m + 2 ∧ h' = h + 1 ∧ k = e + 1 ∧ val z' = val z + F q) ∨
       (m' = m ∧ h' = h + 2 ∧ k = e + 2 ∧ val z' + F (q + 1) = val z + F q)) := by
  obtain ⟨z', k, e, m', h', hz', hT, hc⟩ := macro_step hq hq2 hz m h
  refine ⟨z', k, e, m', h', hz', hT, ?_⟩
  have hval := hT.st.val_eq
  rw [val_B, val_B] at hval
  have hF4 := F_add_four q
  have hF2 := F_add_two q
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine Or.inl ⟨rfl, rfl, rfl, ?_⟩
    simp only [Nat.add_mul] at hval
    omega
  · refine Or.inr ⟨rfl, rfl, rfl, ?_⟩
    simp only [Nat.add_mul] at hval
    omega

/-- The rotation in the mod form of the review: a macro step sends `L` to
`(L + F_{p-2}) % F_{p-1}`. -/
theorem macro_rotation {z : Pos} {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) (hz : Zk z q) (m h : ℕ) :
    ∃ z' k e m' h', Zk z' q ∧ Tr (B z q (m + 5) h) k e (B z' q m' h') ∧
      val z' = (val z + F q) % F (q + 1) := by
  obtain ⟨z', k, e, m', h', hz', hT, hc⟩ := macro_rot hq hq2 hz m h
  refine ⟨z', k, e, m', h', hz', hT, ?_⟩
  have hlt := hz'.val_lt _ _
  rcases hc with ⟨_, _, _, hv⟩ | ⟨_, _, _, hv⟩
  · rw [← hv]
    exact (Nat.mod_eq_of_lt hlt).symm
  · have e1 : val z + F q = val z' + F (q + 1) := hv.symm
    rw [e1, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt hlt).symm

/-- Iterating the macro step. -/
theorem macro_iter {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) :
    ∀ (t : ℕ) (z : Pos) (m h : ℕ), Zk z q → 5 * t ≤ m →
      ∃ z' k e m' h' w, Zk z' q ∧ Tr (B z q m h) k e (B z' q m' h') ∧ w ≤ t ∧
        m' + 3 * (t - w) + 5 * w = m ∧ h' = h + (t - w) + 2 * w ∧ k = e + (t - w) + 2 * w ∧
        val z' + w * F (q + 1) = val z + t * F q := by
  intro t
  induction t with
  | zero =>
    intro z m h hz _
    exact ⟨z, 0, 0, m, h, 0, hz, Tr.refl _, le_refl _, by omega, by omega, by omega, by simp⟩
  | succ t ih =>
    intro z m h hz hm
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 5 := ⟨m - 5, by omega⟩
    obtain ⟨z1, k1, e1, m1, h1, hz1, hT1, hc⟩ := macro_rot hq hq2 hz m0 h
    have hm1 : 5 * t ≤ m1 := by
      rcases hc with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ <;> omega
    obtain ⟨z', k2, e2, m', h', w, hz', hT2, hw, hmm, hhh, hkk, hvv⟩ := ih z1 m1 h1 hz1 hm1
    have htF : (t + 1) * F q = t * F q + F q := by ring
    rcases hc with ⟨rfl, rfl, rfl, hv⟩ | ⟨rfl, rfl, rfl, hv⟩
    · refine ⟨z', e1 + 1 + k2, e1 + e2, m', h', w, hz', hT1.trans hT2, by omega, by omega,
        by omega, by omega, ?_⟩
      rw [htF]
      omega
    · refine ⟨z', e1 + 2 + k2, e1 + e2, m', h', w + 1, hz', hT1.trans hT2, by omega, by omega,
        by omega, by omega, ?_⟩
      have hwF : (w + 1) * F (q + 1) = w * F (q + 1) + F (q + 1) := by ring
      rw [htF, hwF]
      omega

/-- Zeckendorf uniqueness for low states. -/
theorem Zk.eq_of_val : ∀ (t : ℕ) (a b : Pos), Zk a t → Zk b t → val a = val b → a = b := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a b ha hb hv
    have lowZ : ∀ (c : Pos), Zk c t → c t = 0 → Zk c (t - 1) := by
      intro c hc h0
      refine ⟨hc.one, hc.adj, hc.zero, ?_⟩
      intro i hi
      by_cases hit : i = t
      · subst hit; exact h0
      · exact hc.top i (by omega)
    have top1 : ∀ (c : Pos), Zk c t → c t = 1 → 1 ≤ t := by
      intro c hc h1
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [hc.zero] at h1
        omega
      · exact ht
    have erase : ∀ (c : Pos), Zk c t → c t = 1 → Zk (c.update t 0) (t - 2) := by
      intro c hc h1
      have ht := top1 c hc h1
      have hadj : c (t - 1) = 0 := by
        have := hc.adj (t - 1)
        rw [show t - 1 + 1 = t by omega] at this
        omega
      refine hc.erase t (t - 2) ?_
      intro x hx hxt
      have hx3 : x = t - 1 ∨ t < x := by omega
      rcases hx3 with rfl | hx3
      · exact hadj
      · exact hc.top x hx3
    have valtop : ∀ (c : Pos), c t = 1 → val c = val (c.update t 0) + F t := by
      intro c h1
      conv_lhs => rw [decompose_at c t h1]
      rw [val_add, val_single, one_mul]
    have hnocross : ∀ (c d : Pos), Zk c t → Zk d t → c t = 0 → d t = 1 → val c ≠ val d := by
      intro c d hc hd h0 h1 he
      have ht := top1 d hd h1
      have h3 := (lowZ c hc h0).val_lt (t - 1) c
      have h4 := valtop d h1
      have e : t - 1 + 1 = t := by omega
      rw [e] at h3
      omega
    by_cases ha0 : a t = 0
    · by_cases hb0 : b t = 0
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · rw [Zk_zero ha, Zk_zero hb]
        · exact ih (t - 1) (by omega) a b (lowZ a ha ha0) (lowZ b hb hb0) hv
      · have hb1 : b t = 1 := by
          have := hb.one t
          omega
        exact absurd hv (hnocross a b ha hb ha0 hb1)
    · have ha1 : a t = 1 := by
        have := ha.one t
        omega
      by_cases hb0 : b t = 0
      · exact absurd hv.symm (hnocross b a hb ha hb0 ha1)
      · have hb1 : b t = 1 := by
          have := hb.one t
          omega
        have ht := top1 a ha ha1
        have hE := ih (t - 2) (by omega) _ _ (erase a ha ha1) (erase b hb hb1) (by
          have h1 := valtop a ha1
          have h2 := valtop b hb1
          omega)
        calc a = a.update t 0 + Finsupp.single t 1 := decompose_at a t ha1
          _ = b.update t 0 + Finsupp.single t 1 := by rw [hE]
          _ = b := (decompose_at b t hb1).symm

/-! ### Counting the splits -/

/-- The chosen Combine Smallest move at `a` is a split. -/
def splitMoveAt (a : Pos) : Prop :=
  ¬ legalA1 a ∧ smallestCons a = none ∧ ∃ i, legalSplit a i

/-- The number of split moves among the first `k` moves from `a`. -/
noncomputable def splitCount (a : Pos) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (if splitMoveAt (run stepCS a j) then 1 else 0)

lemma chips_step_split {a : Pos} (h : splitMoveAt a) : chips (stepCS a) = chips a := by
  obtain ⟨hA, hco, hex⟩ := h
  cases hsp : smallestSplit a with
  | none => exact absurd hex ((smallestSplit_none_iff a).1 hsp)
  | some i =>
    have hs : stepCS a = doSplit a i := by
      unfold stepCS
      simp [hA, hco, hsp]
    rw [hs]
    exact chips_doSplit a i (smallestSplit_some_spec a hsp).1

lemma chips_step_nonsplit {a : Pos} (hm : hasMove a) (h : ¬ splitMoveAt a) :
    chips (stepCS a) + 1 = chips a := by
  by_cases hA : legalA1 a
  · rw [stepCS_A1 a hA]
    exact chips_doA1 a hA
  · cases hco : smallestCons a with
    | some i =>
      have hl := (smallestCons_some_spec a hco).1
      have hs : stepCS a = doCons a i := by
        unfold stepCS
        simp [hA, hco]
      rw [hs]
      exact chips_doCons a i hl
    | none =>
      exfalso
      rcases hm with ha | ⟨i, hi⟩ | hs
      · exact hA ha
      · exact (smallestCons_none_iff a).1 hco ⟨i, hi⟩
      · exact h ⟨hA, hco, hs⟩

/-- Over any Combine Smallest run, chips lost plus splits equals moves. -/
theorem Steps_chips {a b : Pos} {k : ℕ} (h : Steps a k b) :
    chips a + splitCount a k = chips b + k := by
  induction h with
  | refl a => simp [splitCount]
  | @head a k c hm _ ih =>
    have hsum : splitCount a (k + 1) = splitCount (stepCS a) k
        + (if splitMoveAt a then 1 else 0) := by
      unfold splitCount
      rw [Finset.sum_range_succ']
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [run_succ']
    rw [hsum]
    by_cases hs : splitMoveAt a
    · have h1 := chips_step_split hs
      simp [hs]
      omega
    · have h1 := chips_step_nonsplit hm hs
      simp [hs]
      omega

/-! ### The cycle -/

lemma fib_even_identity (j : ℕ) :
    F (2 * j + 1) * F (2 * j + 1) + 1 = F (2 * j) * F (2 * j) + F (2 * j) * F (2 * j + 1) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
    have e2 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
    rw [e2, e1]
    have h1 : F (2 * j + 2) = F (2 * j + 1) + F (2 * j) := F_add_two (2 * j)
    have h2 : F (2 * j + 3) = F (2 * j + 2) + F (2 * j + 1) := F_add_two (2 * j + 1)
    rw [h2, h1]
    nlinarith

/-- The Cassini-type identity behind the moves per cycle. -/
lemma cassini_even {q : ℕ} (hq : q % 2 = 0) : F (q + 2) * F (q + 2) + 1 = F q * F (q + 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, q = 2 * j := ⟨q / 2, by omega⟩
  have h := fib_even_identity j
  have h1 : F (2 * j + 2) = F (2 * j + 1) + F (2 * j) := F_add_two (2 * j)
  have h2 : F (2 * j + 3) = F (2 * j + 2) + F (2 * j + 1) := F_add_two (2 * j + 1)
  have h4 : F (2 * j + 4) = 2 * F (2 * j + 2) + F (2 * j + 1) := F_add_four (2 * j)
  rw [h4, h1]
  nlinarith

/-- One full rotation cycle of the level `p = q + 2 ≥ 4`: the low state returns, the pool
loses `F_{p+2}`, the output pile gains `F_p`, the cycle has `F_{p+2} - 1` moves, of which
exactly `F_p - 1` are splits. -/
theorem rotation_cycle {q : ℕ} (hq : q % 2 = 0) (hq2 : 2 ≤ q) {z : Pos} (hz : Zk z q) (m h : ℕ)
    (hm : 5 * F (q + 1) ≤ m) :
    ∃ k e, Tr (B z q m h) k e (B z q (m - F (q + 4)) (h + F (q + 2))) ∧
      k + 1 = F (q + 4) ∧ splitCount (B z q m h) k + 1 = F (q + 2) := by
  obtain ⟨z', k, e, m', h', w, hz', hT, hw, hmm, hhh, hkk, hvv⟩ :=
    macro_iter hq hq2 (F (q + 1)) z m h hz hm
  have hc : 0 < F (q + 1) := F_pos _
  have hlt1 : val z' < F (q + 1) := hz'.val_lt _ _
  have hlt2 : val z < F (q + 1) := hz.val_lt _ _
  have hmod : val z' % F (q + 1) = val z % F (q + 1) := by
    have h1 := congrArg (· % F (q + 1)) hvv
    simp only [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_left] at h1
    exact h1
  have hval : val z' = val z := by
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
    exact hmod
  have hzz : z' = z := Zk.eq_of_val q z' z hz' hz hval
  subst hzz
  have hwF : w = F q := by
    have h1 : w * F (q + 1) = F q * F (q + 1) := by
      have h2 : F (q + 1) * F q = F q * F (q + 1) := by ring
      omega
    exact Nat.eq_of_mul_eq_mul_right hc h1
  subst hwF
  have hF4 := F_add_four q
  have hF2 := F_add_two q
  have hFq : F q ≤ F (q + 1) := F_mono (by omega)
  have hm' : m' = m - F (q + 4) := by omega
  have hh' : h' = h + F (q + 2) := by omega
  have hmF4 : F (q + 4) ≤ m := by omega
  subst hm'
  subst hh'
  -- the counter
  have hD := hT.dv
  have ha : d (q + 2) + 1 = F q := by
    have := d_even (i := q + 2) (by omega) (by omega)
    simpa [F] using this
  have hb : d (q + 4) + 1 = F (q + 2) := by
    have := d_even (i := q + 4) (by omega) (by omega)
    simpa [F] using this
  have hcass := cassini_even hq
  have hDz : D (B z' q (m - F (q + 4)) (h + F (q + 2))) =
      D z' + (m - F (q + 4)) * d (q + 2) + (h + F (q + 2)) * d (q + 4) := by
    unfold B
    rw [D_add, D_W]
    ring
  have hDz2 : D (B z' q m h) = D z' + m * d (q + 2) + h * d (q + 4) := by
    unfold B
    rw [D_add, D_W]
    ring
  rw [hDz, hDz2] at hD
  have hpm : (m - F (q + 4)) * d (q + 2) + F (q + 4) * d (q + 2) = m * d (q + 2) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have h2b : (h + F (q + 2)) * d (q + 4) = h * d (q + 4) + F (q + 2) * d (q + 4) := by ring
  have hP : F (q + 2) * d (q + 4) + F (q + 2) = F (q + 2) * F (q + 2) := by
    rw [← hb]
    ring
  have hQ : F (q + 4) * d (q + 2) + F (q + 4) = F q * F (q + 4) := by
    rw [← ha]
    ring
  have he : e + F (q + 4) * d (q + 2) = F (q + 2) * d (q + 4) := by omega
  have hk : k + 1 = F (q + 4) := by omega
  refine ⟨k, e, hT, hk, ?_⟩
  have hchips := Steps_chips hT.st
  rw [chips_B, chips_B] at hchips
  omega

end Zeck
```

## `ZeckChain.lean`

```lean
/-
  Part (b) of MathDB 347063: the level chain.  After `j` levels the number of moves equals
  the counter plus `n/2 + n ∑_{i<j} 1/F_{2i+4}` up to `16 (j+1)`.
-/
import ZeckConst

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

open Finsupp (single)

/-- The limiting density of the counter: `rho = 1/phi^2 = 2 - phi`. -/
noncomputable def rho : ℝ := 2 - phi

lemma rho_pos : 0 < rho := by
  unfold rho
  linarith [phi_lt_two]

lemma rho_le_one : rho ≤ 1 := by
  unfold rho
  linarith [phi_gt_one]

noncomputable def rr (n : ℕ) : ℝ := (Nat.fib n : ℝ) - rho * (Nat.fib (n + 2) : ℝ)

lemma rr_succ (n : ℕ) : rr (n + 1) = s * rr n := by
  have h1 : (Nat.fib (n + 2) : ℝ) = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_add_two
  have h2 : (Nat.fib (n + 1 + 2) : ℝ) = (Nat.fib (n + 1) : ℝ) + (Nat.fib (n + 2) : ℝ) := by
    exact_mod_cast Nat.fib_add_two
  have h := phi_sq
  unfold rr rho s
  rw [h2, h1]
  linear_combination ((Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ)) * h

lemma rr_abs_le (n : ℕ) : |rr n| ≤ 1 := by
  induction n with
  | zero =>
    have e : rr 0 = -rho := by simp [rr]
    rw [e, abs_neg, abs_of_pos rho_pos]
    exact rho_le_one
  | succ n ih =>
    rw [rr_succ, abs_mul]
    have h1 := abs_s_lt_one
    have h2 := abs_nonneg s
    have h3 := abs_nonneg (rr n)
    nlinarith

lemma d_approx (i : ℕ) : |(d i : ℝ) - rho * (F i : ℝ)| ≤ 2 := by
  rcases i with _ | n
  · have e : d 0 = 0 := by decide
    rw [e, F_zero]
    have h := rho_pos
    have h2 := rho_le_one
    rw [abs_le]
    constructor <;> push_cast <;> linarith
  · have hfn := rr_abs_le n
    rw [abs_le] at hfn
    obtain ⟨h1, h2⟩ := hfn
    have e1 : (F (n + 1) : ℝ) = (Nat.fib (n + 2) : ℝ) := by
      show (Nat.fib (n + 1 + 1) : ℝ) = _
      rfl
    unfold rr at h1 h2
    by_cases hev : (n + 1) % 2 = 0
    · have hd := d_even hev (by omega)
      have hd2 : (d (n + 1) : ℝ) + 1 = (Nat.fib n : ℝ) := by
        have h3 : d (n + 1) + 1 = Nat.fib n := by simpa using hd
        exact_mod_cast h3
      rw [e1, abs_le]
      constructor <;> nlinarith
    · have hd := d_odd (i := n + 1) (by omega)
      have hd2 : (d (n + 1) : ℝ) = (Nat.fib n : ℝ) := by
        have h3 : d (n + 1) = Nat.fib n := by simpa using hd
        exact_mod_cast h3
      rw [e1, abs_le]
      constructor <;> nlinarith

/-- The counter of an arbitrary position is `rho` times its value, up to the chip count. -/
lemma D_approx (a : Pos) : |(D a : ℝ) - rho * (val a : ℝ)| ≤ 2 * (chips a : ℝ) := by
  have e : (D a : ℝ) - rho * (val a : ℝ)
      = ∑ i ∈ a.support, (a i : ℝ) * ((d i : ℝ) - rho * (F i : ℝ)) := by
    unfold D val Finsupp.sum
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e2 : 2 * (chips a : ℝ) = ∑ i ∈ a.support, (a i : ℝ) * 2 := by
    unfold chips Finsupp.sum
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [e, e2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  have hc : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (d_approx i) hc

lemma w_le (i : ℕ) : w i ≤ (i : ℝ) + 3 := by
  have h1 : psi * s ^ i ≤ |psi * s ^ i| := le_abs_self _
  have h2 : |psi * s ^ i| ≤ psi := by
    rw [abs_mul, abs_of_pos psi_pos]
    nlinarith [abs_s_pow_le_one i, psi_pos]
  unfold w
  linarith [psi_lt_one]

lemma Phi_le_chips_mul (a : Pos) (T : ℕ) (h : ∀ i, T < i → a i = 0) :
    Phi a ≤ (chips a : ℝ) * ((T : ℝ) + 3) := by
  unfold Phi chips Finsupp.sum
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi' : i ≤ T := by
    by_contra hc
    rw [Finsupp.mem_support_iff] at hi
    exact hi (h i (by omega))
  have hw := w_le i
  have hi2 : (i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hi'
  have hc : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- The chain of READY states from the start of the game. -/
theorem chain (n J : ℕ) (hn : 1000 ≤ n) (hJ : F (2 * J + 2) ^ 2 ≤ n) :
    ∀ j, j ≤ J → ∃ z m h k e, Zk z (2 * j) ∧ h ≤ 2 ∧ Tr (start n) k e (B z (2 * j) m h) ∧
      |(k : ℝ) - e - ((n : ℝ) / 2 + n * Ssum j)| ≤ 16 * ((j : ℝ) + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨m, h, k, e, hh, hT, h1, h2⟩ := start_phase n (by omega)
    refine ⟨0, m, h, k, e, Zk_zero' _, hh, ?_, ?_⟩
    · simpa using hT
    · have h3 : (2 : ℝ) * e + n ≤ 2 * k := by exact_mod_cast h1
      have h4 : (2 : ℝ) * k ≤ 2 * e + n + 1 := by exact_mod_cast h2
      rw [Ssum_zero, abs_le]
      constructor <;> push_cast <;> linarith
  | succ j ih =>
    intro hj
    obtain ⟨z, m, h, k, e, hz, hh, hT, hQ⟩ := ih (by omega)
    have hval : val z + m * F (2 * j + 2) + h * F (2 * j + 4) = n := by
      have := hT.st.val_eq
      rw [val_B, val_start] at this
      exact this
    have hlt : val z < F (2 * j + 1) := hz.val_lt _ _
    have hF2 : F (2 * j + 4) ≤ 3 * F (2 * j + 2) := F_add_two_le (2 * j)
    have hF1 : F (2 * j + 1) ≤ F (2 * j + 2) := F_mono (by omega)
    have hFpos : 0 < F (2 * j + 2) := F_pos _
    have hmF : n ≤ (m + 7) * F (2 * j + 2) := by
      have h1 : h * F (2 * j + 4) ≤ 2 * (3 * F (2 * j + 2)) := Nat.mul_le_mul hh hF2
      nlinarith
    have hJ' : F (2 * j + 4) ≤ F (2 * J + 2) := F_mono (by omega)
    have hF42 : F (2 * j + 2) ≤ F (2 * j + 4) := F_mono (by omega)
    have hm24 : 24 ≤ m := by
      by_contra hc
      have hm23 : m + 7 ≤ 30 := by omega
      have h1 : n ≤ 30 * F (2 * j + 2) := le_trans hmF (Nat.mul_le_mul_right _ hm23)
      have h2 : F (2 * j + 2) * F (2 * j + 2) ≤ n := by
        calc F (2 * j + 2) * F (2 * j + 2) ≤ F (2 * J + 2) * F (2 * J + 2) :=
              Nat.mul_le_mul (le_trans hF42 hJ') (le_trans hF42 hJ')
          _ = F (2 * J + 2) ^ 2 := (pow_two _).symm
          _ ≤ n := hJ
      have h3 : F (2 * j + 2) ≤ 30 :=
        Nat.le_of_mul_le_mul_right (le_trans h2 h1) hFpos
      have h4 : n ≤ 900 := le_trans h1 (Nat.mul_le_mul_left 30 h3)
      omega
    obtain ⟨z', k', e', m', h', hz', hh', hT', hA, hB⟩ :=
      level_step (q := 2 * j) (by omega) hz m h hm24 hh
    have hTT := hT.trans hT'
    have hval' : val z' + m' * F (2 * j + 4) + h' * F (2 * j + 6) = n := by
      have := hTT.st.val_eq
      rw [val_B, val_start] at this
      exact this
    have hlt' : val z' < F (2 * j + 3) := hz'.val_lt _ _
    have hF2' : F (2 * j + 6) ≤ 3 * F (2 * j + 4) := F_add_two_le (2 * j + 2)
    have hF1' : F (2 * j + 3) ≤ F (2 * j + 4) := F_mono (by omega)
    have hFa : 0 < F (2 * j + 4) := F_pos _
    have hm'le : m' * F (2 * j + 4) ≤ n := by omega
    have hmF' : n ≤ (m' + 7) * F (2 * j + 4) := by
      have h1 : h' * F (2 * j + 6) ≤ 2 * (3 * F (2 * j + 4)) := Nat.mul_le_mul hh' hF2'
      nlinarith
    have hF0 : (0 : ℝ) < (F (2 * j + 4) : ℝ) := F_cast_pos _
    have hm1 : (m' : ℝ) * (F (2 * j + 4) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm'le
    have hm2 : (n : ℝ) ≤ ((m' : ℝ) + 7) * (F (2 * j + 4) : ℝ) := by exact_mod_cast hmF'
    have hd1 : (m' : ℝ) ≤ (n : ℝ) / (F (2 * j + 4) : ℝ) := by
      rw [le_div_iff₀ hF0]; exact hm1
    have hd2 : (n : ℝ) / (F (2 * j + 4) : ℝ) ≤ (m' : ℝ) + 7 := by
      rw [div_le_iff₀ hF0]; exact hm2
    have hSs : (n : ℝ) * Ssum (j + 1) = n * Ssum j + (n : ℝ) / (F (2 * j + 4) : ℝ) := by
      rw [Ssum_succ]
      unfold aT
      ring
    have hAr : (e' : ℝ) + m' ≤ k' + 3 := by exact_mod_cast hA
    have hBr : (k' : ℝ) ≤ e' + m' + 6 := by exact_mod_cast hB
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]
    refine ⟨z', m', h', k + k', e + e', hz', hh', hTT, ?_⟩
    rw [abs_le] at hQ ⊢
    obtain ⟨hQ1, hQ2⟩ := hQ
    push_cast
    rw [hSs]
    constructor <;> linarith

end Zeck
```

## `ZeckCS.lean`

```lean
/-
  Part (b) of MathDB 347063: the Combine Smallest estimate.
-/
import ZeckChain

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

noncomputable def bL : ℝ := 1 / (2 * Real.log 2)

noncomputable def C0 : ℝ := 8 * bL ^ 2 + 40 * bL + 29 / Real.log 2

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma bL_pos : 0 < bL := by
  unfold bL
  have := log_two_pos'
  positivity

lemma C0_pos : 0 < C0 := by
  unfold C0
  have h1 := bL_pos
  have h2 := log_two_pos'
  positivity

lemma D_start (n : ℕ) : D (start n) = 0 := by
  unfold start
  rw [D_single]
  have e : d 1 = 0 := by decide
  rw [e, mul_zero]

lemma exists_level (n : ℕ) (hn : 4 ≤ n) :
    ∃ J, F (2 * J + 2) ^ 2 ≤ n ∧ n < F (2 * J + 4) ^ 2 := by
  have hex : ∃ j, n < F (2 * j + 4) ^ 2 := by
    refine ⟨n, ?_⟩
    have h1 : 2 ^ (n + 2) ≤ F (2 * (n + 2)) := (F_pow_two_mul (n + 2)).1 (by omega)
    have h2 : n < 2 ^ n := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ n ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 * (n + 2) = 2 * n + 4 := by ring
    rw [e] at h1
    have h4 : F (2 * n + 4) ≤ F (2 * n + 4) ^ 2 := by
      have := F_pos (2 * n + 4)
      nlinarith
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    simpa using hn
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have e : 2 * (Nat.find hex - 1) + 4 = 2 * Nat.find hex + 2 := by omega
    rw [e] at hmin
    exact not_lt.mp hmin

lemma sqrt_nat_ge_one (n : ℕ) (h : 1 ≤ n) : 1 ≤ Real.sqrt n := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_one] at h2

/-- The real-variable part of the Combine Smallest estimate. -/
lemma real_final (A Sq L χ T tail : ℝ) (hA0 : 0 ≤ A) (hSq : 1 ≤ Sq) (hl2L : Real.log 2 ≤ L)
    (hL2 : L ≤ 2 * Sq) (hA : A ≤ bL * L) (hχ : χ ≤ 2 * A + 3 * Sq)
    (hT : T ≤ χ * (2 * A + 7)) (htail : tail ≤ 2 * Sq) :
    16 * A + 2 * χ + T + tail ≤ C0 * Sq * L := by
  have hl2 := log_two_pos'
  have hb := bL_pos
  have hLpos : 0 < L := lt_of_lt_of_le hl2 hl2L
  have hA1 : 2 * χ + T ≤ (2 * A + 9) * (2 * A + 3 * Sq) := by
    have h1 : T ≤ χ * (2 * A + 7) := hT
    have h2 : χ * (2 * A + 9) ≤ (2 * A + 3 * Sq) * (2 * A + 9) :=
      mul_le_mul_of_nonneg_right hχ (by linarith)
    nlinarith
  have hexp : 16 * A + (2 * A + 9) * (2 * A + 3 * Sq) + 2 * Sq
      = 4 * A ^ 2 + 34 * A + 6 * A * Sq + 29 * Sq := by ring
  have t1 : 4 * A ^ 2 ≤ 8 * bL ^ 2 * Sq * L := by
    calc 4 * A ^ 2 ≤ 4 * (bL * L) ^ 2 := by gcongr
      _ = 4 * bL ^ 2 * L * L := by ring
      _ ≤ 4 * bL ^ 2 * L * (2 * Sq) := by gcongr
      _ = 8 * bL ^ 2 * Sq * L := by ring
  have t2 : 34 * A ≤ 34 * bL * Sq * L := by
    have h1 : 34 * A ≤ 34 * (bL * L) := by linarith
    have h2 : bL * L ≤ bL * L * Sq := by
      have : 0 ≤ bL * L := by positivity
      nlinarith
    nlinarith
  have t3 : 6 * A * Sq ≤ 6 * bL * Sq * L := by
    have h1 : A * Sq ≤ (bL * L) * Sq := by
      exact mul_le_mul_of_nonneg_right hA (by linarith)
    nlinarith
  have t4 : 29 * Sq ≤ 29 / Real.log 2 * Sq * L := by
    have h1 : 1 ≤ L / Real.log 2 := (one_le_div hl2).2 hl2L
    have e : 29 / Real.log 2 * Sq * L = 29 * Sq * (L / Real.log 2) := by
      field_simp
    rw [e]
    have h2 : 29 * Sq * 1 ≤ 29 * Sq * (L / Real.log 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hfinal : C0 * Sq * L = 8 * bL ^ 2 * Sq * L + 34 * bL * Sq * L + 6 * bL * Sq * L
      + 29 / Real.log 2 * Sq * L := by
    unfold C0
    ring
  calc 16 * A + 2 * χ + T + tail ≤ 16 * A + (2 * A + 9) * (2 * A + 3 * Sq) + 2 * Sq := by
        linarith
    _ = 4 * A ^ 2 + 34 * A + 6 * A * Sq + 29 * Sq := hexp
    _ ≤ 8 * bL ^ 2 * Sq * L + 34 * bL * Sq * L + 6 * bL * Sq * L
        + 29 / Real.log 2 * Sq * L := by linarith
    _ = C0 * Sq * L := hfinal.symm

theorem CS_large (n : ℕ) (hn : 1000 ≤ n) :
    |(CS n : ℝ) - combC * n| ≤ C0 * Real.sqrt n * Real.log n := by
  obtain ⟨J, hJ1, hJ2⟩ := exists_level n (by omega)
  obtain ⟨z, m, h, k, e, hz, hh, hT, hQ⟩ := chain n J hn hJ1 J (le_refl _)
  have hval : val (B z (2 * J) m h) = n := by
    have := hT.st.val_eq
    rw [val_start] at this
    exact this
  have hval2 : val z + m * F (2 * J + 2) + h * F (2 * J + 4) = n := by
    rw [val_B] at hval
    exact hval
  have hD : (D (B z (2 * J) m h) : ℝ) = e := by
    have := hT.dv
    rw [D_start, zero_add] at this
    rw [this]
  have hSteps : CS n = k + CSfrom (B z (2 * J) m h) := CSfrom_eq hT.st
  -- the real quantities
  have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hSq1 : 1 ≤ Real.sqrt n := sqrt_nat_ge_one n (by omega)
  have hSqSq : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
    (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  have hl2 := log_two_pos'
  have hL2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by linarith)
  have hL1 : Real.log n ≤ 2 * Real.sqrt n := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt n by linarith)
    have h2 := Real.log_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ (n : ℝ))
    linarith
  have hA : (J : ℝ) + 1 ≤ bL * Real.log n := by
    have hpow : 2 ^ (J + 1) ≤ F (2 * J + 2) := by
      have := (F_pow_two_mul (J + 1)).1 (by omega)
      have e : 2 * (J + 1) = 2 * J + 2 := by ring
      rwa [e] at this
    have hsq : (2 ^ (J + 1)) ^ 2 ≤ n :=
      le_trans (Nat.pow_le_pow_left hpow 2) hJ1
    have hr : ((2 : ℝ) ^ (J + 1)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsq
    have hlog : ((J : ℝ) + 1) * (2 * Real.log 2) ≤ Real.log n := by
      have h1 := Real.log_le_log (by positivity) hr
      have h2 : Real.log (((2 : ℝ) ^ (J + 1)) ^ 2) = ((J : ℝ) + 1) * (2 * Real.log 2) := by
        rw [Real.log_pow, Real.log_pow]
        push_cast
        ring
      rw [h2] at h1
      exact h1
    have e : bL * Real.log n = Real.log n / (2 * Real.log 2) := by
      unfold bL
      ring
    rw [e, le_div_iff₀ (by positivity)]
    exact hlog
  -- the bound on the number of chips
  have hFb0 : (0 : ℝ) < (F (2 * J + 4) : ℝ) := F_cast_pos _
  have hF20 : (0 : ℝ) < (F (2 * J + 2) : ℝ) := F_cast_pos _
  have hFb2 : (F (2 * J + 4) : ℝ) ≤ 3 * (F (2 * J + 2) : ℝ) := by
    exact_mod_cast F_add_two_le (2 * J)
  have hJ2R : (n : ℝ) < (F (2 * J + 4) : ℝ) ^ 2 := by exact_mod_cast hJ2
  have hSqFb : Real.sqrt n < (F (2 * J + 4) : ℝ) := (Real.sqrt_lt' hFb0).2 hJ2R
  have hmF : (m : ℝ) * (F (2 * J + 2) : ℝ) ≤ n := by
    have : m * F (2 * J + 2) ≤ n := by omega
    exact_mod_cast this
  have hm3 : (m : ℝ) ≤ 3 * Real.sqrt n := by
    have h1 : (n : ℝ) ≤ Real.sqrt n * (F (2 * J + 4) : ℝ) := by
      have h0 := mul_le_mul_of_nonneg_left (le_of_lt hSqFb) hSq0
      linarith [hSqSq]
    have h2 : Real.sqrt n * (F (2 * J + 4) : ℝ) ≤ Real.sqrt n * (3 * (F (2 * J + 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hFb2 hSq0
    have h3 : (m : ℝ) * (F (2 * J + 2) : ℝ) ≤ (3 * Real.sqrt n) * (F (2 * J + 2) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right h3 hF20
  have hchips : (chips (B z (2 * J) m h) : ℝ) ≤ 2 * ((J : ℝ) + 1) + 3 * Real.sqrt n := by
    have h1 := hz.chips_le _ _
    have h2 := chips_B z (2 * J) m h
    have h3 : chips (B z (2 * J) m h) ≤ 2 * J + m + 2 := by omega
    have h4 : (chips (B z (2 * J) m h) : ℝ) ≤ 2 * (J : ℝ) + (m : ℝ) + 2 := by exact_mod_cast h3
    linarith
  have hchips0 : (0 : ℝ) ≤ (chips (B z (2 * J) m h) : ℝ) := Nat.cast_nonneg _
  -- the remaining moves
  have hT1 : (CSfrom (B z (2 * J) m h) : ℝ) ≤
      (chips (B z (2 * J) m h) : ℝ) * (2 * ((J : ℝ) + 1) + 7) := by
    have h1 := CSfrom_le_Phi (B z (2 * J) m h)
    have h2 := Phi_le_chips_mul (B z (2 * J) m h) (2 * J + 6) (by
      intro i hi
      unfold B
      rw [Finsupp.add_apply, hz.top i (by omega), W_above (by omega)])
    push_cast at h2
    have e : (2 : ℝ) * (J : ℝ) + 6 + 3 = 2 * ((J : ℝ) + 1) + 7 := by ring
    rw [e] at h2
    linarith
  have hT0 : (0 : ℝ) ≤ (CSfrom (B z (2 * J) m h) : ℝ) := Nat.cast_nonneg _
  -- the tail of the series
  have htail0 := aT_tail_nonneg J
  have htail1 := aT_tail_le J
  have htail2 : (n : ℝ) * ∑' t, aT (t + J) ≤ 2 * Real.sqrt n := by
    have h1 : (n : ℝ) * ∑' t, aT (t + J) ≤ n * (2 * aT J) :=
      mul_le_mul_of_nonneg_left htail1 (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (2 * aT J) = 2 * ((n : ℝ) / (F (2 * J + 4) : ℝ)) := by
      unfold aT
      ring
    have h3 : (n : ℝ) / (F (2 * J + 4) : ℝ) ≤ Real.sqrt n := by
      rw [div_le_iff₀ hFb0]
      have h4 : Real.sqrt n * Real.sqrt n ≤ Real.sqrt n * (F (2 * J + 4) : ℝ) :=
        mul_le_mul_of_nonneg_left (le_of_lt hSqFb) hSq0
      linarith [hSqSq]
    linarith
  -- the counter and the assembly
  have hDA := D_approx (B z (2 * J) m h)
  rw [hval, hD] at hDA
  have hCS : (CS n : ℝ) = k + (CSfrom (B z (2 * J) m h) : ℝ) := by
    rw [hSteps]
    push_cast
    ring
  have hc : combC * (n : ℝ) = (n : ℝ) / 2 + rho * n + n * Ssum J + n * ∑' t, aT (t + J) := by
    rw [combC_eq, aT_split J]
    unfold rho
    ring
  rw [hCS, hc]
  rw [abs_le] at hQ hDA
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨hDA1, hDA2⟩ := hDA
  have hfin := real_final ((J : ℝ) + 1) (Real.sqrt n) (Real.log n)
    (chips (B z (2 * J) m h) : ℝ) (CSfrom (B z (2 * J) m h) : ℝ) ((n : ℝ) * ∑' t, aT (t + J))
    (by positivity) hSq1 hL2 hL1 hA hchips hT1 htail2
  have htail3 : 0 ≤ (n : ℝ) * ∑' t, aT (t + J) := mul_nonneg (Nat.cast_nonneg n) htail0
  rw [abs_le]
  constructor <;> linarith

lemma CS_nonneg_le (n : ℕ) : (CS n : ℝ) ≤ 3 * n := by
  have h := CSfrom_le_Phi (start n)
  rw [← CS_eq, Phi_start] at h
  have h1 := phi_sq
  have h2 := phi_lt_two
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- The Combine Smallest estimate for every `n ≥ 2`. -/
theorem CS_estimate :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(CS n : ℝ) - combC * n| ≤ C * Real.sqrt n * Real.log n := by
  have hl2 := log_two_pos'
  refine ⟨C0 + 3000 / Real.log 2, fun n hn => ?_⟩
  have hC0 := C0_pos
  have hq0 : (0 : ℝ) < 3000 / Real.log 2 := by positivity
  have hSq1 : 1 ≤ Real.sqrt n := sqrt_nat_ge_one n (by omega)
  have hL : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hL0 : 0 ≤ Real.log n := le_of_lt (lt_of_lt_of_le hl2 hL)
  have hprod : 0 ≤ Real.sqrt n * Real.log n := mul_nonneg (by linarith) hL0
  by_cases hbig : 1000 ≤ n
  · have h := CS_large n hbig
    have e : (C0 + 3000 / Real.log 2) * Real.sqrt n * Real.log n
        = C0 * Real.sqrt n * Real.log n + 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      ring
    rw [e]
    have : 0 ≤ 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := mul_nonneg (le_of_lt hq0) hprod
    linarith
  · have hsmall : (n : ℝ) ≤ 1000 := by
      have : n ≤ 1000 := by omega
      exact_mod_cast this
    have hle := CS_nonneg_le n
    have hge : (0 : ℝ) ≤ (CS n : ℝ) := Nat.cast_nonneg _
    have hbr := combC_bracket
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hc1 : combC * (n : ℝ) ≤ 2 * n := by nlinarith [hbr.2]
    have hc2 : 0 ≤ combC * (n : ℝ) := by nlinarith [hbr.1]
    have habs : |(CS n : ℝ) - combC * n| ≤ 3000 := by
      rw [abs_le]
      constructor <;> linarith
    have hprod1 : Real.log 2 ≤ Real.sqrt n * Real.log n := by nlinarith
    have hlast : (3000 : ℝ) ≤ 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      have h1 : 1 ≤ (Real.sqrt n * Real.log n) / Real.log 2 := (one_le_div hl2).2 hprod1
      have e : 3000 / Real.log 2 * (Real.sqrt n * Real.log n)
          = 3000 * ((Real.sqrt n * Real.log n) / Real.log 2) := by
        field_simp
      rw [e]
      linarith
    have e : (C0 + 3000 / Real.log 2) * Real.sqrt n * Real.log n
        = C0 * (Real.sqrt n * Real.log n) + 3000 / Real.log 2 * (Real.sqrt n * Real.log n) := by
      ring
    rw [e]
    have : 0 ≤ C0 * (Real.sqrt n * Real.log n) := mul_nonneg (le_of_lt hC0) hprod
    linarith

end Zeck
```

## `ZeckSS.lean`

```lean
/-
  Part (a) of MathDB 347063: the lower half of the Split Smallest estimate.
  A combine at index at least two only happens once every count is at most one,
  so the chip count is at most `2 log₂ n + 2` from that moment on.
-/
import ZeckChain

open Classical

set_option linter.unusedSimpArgs false

namespace Zeck

/-- A step never drops the potential by more than the bound on the index, and any excess is
paid for by a lost chip. -/
lemma step_excess (a : Pos) (n : ℕ) (hv : val a = n) (hm : hasMove a) :
    (dropSS a : ℝ) - 1 ≤ (2 * (Nat.log2 n : ℝ) + 1) * ((chips a : ℝ) - chips (stepSS a)) := by
  have hK : (0 : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by positivity
  unfold stepSS dropSS
  cases hsp : smallestSplit a with
  | some i =>
    dsimp only
    rw [chips_doSplit a i (smallestSplit_some_spec a hsp).1]
    simp
  | none =>
    dsimp only
    split_ifs with hA
    · have h1 := chips_doA1 a hA
      have h2 : (chips (doA1 a) : ℝ) + 1 = (chips a : ℝ) := by exact_mod_cast h1
      have h3 : (chips a : ℝ) - chips (doA1 a) = 1 := by linarith
      rw [h3]
      simp
      linarith
    · cases hco : smallestCons a with
      | some i =>
        dsimp only
        have hl := (smallestCons_some_spec a hco).1
        have h1 := chips_doCons a i hl
        have h2 : (chips (doCons a i) : ℝ) + 1 = (chips a : ℝ) := by exact_mod_cast h1
        have h3 : (chips a : ℝ) - chips (doCons a i) = 1 := by linarith
        rw [h3]
        have hi : i ≤ 2 * Nat.log2 n + 1 := idx_bound a n hv i hl.2.2
        have hi' : (i : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by exact_mod_cast hi
        linarith
      | none =>
        dsimp only
        exfalso
        rcases hm with ha | hc | hs
        · exact hA ha
        · exact (smallestCons_none_iff a).1 hco hc
        · exact (smallestSplit_none_iff a).1 hsp hs

lemma drop_ge_two_spec (a : Pos) (h : 2 ≤ dropSS a) : smallestSplit a = none ∧ ¬ legalA1 a := by
  unfold dropSS at h
  cases hsp : smallestSplit a with
  | some i =>
    rw [hsp] at h
    dsimp only at h
    omega
  | none =>
    rw [hsp] at h
    dsimp only at h
    split_ifs at h with hA
    · omega
    · exact ⟨rfl, hA⟩

/-- The excess is bounded by the chip count at the first genuine combine. -/
theorem SS_excess_le (n : ℕ) :
    Finset.sum (Finset.range (SS n)) (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1)
      ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by
  have hK : (0 : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 1 := by positivity
  by_cases hex : ∃ j, j < SS n ∧ 2 ≤ dropSS (run stepSS (start n) j)
  · let j0 := Nat.find hex
    have hj0 : j0 < SS n ∧ 2 ≤ dropSS (run stepSS (start n) j0) := Nat.find_spec hex
    have hmin : ∀ t, t < j0 → t < SS n → dropSS (run stepSS (start n) t) ≤ 1 := by
      intro t ht htN
      by_contra hc
      exact Nat.find_min hex ht ⟨htN, by omega⟩
    have hspec := drop_ge_two_spec _ hj0.2
    have hchips : chips (run stepSS (start n) j0) ≤ 2 * Nat.log2 n + 2 :=
      chips_le_of_all_one _ n (runSS_val n j0) (runSS_zero n j0)
        (stepSS_cons_le_one _ hspec.1 hspec.2)
    let G : ℕ → ℝ := fun t =>
      if t ≤ j0 then (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2)
      else (2 * (Nat.log2 n : ℝ) + 1) * (chips (run stepSS (start n) t) : ℝ)
    have hG0 : G 0 = (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by
      simp [G]
    have hGnn : ∀ t, 0 ≤ G t := by
      intro t
      simp only [G]
      split_ifs
      · positivity
      · positivity
    have hstep : ∀ t, t ≤ SS n →
        Finset.sum (Finset.range t) (fun j => (dropSS (run stepSS (start n) j) : ℝ) - 1) + G t
          ≤ G 0 := by
      intro t
      induction t with
      | zero =>
        intro _
        simp
      | succ t ih =>
        intro ht
        have ih' := ih (by omega)
        rw [Finset.sum_range_succ]
        have htN : t < SS n := by omega
        have hm : hasMove (run stepSS (start n) t) :=
          gameLen_min stepSS stepSS_drop (start n) t htN
        have hdiff := step_excess _ n (runSS_val n t) hm
        have hK1 : (0 : ℝ) ≤ (2 * (Nat.log2 n : ℝ) + 1) := hK
        have key : (dropSS (run stepSS (start n) t) : ℝ) - 1 + G (t + 1) ≤ G t := by
          by_cases h1 : t < j0
          · have hd := hmin t h1 htN
            have hd' : (dropSS (run stepSS (start n) t) : ℝ) ≤ 1 := by exact_mod_cast hd
            have ht1 : t + 1 ≤ j0 := by omega
            have ht2 : t ≤ j0 := by omega
            simp only [G, ht1, ht2, ite_true]
            linarith
          · by_cases h2 : t = j0
            · have ht1 : ¬ t + 1 ≤ j0 := by omega
              have ht2 : t ≤ j0 := by omega
              simp only [G, ht1, ht2, ite_true, ite_false]
              have hc' : (chips (run stepSS (start n) j0) : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 2 := by
                exact_mod_cast hchips
              rw [← h2] at hc'
              have h3 : (2 * (Nat.log2 n : ℝ) + 1) * (chips (run stepSS (start n) t) : ℝ)
                  ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) :=
                mul_le_mul_of_nonneg_left hc' hK1
              rw [run_succ] at *
              nlinarith
            · have ht1 : ¬ t + 1 ≤ j0 := by omega
              have ht2 : ¬ t ≤ j0 := by omega
              simp only [G, ht1, ht2, ite_false]
              rw [run_succ]
              nlinarith
        linarith
    have hN := hstep (SS n) (le_refl _)
    rw [hG0] at hN
    have := hGnn (SS n)
    linarith
  · have hall : ∀ j ∈ Finset.range (SS n), (dropSS (run stepSS (start n) j) : ℝ) - 1 ≤ 0 := by
      intro j hj
      have hjN : j < SS n := Finset.mem_range.1 hj
      have h1 : dropSS (run stepSS (start n) j) ≤ 1 := by
        by_contra hc
        exact hex ⟨j, hjN, by omega⟩
      have h2 : (dropSS (run stepSS (start n) j) : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
    have hsum := Finset.sum_nonpos hall
    have hpos : (0 : ℝ) ≤ (2 * (Nat.log2 n : ℝ) + 1) * (2 * (Nat.log2 n : ℝ) + 2) := by positivity
    linarith

/-- The Split Smallest deficit at the end of the game. -/
lemma SS_final_Phi_le (n : ℕ) :
    Phi (run stepSS (start n) (SS n)) ≤ (2 * (Nat.log2 n : ℝ) + 2) * (2 * (Nat.log2 n : ℝ) + 4) := by
  have hterm : ¬ hasMove (run stepSS (start n) (SS n)) :=
    gameLen_spec stepSS stepSS_drop (start n)
  have hchips : chips (run stepSS (start n) (SS n)) ≤ 2 * Nat.log2 n + 2 :=
    chips_le_of_all_one _ n (runSS_val n _) (runSS_zero n _)
      (fun j hj => terminal_le_one _ hterm hj)
  have hc' : (chips (run stepSS (start n) (SS n)) : ℝ) ≤ 2 * (Nat.log2 n : ℝ) + 2 := by
    exact_mod_cast hchips
  have hP := Phi_le_chips_mul (run stepSS (start n) (SS n)) (2 * Nat.log2 n + 1) (by
    intro i hi
    by_contra hc
    have : 1 ≤ (run stepSS (start n) (SS n)) i := by omega
    have := runSS_idx n (SS n) i this
    omega)
  push_cast at hP
  have hL : (0 : ℝ) ≤ (Nat.log2 n : ℝ) := Nat.cast_nonneg _
  have e : (2 * (Nat.log2 n : ℝ) + 1 + 3) = 2 * (Nat.log2 n : ℝ) + 4 := by ring
  rw [e] at hP
  have h4 : (chips (run stepSS (start n) (SS n)) : ℝ) * (2 * (Nat.log2 n : ℝ) + 4)
      ≤ (2 * (Nat.log2 n : ℝ) + 2) * (2 * (Nat.log2 n : ℝ) + 4) :=
    mul_le_mul_of_nonneg_right hc' (by positivity)
  linarith

/-- The Split Smallest estimate. -/
theorem SS_estimate :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨40 / (Real.log 2) ^ 2, fun n hn => ?_⟩
  have hdef := SS_deficit n
  have hex := SS_excess_nonneg n
  have hP0 := Phi_nonneg (run stepSS (start n) (SS n))
  have hEx := SS_excess_le n
  have hPh := SS_final_Phi_le n
  set l : ℝ := (Nat.log2 n : ℝ) with hl
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hdef1 : phi ^ 2 * n - (SS n : ℝ) ≤ 10 * (l + 1) ^ 2 := by
    rw [hdef]
    nlinarith
  have hdef0 : 0 ≤ phi ^ 2 * n - (SS n : ℝ) := by
    rw [hdef]
    linarith
  have hlog : l + 1 ≤ 2 * Real.log n / Real.log 2 := by
    have hn0 : n ≠ 0 := by omega
    have hp := Nat.pow_log_le_self 2 hn0
    rw [← Nat.log2_eq_log_two] at hp
    have hpR : (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) := by exact_mod_cast hp
    have hlogp := Real.log_le_log (by positivity) hpR
    rw [Real.log_pow] at hlogp
    have h2n : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have e1 : l * Real.log 2 ≤ Real.log n := hlogp
    have e2 : 2 * Real.log n / Real.log 2 = (2 * Real.log n) * (1 / Real.log 2) := by ring
    rw [le_div_iff₀ hl2]
    nlinarith
  have hsq : (l + 1) ^ 2 ≤ (2 * Real.log n / Real.log 2) ^ 2 := by
    have h0 : 0 ≤ l + 1 := by linarith
    gcongr
  have e3 : 10 * (2 * Real.log n / Real.log 2) ^ 2 = 40 / (Real.log 2) ^ 2 * (Real.log n) ^ 2 := by
    field_simp
    ring
  rw [abs_sub_comm, abs_of_nonneg hdef0]
  calc phi ^ 2 * n - (SS n : ℝ) ≤ 10 * (l + 1) ^ 2 := hdef1
    _ ≤ 10 * (2 * Real.log n / Real.log 2) ^ 2 := by gcongr
    _ = 40 / (Real.log 2) ^ 2 * (Real.log n) ^ 2 := e3

end Zeck
```

## `ZeckEndpoint.lean`

```lean
/-
  MathDB 347063: the two endpoint theorems.

  The game is the source game of Li--Li--Miller--Mizgerd--Sun--Xia--Zhou: `n` chips of value
  `F 1` initially, not the Zeckendorf decomposition named in the MathDB record (from which no
  move is legal, as `Zeck.CS_zeckendorf_zero` records).  `phi = (1 + √5) / 2`.
-/
import ZeckCS
import ZeckSS

open Classical

namespace Zeck

/-- Split Smallest, part (a): the number of moves is `phi^2 * n + O((log n)^2)`. -/
theorem split_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(SS n : ℝ) - phi ^ 2 * n| ≤ C * (Real.log n) ^ 2 :=
  SS_estimate

/-- Combine Smallest, part (b): the number of moves is `c * n + O(√n log n)` with
`c = 5/2 - phi + ∑_{j ≥ 2} 1 / F_{2j}`. -/
theorem combine_smallest_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(CS n : ℝ) - (5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ)) * n|
        ≤ C * Real.sqrt n * Real.log n :=
  CS_estimate

/-- The numerical bracket for the Combine Smallest constant. -/
theorem combine_constant_bracket :
    (1.206 : ℝ) < 5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) ∧
      5 / 2 - phi + ∑' j : ℕ, 1 / (F (2 * (j + 2)) : ℝ) < 1.207 :=
  combC_bracket

end Zeck
```

## `ZeckAudit2.lean`

```lean
/-
  Axiom audit for the new modules of the second lane of MathDB 347063.
  Only propext, Classical.choice and Quot.sound are permitted.
-/
import ZeckEndpoint

#print axioms Zeck.Steps.trans
#print axioms Zeck.CSfrom_eq
#print axioms Zeck.Phi_stepCS_le
#print axioms Zeck.CSfrom_le_Phi
#print axioms Zeck.Tr.trans
#print axioms Zeck.Tr_Cp
#print axioms Zeck.Tr_Cp1
#print axioms Zeck.Tr_Cp2
#print axioms Zeck.Tr_Cp3
#print axioms Zeck.Tr_Sp
#print axioms Zeck.Tr_S2
#print axioms Zeck.Tr_A1
#print axioms Zeck.Tr_low_cons
#print axioms Zeck.Tr_low_split
#print axioms Zeck.Tr_low_split2
#print axioms Zeck.cascade
#print axioms Zeck.pending
#print axioms Zeck.macro_step
#print axioms Zeck.macro_step0
#print axioms Zeck.macro_loop
#print axioms Zeck.macro_loop0
#print axioms Zeck.exit_step
#print axioms Zeck.exit_step0
#print axioms Zeck.level_step
#print axioms Zeck.start_phase
#print axioms Zeck.Zk.val_lt
#print axioms Zeck.Zk.chips_le
#print axioms Zeck.combC_bracket
#print axioms Zeck.D_approx
#print axioms Zeck.Phi_le_chips_mul
#print axioms Zeck.chain
#print axioms Zeck.real_final
#print axioms Zeck.CS_large
#print axioms Zeck.CS_estimate
#print axioms Zeck.step_excess
#print axioms Zeck.SS_excess_le
#print axioms Zeck.SS_final_Phi_le
#print axioms Zeck.SS_estimate
#print axioms Zeck.split_smallest_asymptotic
#print axioms Zeck.combine_smallest_asymptotic
#print axioms Zeck.combine_constant_bracket
```

## `ZeckAudit3.lean`

```lean
/-
  Axiom audit for the rotation and cycle theorems of the second lane of MathDB 347063.
  Only propext, Classical.choice and Quot.sound are permitted.
-/
import ZeckEndpoint
import ZeckRotation

#print axioms Zeck.macro_rot
#print axioms Zeck.macro_rotation
#print axioms Zeck.macro_iter
#print axioms Zeck.Zk.eq_of_val
#print axioms Zeck.Steps_chips
#print axioms Zeck.cassini_even
#print axioms Zeck.rotation_cycle
```
