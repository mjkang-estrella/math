import DepthDefs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
@[simp] theorem depth_zero : depth 0 = 0 := rfl
theorem depth_eq (k : ℕ) (hk : 1 ≤ k) :
    depth k = k^2 * (depth (k-1) + k + 10) := by
  cases k with
  | zero => omega
  | succ n => simp [depth]
theorem depth_lower (k : ℕ) : k^2 * (k+10) ≤ depth k := by
  cases k with
  | zero => simp [depth]
  | succ n => simp only [depth]; nlinarith
theorem depth_strictMono : StrictMono depth := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [depth]
  have : 1 ≤ (n+1)^2 := by exact Nat.one_le_pow _ _ (by omega)
  nlinarith [Nat.mul_le_mul_right (depth n + (n+1)+10) this]
theorem index_le_depth (k : ℕ) : k ≤ depth k := by
  have := depth_strictMono.id_le k
  simpa [depth] using this
theorem room (k : ℕ) (hk : 3 ≤ k) :
    anchorLength k + terminalLength k + 1 ≤ depth k := by
  rw [depth_eq k (by omega)]
  unfold anchorLength terminalLength
  have : 1 ≤ k^2 := by nlinarith
  nlinarith [Nat.mul_le_mul_right (depth (k-1)+k+10) this]
theorem decomposition (k : ℕ) (hk : 3 ≤ k) :
    depth k = anchorLength k + blockCount k * k + tailRemainder k + terminalLength k := by
  have h := room k hk
  have hd := Nat.mod_add_div (remainderLength k) k
  unfold blockCount tailRemainder
  unfold remainderLength at *
  rw [Nat.mul_comm k] at hd
  omega
theorem tail_lt (k : ℕ) (hk : 3 ≤ k) : tailRemainder k < k :=
  Nat.mod_lt _ (by omega)
theorem free_le (k : ℕ) (hk : 3 ≤ k) : freeCount k ≤ depth k - 1 := by
  have h := decomposition k hk
  have hm : (k-2)*blockCount k ≤ k*blockCount k :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [Nat.mul_comm k] at hm
  unfold freeCount anchorLength terminalLength at *
  omega
theorem deficit_add_free (k : ℕ) (hk : 3 ≤ k) :
    deficit k + freeCount k = depth k - 1 := by
  exact Nat.sub_add_cancel (free_le k hk)
theorem previous_bound (k : ℕ) (hk : 1 ≤ k) : depth (k-1)*k^2 ≤ depth k := by
  rw [depth_eq k hk]; nlinarith
theorem deficit_bound (k : ℕ) (hk : 3 ≤ k) :
    deficit k * k^2 ≤ (2*k+1)*depth k + (3*k+5)*k^2 := by
  have hd := decomposition k hk
  have ht := tail_lt k hk
  have hf := deficit_add_free k hk
  have hr := room k hk
  have hp := previous_bound k (by omega)
  have hs : k - 2 + 2 = k := by omega
  have he : freeCount k + 2*blockCount k = k*blockCount k := by
    unfold freeCount
    nlinarith [congrArg (fun t : ℕ => t * blockCount k) hs]
  have hb : blockCount k * k ≤ depth k := by omega
  have hD : deficit k * k ≤ 2*depth k + (depth (k-1)+3*k+5)*k := by
    unfold anchorLength terminalLength at hd hr
    have hn : depth k - 1 + 1 = depth k := by omega
    nlinarith
  nlinarith [Nat.mul_le_mul_right k hD]
theorem deficit_linear_bound (k : ℕ) (hk : 3 ≤ k) :
    deficit k * k ≤ 4 * depth k := by
  have h := deficit_bound k hk
  have hl := depth_lower k
  have ha : 3*k+5 ≤ k*(k+10) := by nlinarith
  have hb : (3*k+5)*k^2 ≤ k*depth k := by
    nlinarith [Nat.mul_le_mul_right (k^2) ha, Nat.mul_le_mul_left k hl]
  nlinarith
end CascadeRate
