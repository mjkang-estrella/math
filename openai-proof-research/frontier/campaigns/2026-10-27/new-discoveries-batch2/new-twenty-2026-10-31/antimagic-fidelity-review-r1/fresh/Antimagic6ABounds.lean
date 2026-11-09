import AntimagicFinal5A
import Mathlib.Tactic.Ring
namespace Antimagic.Round6A
open Finset Round5A

theorem internalEdges_succ (t n : ℕ) (hn : 1 ≤ n) :
    internalEdges t (n+1) = internalEdges t n + t^n := by
  simp [internalEdges, sum_range_succ, hn]

/-- The geometric tail fits into two copies of its final row. -/
theorem internalEdges_upper (t n : ℕ) (ht : 2 ≤ t) (hn : 2 ≤ n) :
    internalEdges t n + 2 ≤ 2 * t^(n-1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hb : n = 1
    · subst n
      simp [internalEdges, sum_range_succ]
      omega
    · have hn2 : 2 ≤ n := by omega
      have hi := ih hn2
      rw [internalEdges_succ t n (by omega)]
      have hp : t^n = t^(n-1)*t := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      simp only [Nat.add_sub_cancel]
      rw [hp]
      nlinarith

theorem internalEdges_geometric (t n : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) :
    (t-1)*internalEdges t n+t=t^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hb : n=0
    · subst n; simp [internalEdges]
    · have hi := ih (by omega)
      rw [internalEdges_succ t n (by omega),pow_succ]
      have ht1 : t-1+1=t := by omega
      calc
        _ = ((t-1)*internalEdges t n+t)+(t-1)*t^n := by ring
        _ = t^n+(t-1)*t^n := by rw [hi]
        _ = ((t-1)+1)*t^n := by ring
        _ = t^n*t := by rw [ht1,Nat.mul_comm]

theorem center_le_last_row (t n : ℕ) (ht : 2 ≤ t) (hn : 3 ≤ n) :
    center t n ≤ t^(n-1) := by
  have := internalEdges_upper t n ht (by omega)
  unfold center
  omega

theorem center_mul_ge_internal (s n : ℕ) (hs : 1 ≤ s) (hn : 3 ≤ n) :
    internalEdges (2*s) n ≤ (2*s)*center (2*s) n := by
  have hz := shell_size (2*s) n (show Even (2*s) from ⟨s,by omega⟩) hn
  have he := internalEdges_split (2*s) n (by omega)
  have hZ : 1 ≤ center (2*s) n := by simp [center]
  have hEq : internalEdges (2*s) n+2=2*center (2*s) n+2*s := by omega
  have hmul := Nat.mul_le_mul_right (center (2*s) n-1) hs
  have hmulEq : s*(center (2*s) n-1)+s=s*center (2*s) n := by
    rw [← Nat.mul_succ]; congr 1
  have hcenterEq : center (2*s) n-1+1=center (2*s) n := by omega
  nlinarith

theorem internalEdges_lower (t n : ℕ) (hn : 3 ≤ n) :
    t+t^2 ≤ internalEdges t n := by
  have h1 := internalEdges_split t n (by omega)
  have h2 := offset_step t n 1 (by omega)
  norm_num only at h2
  omega

/-- The last-parent colour exceeds every edge label. -/
theorem leafConstant_large (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    internalEdges (2*s) n + (2*s)^n < leafConstant s n := by
  have hpow : (2*s)^n = (2*s)^(n-1)*(2*s) := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hN := internalEdges_lower (2*s) n hn
  unfold leafConstant
  have hmul := Nat.mul_le_mul_right (2*internalEdges (2*s) n+(2*s)*(2*s)^(n-1)+1) hs
  rw [hpow]
  rw [Nat.mul_comm ((2*s)^(n-1)) (2*s)]
  omega

#print axioms center_le_last_row
#print axioms center_mul_ge_internal
#print axioms leafConstant_large
end Antimagic.Round6A
