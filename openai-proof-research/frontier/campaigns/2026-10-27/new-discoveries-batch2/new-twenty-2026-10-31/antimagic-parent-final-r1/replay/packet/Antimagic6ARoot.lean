import Antimagic6ABounds
namespace Antimagic.Round6A
open Finset Round5A

def rootColor (t n : ℕ) : ℕ := ∑ i ∈ range t, internalLabel t n 1 i

theorem rootColor_double (t n : ℕ) (ht : 2 ≤ t) (hn : 3 ≤ n) :
    2 * rootColor t n = 2*center t n + (t-1)*(2*internalEdges t n-t+2) := by
  have hN := internalEdges_lower t n hn
  unfold rootColor
  nth_rw 1 [show t = (t-1)+1 by omega]
  rw [sum_range_succ']
  have he : (∑ i ∈ range (t-1), internalLabel t n 1 (i+1)) =
      (t-1)*(internalEdges t n-t+2) + ∑ i ∈ range (t-1), i := by
    calc
      _ = ∑ i ∈ range (t-1), (internalEdges t n-t+2+i) := by
        apply sum_congr rfl
        intro i _
        simp only [internalLabel, ite_true, show i+1 ≠ 0 by omega, ite_false]
        omega
      _ = _ := by rw [sum_add_distrib]; simp
  rw [he]
  simp only [internalLabel, ite_true]
  have htri := sum_range_id_mul_two (t-1)
  have ht1 : t-1+1=t := by omega
  have ht2 : t-1-1+2=t := by omega
  have hNt : internalEdges t n-t+t=internalEdges t n := by omega
  have h2Nt : 2*internalEdges t n-t+t=2*internalEdges t n := by omega
  nlinarith

theorem root_weight (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    weight (tree (2*s) n) (higherLabeling s n hs hn) (root (2*s) n) = rootColor (2*s) n := by
  rw [Round3.literal_weight_row (by omega) _ (higherLabeling_label s n hs hn) _ (by change 0<n; omega)]
  change (if 0<0 then _ else 0) + (∑ j : Fin (2*s), label (2*s) n 1 ((2*s)*0+j.val)) = _
  simp only [show ¬ (0<0) by omega,ite_false,Nat.zero_add,Nat.mul_zero]
  simp_rw [label_large (2*s) n _ _ hn]
  simp only [largeLabel,show 1<n by omega,ite_true]
  exact Fin.sum_univ_eq_sum_range (fun i => internalLabel (2*s) n 1 i) (2*s)

/-- Root weights lie in the leaf-label band and above all middle weights. -/
theorem rootColor_bounds (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    internalEdges (2*s) n < rootColor (2*s) n ∧
    rootColor (2*s) n ≤ internalEdges (2*s) n + (2*s)^n ∧
    internalEdges (2*s) n + (2*s)*center (2*s) n < rootColor (2*s) n := by
  have hd := rootColor_double (2*s) n (by omega) hn
  have hz := shell_size (2*s) n (show Even (2*s) from ⟨s,by omega⟩) hn
  have hN := internalEdges_lower (2*s) n hn
  have hu := internalEdges_upper (2*s) n (by omega) (by omega)
  have hc := center_le_last_row (2*s) n (by omega) hn
  have hg := internalEdges_geometric (2*s) n (by omega) (by omega)
  have hpos : 0 ≤ (s-2)*internalEdges (2*s) n := Nat.zero_le _
  have hs2 : s-2+2=s := by omega
  have hZ : 1 ≤ center (2*s) n := by simp [center]
  have hp : (2*s)^n = (2*s)^(n-1)*(2*s) := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hsub : internalEdges (2*s) n-2*s+2*s=internalEdges (2*s) n := by omega
  have hsub2 : 2*internalEdges (2*s) n-2*s+2*s=2*internalEdges (2*s) n := by omega
  have ht1 : 2*s-1+1=2*s := by omega
  have hlin : 2*internalEdges (2*s) n-2*s+2=internalEdges (2*s) n+2*center (2*s) n := by omega
  have hprod : (2*s-1)*center (2*s) n+center (2*s) n=(2*s)*center (2*s) n := by
    rw [← Nat.succ_mul,show (2*s-1).succ=2*s by omega]
  have hroot : 2*rootColor (2*s) n=2*((2*s)*center (2*s) n)+(2*s-1)*internalEdges (2*s) n := by
    rw [hlin] at hd
    nlinarith only [hd,hprod]
  have hNpos : 0 < internalEdges (2*s) n := by nlinarith
  have hsep := Nat.mul_le_mul_right (internalEdges (2*s) n) (show 3≤2*s-1 by omega)
  have hsep' : internalEdges (2*s) n+(2*s)*center (2*s) n<rootColor (2*s) n := by
    nlinarith only [hroot,hsep,hNpos]
  refine ⟨by omega,?_,hsep'⟩
  have hZN : center (2*s) n ≤ internalEdges (2*s) n := by omega
  have hmul := Nat.mul_le_mul_left (2*s-1)
    (show 2*internalEdges (2*s) n-2*s+2≤2*internalEdges (2*s) n by omega)
  nlinarith only [hd,hmul,hg,hZN]

#print axioms root_weight
#print axioms rootColor_bounds
end Antimagic.Round6A
