import Antimagic6ABinaryInternal
namespace Antimagic.Round6A
open Finset Round5A

theorem binary_rootColor (n : ℕ) (hn : 3 ≤ n) : rootColor 2 n=3*center 2 n := by
  have hd := rootColor_double 2 n (by omega) hn
  have hc := binary_center n hn
  have hl := internalEdges_lower 2 n hn
  norm_num only at hd
  omega

/-- Literal binary root weight, for any realization of the frozen formula. -/
theorem binary_root_weight (n : ℕ) (hn : 3 ≤ n) (f : Labeling (tree 2 n))
    (hf : ∀ a : Nonroot 2 n, (f (incomingEdge (by omega) a)).val+1=
      label 2 n a.val.1.val a.val.2.val) :
    weight (tree 2 n) f (root 2 n)=3*center 2 n := by
  rw [Round3.literal_weight_row (by omega) f hf _ (by change 0<n; omega)]
  change (if 0<0 then _ else 0)+(∑ j : Fin 2, label 2 n 1 (2*0+j.val))=_
  simp only [show ¬ (0<0) by omega,ite_false,Nat.zero_add,Nat.mul_zero]
  simp_rw [label_large 2 n _ _ hn]
  simp only [largeLabel,show 1<n by omega,ite_true]
  rw [Fin.sum_univ_eq_sum_range]
  exact binary_rootColor n hn

/-- Both patched row-one weights are fixed symbolic expressions. -/
theorem binary_first_weight (n : ℕ) (hn : 3 ≤ n) (f : Labeling (tree 2 n))
    (hf : ∀ a : Nonroot 2 n, (f (incomingEdge (by omega) a)).val+1=
      label 2 n a.val.1.val a.val.2.val)
    (v : Vertex 2 n) (hv : v.1.val=1) :
    weight (tree 2 n) f v=if v.2.val=0 then 3*center 2 n+1 else 4*center 2 n-1 := by
  have hr := Round3.literal_weight_row (by omega) f hf v (by change v.1.val<n; omega)
  have hd : 0<depth v := by change 0<v.1.val; omega
  rw [ite_eq_left hd] at hr
  simp_rw [label_large 2 n _ _ hn] at hr
  have hm : v.1.val<n := by omega
  have hc : v.1.val+1<n := by omega
  simp only [largeLabel,hm,hc,ite_true] at hr
  simp only [hv,Nat.reduceAdd] at hr
  have hb : v.2.val<2 := by have := v.2.isLt; simpa only [hv,pow_one] using this
  have he := binary_row_two n hn
  have hz : 3 ≤ center 2 n := by have := internalEdges_lower 2 n hn; have := binary_center n hn; norm_num only at *; omega
  have hN := binary_center n hn
  rw [Fin.sum_univ_two] at hr
  by_cases hi : v.2.val=0
  · simp only [hi,Nat.mul_zero,Nat.zero_add,Fin.val_zero,Fin.val_one] at hr
    rw [he.1,he.2.1] at hr
    simp only [internalLabel,ite_true] at hr
    simp only [hi,ite_true]
    omega
  · have hi1 : v.2.val=1 := by omega
    simp only [hi1,Fin.val_zero,Fin.val_one] at hr
    norm_num only at hr
    rw [he.2.2.1,he.2.2.2] at hr
    simp only [internalLabel,ite_true,Nat.one_ne_zero,ite_false] at hr
    simp only [hi,ite_false]
    omega

/-- The root and either first-row vertex are separated by the binary patch. -/
theorem binary_root_separation (n : ℕ) (hn : 3 ≤ n) :
    3*center 2 n ≠ 3*center 2 n+1 ∧ 3*center 2 n ≠ 4*center 2 n-1 := by
  have := internalEdges_lower 2 n hn
  have := binary_center n hn
  norm_num only at *
  omega

#print axioms binary_root_weight
#print axioms binary_first_weight
#print axioms binary_root_separation
end Antimagic.Round6A
