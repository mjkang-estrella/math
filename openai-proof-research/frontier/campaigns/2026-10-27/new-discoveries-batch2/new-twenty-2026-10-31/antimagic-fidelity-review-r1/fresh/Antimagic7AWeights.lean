import Antimagic7ABijection
namespace Antimagic.Round7A
open Finset Round4A Round5A Round6A

theorem internal_children_sum (n h i : ℕ) (hh : 2 ≤ h) (hn : h+1<n) (hi : i<2^h) :
    (∑ j ∈ range 2, internalLabel 2 n (h+1) (2*i+j))=2*center 2 n := by
  obtain ⟨b,hb⟩ := offset_even 2 n (h+1) (by decide) (by omega)
  have hp : 2*i+2 ≤ 2^(h+1) := by rw [pow_succ]; omega
  have hc := coordinate_bound 2 n (h+1) (2*i+1) (by omega) hn (by omega)
  have hz := shell_size 2 n (by decide) (by omega)
  have hed := internalEdges_split 2 n (by omega)
  rw [hb] at hc
  calc
    _ = ∑ j ∈ range 2, shellEntry (center 2 n) (2*(b+i)+j) := by
      apply sum_congr rfl
      intro j _
      rw [binary_internal_shell n (h+1) _ (by omega)]
      simp only [patchedIndex,show h+1≠2 by omega, and_false, false_and, ite_false]
      congr 1
      omega
    _ = _ := by simpa using shellEntry_sum (center 2 n) (b+i) 1 (by omega)

theorem leaf_parent_sum (n i : ℕ) (hn : 3 ≤ n) (hi : i<2^(n-1)) :
    internalLabel 2 n (n-1) i + (∑ j ∈ range 2, largeLabel 2 n n (2*i+j))=leafConstant 1 n := by
  have ha := parentParameter_range n i hn hi
  have hp := even_power 2 (n-1) (by decide) (by omega)
  have hsum := leafEntry_sum 1 (2^(n-1)/2) (parentParameter 2 n i) (by decide) (by omega)
  have hc := parent_cancel n i hn hi
  have htotal : (∑ j ∈ range 2, largeLabel 2 n n (2*i+j)) =
      2*internalEdges 2 n+∑ j ∈ range 2, leafEntry 1 (2^(n-1)/2) (parentParameter 2 n i) j := by
    calc
      _ = ∑ j ∈ range 2, (internalEdges 2 n+leafEntry 1 (2^(n-1)/2) (parentParameter 2 n i) j) := by
        apply sum_congr rfl
        intro j hj
        rw [leaf_formula n _ hn]
        have hj' := mem_range.mp hj
        rw [show (2*i+j)/2=i by omega,show (2*i+j)%2=j by omega]
      _ = _ := by rw [sum_add_distrib]; simp
  rw [← hp] at hsum
  rw [htotal]
  unfold leafConstant
  norm_num only at *
  omega
theorem middle_weight (n : ℕ) (hn : 3  ≤  n)
    (v : Vertex 2 n) (hv : 2  ≤  v.1.val) (hm : v.1.val+1 < n) :
    weight (tree 2 n) (higherLabeling n hn) v =
      internalLabel 2 n v.1.val v.2.val + 2*center 2 n := by
  have hrow := Round3.literal_weight_row (by omega : 0 < 2)
    (higherLabeling n hn) (higherLabeling_label n hn) v
    (by change v.1.val < n; omega)
  have hsum : (∑ j : Fin 2, label 2 n (v.1.val+1) (2*v.2.val+j.val)) =
      2*center 2 n := by
    simp_rw [label_large 2 n _ _ hn]
    simp only [largeLabel,hm,ite_true]
    rw [Fin.sum_univ_eq_sum_range (fun j => internalLabel 2 n (v.1.val+1) (2*v.2.val+j))]
    exact internal_children_sum n v.1.val v.2.val hv hm v.2.isLt
  rw [hsum] at hrow
  have hd : 0 < depth v := by change 0 < v.1.val; omega
  rw [ite_eq_left hd,label_large 2 n _ _ hn] at hrow
  have hi : v.1.val < n := by omega
  rw [show largeLabel 2 n v.1.val v.2.val = internalLabel 2 n v.1.val v.2.val by simp [largeLabel,hi]] at hrow
  exact hrow

/-- Constant colour of every actual leaf parent, for the already-built equivalence. -/
theorem last_parent_weight (n : ℕ) (hn : 3  ≤  n)
    (v : Vertex 2 n) (hv : v.1.val = n-1) :
    weight (tree 2 n) (higherLabeling n hn) v = leafConstant 1 n := by
  have hrow := Round3.literal_weight_row (by omega : 0 < 2)
    (higherLabeling n hn) (higherLabeling_label n hn) v
    (by change v.1.val < n; omega)
  have hd : 0 < depth v := by change 0 < v.1.val; omega
  rw [ite_eq_left hd] at hrow
  simp_rw [label_large 2 n _ _ hn] at hrow
  have hi : v.1.val < n := by omega
  rw [show largeLabel 2 n v.1.val v.2.val = internalLabel 2 n v.1.val v.2.val by simp [largeLabel,hi]] at hrow
  have hsum : (∑ j : Fin 2, largeLabel 2 n (v.1.val+1) (2*v.2.val+j.val)) =
      ∑ j ∈ range 2, largeLabel 2 n n (2*v.2.val+j) := by
    rw [show v.1.val+1=n by omega,Fin.sum_univ_eq_sum_range (fun j => largeLabel 2 n n (2*v.2.val+j))]
  rw [hsum] at hrow
  conv at hrow => rhs; arg 1; arg 3; rw [hv]
  rw [hrow]
  exact leaf_parent_sum n v.2.val hn (by simpa only [hv] using v.2.isLt)

theorem leaf_weight (n : ℕ) (hn : 3  ≤  n)
    (v : Vertex 2 n) (hv : depth v = n) :
    weight (tree 2 n) (higherLabeling n hn) v = label 2 n v.1.val v.2.val := by
  rw [weight_bottom (by omega) (by omega) _ v hv,higherLabeling_label]

#print axioms middle_weight
#print axioms last_parent_weight
#print axioms leaf_weight
end Antimagic.Round7A
