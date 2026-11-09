import Antimagic5ABijection
namespace Antimagic.Round5A
open Finset

/-- The middle-row sum identity transported to the literal graph incidence weight. -/
theorem middle_weight (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (v : Vertex (2*s) n) (hv : 1 ≤ v.1.val) (hm : v.1.val+1 < n) :
    weight (tree (2*s) n) (higherLabeling s n hs hn) v =
      internalLabel (2*s) n v.1.val v.2.val + (2*s)*center (2*s) n := by
  have hrow := Round3.literal_weight_row (by omega : 0 < 2*s)
    (higherLabeling s n hs hn) (higherLabeling_label s n hs hn) v
    (by change v.1.val < n; omega)
  have hsum : (∑ j : Fin (2*s), label (2*s) n (v.1.val+1) ((2*s)*v.2.val+j.val)) =
      (2*s)*center (2*s) n := by
    simp_rw [label_large (2*s) n _ _ hn]
    simp only [largeLabel,hm,ite_true]
    rw [Fin.sum_univ_eq_sum_range (fun j => internalLabel (2*s) n (v.1.val+1) ((2*s)*v.2.val+j))]
    exact internal_children_sum s n v.1.val v.2.val hs hv hm v.2.isLt
  rw [hsum] at hrow
  have hd : 0 < depth v := by change 0 < v.1.val; omega
  rw [ite_eq_left hd,label_large (2*s) n _ _ hn] at hrow
  have hi : v.1.val < n := by omega
  rw [show largeLabel (2*s) n v.1.val v.2.val = internalLabel (2*s) n v.1.val v.2.val by simp [largeLabel,hi]] at hrow
  exact hrow

/-- Constant colour of every actual leaf parent, for the already-built equivalence. -/
theorem last_parent_weight (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (v : Vertex (2*s) n) (hv : v.1.val = n-1) :
    weight (tree (2*s) n) (higherLabeling s n hs hn) v = leafConstant s n := by
  have hrow := Round3.literal_weight_row (by omega : 0 < 2*s)
    (higherLabeling s n hs hn) (higherLabeling_label s n hs hn) v
    (by change v.1.val < n; omega)
  have hd : 0 < depth v := by change 0 < v.1.val; omega
  rw [ite_eq_left hd] at hrow
  simp_rw [label_large (2*s) n _ _ hn] at hrow
  have hi : v.1.val < n := by omega
  rw [show largeLabel (2*s) n v.1.val v.2.val = internalLabel (2*s) n v.1.val v.2.val by simp [largeLabel,hi]] at hrow
  have hsum : (∑ j : Fin (2*s), largeLabel (2*s) n (v.1.val+1) ((2*s)*v.2.val+j.val)) =
      ∑ j ∈ range (2*s), largeLabel (2*s) n n ((2*s)*v.2.val+j) := by
    rw [show v.1.val+1=n by omega,Fin.sum_univ_eq_sum_range (fun j => largeLabel (2*s) n n ((2*s)*v.2.val+j))]
  rw [hsum] at hrow
  conv at hrow => rhs; arg 1; arg 3; rw [hv]
  rw [hrow]
  exact leaf_parent_sum s n v.2.val hs hn (by simpa only [hv] using v.2.isLt)

theorem leaf_weight (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (v : Vertex (2*s) n) (hv : depth v = n) :
    weight (tree (2*s) n) (higherLabeling s n hs hn) v = label (2*s) n v.1.val v.2.val := by
  rw [weight_bottom (by omega) (by omega) _ v hv,higherLabeling_label]

#print axioms middle_weight
#print axioms last_parent_weight
#print axioms leaf_weight
end Antimagic.Round5A
