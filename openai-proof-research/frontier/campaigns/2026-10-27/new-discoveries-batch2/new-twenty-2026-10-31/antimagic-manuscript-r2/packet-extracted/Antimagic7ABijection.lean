import Antimagic7ALeaves
namespace Antimagic.Round7A
open Round4A Round5A Round6A

theorem internal_range (n h i : ℕ) (hn : 3  ≤  n) (hh : 1 ≤ h) (hhn : h<n) (hi : i<2^h) :
    1 ≤ internalLabel 2 n h i ∧ internalLabel 2 n h i ≤ internalEdges 2 n := by
  by_cases h1 : h=1
  · subst h
    have := binary_center n hn
    have := internalEdges_lower 2 n hn
    norm_num only at hi this
    simp only [internalLabel,ite_true]
    split_ifs <;> omega
  · have := binary_internal_range n h i hn (by omega) hhn hi
    omega

def internalMap (n : ℕ) (hn : 3 ≤ n) (v : InternalVertex 2 n) : Fin (internalEdges 2 n) :=
  ⟨internalLabel 2 n v.val.val.1.val v.val.val.2.val-1,by
    have := internal_range n _ _ hn v.val.property v.property v.val.val.2.isLt
    simp only [depth] at this
    omega⟩

theorem internalMap_bijective (n : ℕ) (hn : 3 ≤ n) : Function.Bijective (internalMap n hn) := by
  constructor
  · intro v w eq
    have hv := internal_range n _ _ hn v.val.property v.property v.val.val.2.isLt
    have hw := internal_range n _ _ hn w.val.property w.property w.val.val.2.isLt
    simp only [depth] at hv hw
    have eqv := congrArg Fin.val eq
    change internalLabel 2 n v.val.val.1.val v.val.val.2.val-1=internalLabel 2 n w.val.val.1.val w.val.val.2.val-1 at eqv
    have hc := binary_internal_injective n _ _ _ _ hn v.val.property w.val.property
      v.property w.property v.val.val.2.isLt w.val.val.2.isLt (by simp only [depth]; omega)
    exact Subtype.ext (vertex_ext hc.1 hc.2)
  · intro x
    obtain ⟨h,i,hh,hhn,hi,heq⟩ := binary_internal_exists n (x.val+1) hn (by have := x.isLt; omega)
    refine ⟨⟨⟨⟨⟨h,by omega⟩,⟨i,hi⟩⟩,hh⟩,hhn⟩,?_⟩
    apply Fin.ext
    change internalLabel 2 n h i-1=x.val
    omega

theorem formula_range_rows (n h i : ℕ) (hn : 3 ≤ n) (hh : 1 ≤ h) (hhn : h ≤ n) (hi : i<2^h) :
    1 ≤ label 2 n h i ∧ label 2 n h i ≤ internalEdges 2 n+2^n := by
  rw [label_large 2 n h i hn]
  by_cases hl : h<n
  · rw [largeLabel,ite_eq_left hl]
    have := internal_range n h i hn hh hl hi
    exact ⟨this.1, this.2.trans (Nat.le_add_right _ _)⟩
  · have he : h=n := by omega
    subst h
    have := leaf_range n i hn hi
    omega

theorem large_injective (n h g i j : ℕ) (hn : 3 ≤ n)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hhn : h ≤ n) (hgn : g ≤ n)
    (hi : i<2^h) (hj : j<2^g) (eq : largeLabel 2 n h i=largeLabel 2 n g j) : h=g ∧ i=j := by
  by_cases hl : h<n
  · by_cases gl : g<n
    · simp only [largeLabel,hl,gl,ite_true] at eq
      exact binary_internal_injective n h g i j hn hh hg hl gl hi hj eq
    · have gn : g=n := by omega
      subst g
      have := leaf_range n j hn hj
      have := internal_range n h i hn hh hl hi
      rw [largeLabel,ite_eq_left hl] at eq
      omega
  · have he : h=n := by omega
    subst h
    by_cases gl : g<n
    · have := leaf_range n i hn hi
      have := internal_range n g j hn hg gl hj
      rw [show largeLabel 2 n g j=internalLabel 2 n g j by simp [largeLabel,gl]] at eq
      omega
    · have gn : g=n := by omega
      subst g
      exact ⟨rfl,congrArg Fin.val (leaf_row_injective n hn (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) eq)⟩
def formulaMap (n : ℕ) (hn : 3  ≤  n) (v : Nonroot 2 n) :
    Fin (internalEdges 2 n + 2^n) :=
  ⟨label 2 n v.val.1.val v.val.2.val - 1,by
    have hb := formula_range_rows n v.val.1.val v.val.2.val hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt
    omega⟩

theorem formulaMap_bijective (n : ℕ) (hn : 3  ≤  n) :
    Function.Bijective (formulaMap n hn) := by
  constructor
  · intro v w eq
    have hv := formula_range_rows n v.val.1.val v.val.2.val hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt
    have hw := formula_range_rows n w.val.1.val w.val.2.val hn w.property (by have := w.val.1.isLt; omega) w.val.2.isLt
    have eqv := congrArg Fin.val eq
    change label 2 n v.val.1.val v.val.2.val - 1 = label 2 n w.val.1.val w.val.2.val - 1 at eqv
    have hc := large_injective n v.val.1.val w.val.1.val v.val.2.val w.val.2.val hn v.property w.property
      (by have := v.val.1.isLt; omega) (by have := w.val.1.isLt; omega) v.val.2.isLt w.val.2.isLt (by
        rw [← label_large 2 n _ _ hn,← label_large 2 n _ _ hn]; omega)
    exact vertex_ext hc.1 hc.2
  · intro x
    by_cases hx : x.val < internalEdges 2 n
    · obtain ⟨v,hv⟩ := (internalMap_bijective n hn).2 ⟨x.val,hx⟩
      refine ⟨v.val,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hv
      change internalLabel 2 n v.val.val.1.val v.val.val.2.val - 1 = x.val at hval
      change label 2 n v.val.val.1.val v.val.val.2.val - 1 = x.val
      rw [label_large 2 n _ _ hn,largeLabel,ite_eq_left v.property]
      exact hval
    · obtain ⟨i,hi⟩ := (leafRowMap_bijective n hn).2 ⟨x.val-internalEdges 2 n,by have := x.isLt; omega⟩
      refine ⟨⟨⟨⟨n,by omega⟩,i⟩,by change 0 < n; omega⟩,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hi
      change largeLabel 2 n n i.val - (internalEdges 2 n+1) = x.val-internalEdges 2 n at hval
      change label 2 n n i.val - 1 = x.val
      rw [label_large 2 n n i.val hn]
      have hb := (leaf_range n i.val hn i.isLt).1
      omega

noncomputable def higherLabeling (n : ℕ) (hn : 3  ≤  n) : Labeling (tree 2 n) :=
  let e := Equiv.ofBijective _ (formulaMap_bijective n hn)
  (incomingEquiv (by omega : 0 < 2)).symm.trans (e.trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv (by omega : 0 < 2)),
      Fintype.card_congr e,Fintype.card_fin])))

theorem higherLabeling_label (n : ℕ) (hn : 3  ≤  n) (v : Nonroot 2 n) :
    (higherLabeling n hn (incomingEdge (by omega) v)).val+1 =
      label 2 n v.val.1.val v.val.2.val := by
  change (higherLabeling n hn ((incomingEquiv (by omega)) v)).val+1 = _
  simp only [higherLabeling,Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply,Fin.val_cast]
  exact Nat.sub_add_cancel (formula_range_rows n v.val.1.val v.val.2.val hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt).1

#print axioms formulaMap_bijective
#print axioms higherLabeling_label
end Antimagic.Round7A
