import Antimagic5ALeafRow
namespace Antimagic.Round5A
open Round4A

theorem large_leaf_above (s n i : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (hi : i < (2*s)^n) :
    internalEdges (2*s) n < largeLabel (2*s) n n i := by
  have he : Even (2*s) := ⟨s,by omega⟩
  have hq : i/(2*s) < (2*s)^(n-1) := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)).mpr
    have hexp : (2*s)^n = (2*s)^(n-1)*(2*s) := by rw [← pow_succ,show n-1+1=n by omega]
    omega
  have ha := parentParameter_range (2*s) n _ (by omega) he hn hq
  have hp := even_power (2*s) (n-1) he (by omega)
  have hr := leafEntry_range s ((2*s)^(n-1)/2) (parentParameter (2*s) n (i/(2*s)))
    (i%(2*s)) (by omega) (by omega) (Nat.mod_lt _ (by omega))
  have hf := leaf_formula s n (i/(2*s)) (i%(2*s)) hs hn (Nat.mod_lt _ (by omega))
  rw [Nat.div_add_mod] at hf
  omega

theorem label_large (t n h i : ℕ) (hn : 3 ≤ n) : label t n h i = largeLabel t n h i := by
  simp only [label,show n ≠ 1 by omega,show n ≠ 2 by omega,ite_false]

theorem large_injective (s n h g i j : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hhn : h ≤ n) (hgn : g ≤ n)
    (hi : i < (2*s)^h) (hj : j < (2*s)^g)
    (eq : largeLabel (2*s) n h i = largeLabel (2*s) n g j) : h = g ∧ i = j := by
  have he : Even (2*s) := ⟨s,by omega⟩
  by_cases hl : h < n
  · by_cases gl : g < n
    · simp only [largeLabel,hl,gl,ite_true] at eq
      exact internalLabel_injective (2*s) n h g i j (by omega) he hn hh hg hl gl hi hj eq
    · have gn : g = n := by omega
      subst g
      have hb := large_leaf_above s n j hs hn hj
      have hr := internal_range (2*s) n h i (by omega) he hn hh hl hi
      rw [largeLabel,ite_eq_left hl] at eq
      omega
  · have hn' : h = n := by omega
    subst h
    by_cases gl : g < n
    · have hb := large_leaf_above s n i hs hn hi
      have hr := internal_range (2*s) n g j (by omega) he hn hg gl hj
      rw [show largeLabel (2*s) n g j = internalLabel (2*s) n g j by simp [largeLabel,gl]] at eq
      omega
    · have gn : g = n := by omega
      subst g
      have hij := leaf_row_injective s n hs hn (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) eq
      exact ⟨rfl,congrArg (fun a : Fin ((2*s)^n) => a.val) hij⟩

def formulaMap (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (v : Nonroot (2*s) n) :
    Fin (internalEdges (2*s) n + (2*s)^n) :=
  ⟨label (2*s) n v.val.1.val v.val.2.val - 1,by
    have hb := formula_range_rows s n v.val.1.val v.val.2.val hs hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt
    omega⟩

theorem formulaMap_bijective (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    Function.Bijective (formulaMap s n hs hn) := by
  constructor
  · intro v w eq
    have hv := formula_range_rows s n v.val.1.val v.val.2.val hs hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt
    have hw := formula_range_rows s n w.val.1.val w.val.2.val hs hn w.property (by have := w.val.1.isLt; omega) w.val.2.isLt
    have eqv := congrArg Fin.val eq
    change label (2*s) n v.val.1.val v.val.2.val - 1 = label (2*s) n w.val.1.val w.val.2.val - 1 at eqv
    have hc := large_injective s n v.val.1.val w.val.1.val v.val.2.val w.val.2.val hs hn v.property w.property
      (by have := v.val.1.isLt; omega) (by have := w.val.1.isLt; omega) v.val.2.isLt w.val.2.isLt (by
        rw [← label_large (2*s) n _ _ hn,← label_large (2*s) n _ _ hn]; omega)
    exact vertex_ext hc.1 hc.2
  · intro x
    have he : Even (2*s) := ⟨s,by omega⟩
    by_cases hx : x.val < internalEdges (2*s) n
    · obtain ⟨v,hv⟩ := (internalMap_bijective (2*s) n (by omega) he hn).2 ⟨x.val,hx⟩
      refine ⟨v.val,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hv
      change internalLabel (2*s) n v.val.val.1.val v.val.val.2.val - 1 = x.val at hval
      change label (2*s) n v.val.val.1.val v.val.val.2.val - 1 = x.val
      rw [label_large (2*s) n _ _ hn,largeLabel,ite_eq_left v.property]
      exact hval
    · obtain ⟨i,hi⟩ := (leafRowMap_bijective s n hs hn).2 ⟨x.val-internalEdges (2*s) n,by have := x.isLt; omega⟩
      refine ⟨⟨⟨⟨n,by omega⟩,i⟩,by change 0 < n; omega⟩,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hi
      change largeLabel (2*s) n n i.val - (internalEdges (2*s) n+1) = x.val-internalEdges (2*s) n at hval
      change label (2*s) n n i.val - 1 = x.val
      rw [label_large (2*s) n n i.val hn]
      have hb := large_leaf_above s n i.val hs hn i.isLt
      omega

noncomputable def higherLabeling (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) : Labeling (tree (2*s) n) :=
  let e := Equiv.ofBijective _ (formulaMap_bijective s n hs hn)
  (incomingEquiv (by omega : 0 < 2*s)).symm.trans (e.trans
    (finCongr (by rw [← Fintype.card_congr (incomingEquiv (by omega : 0 < 2*s)),
      Fintype.card_congr e,Fintype.card_fin])))

theorem higherLabeling_label (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (v : Nonroot (2*s) n) :
    (higherLabeling s n hs hn (incomingEdge (by omega) v)).val+1 =
      label (2*s) n v.val.1.val v.val.2.val := by
  change (higherLabeling s n hs hn ((incomingEquiv (by omega)) v)).val+1 = _
  simp only [higherLabeling,Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply,Fin.val_cast]
  exact Nat.sub_add_cancel (formula_range_rows s n v.val.1.val v.val.2.val hs hn v.property (by have := v.val.1.isLt; omega) v.val.2.isLt).1

#print axioms formulaMap_bijective
#print axioms higherLabeling_label
end Antimagic.Round5A
