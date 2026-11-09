import Antimagic7AWeights
namespace Antimagic.Round7A
open Finset Round4A Round5A Round6A

theorem center_ge_three (n : ℕ) (hn : 3 ≤ n) : 3 ≤ center 2 n := by
  have := binary_center n hn
  have := internalEdges_lower 2 n hn
  norm_num only at *
  omega

theorem leafConstant_large (n : ℕ) (hn : 3 ≤ n) :
    internalEdges 2 n+2^n<leafConstant 1 n := by
  have := binary_center n hn
  have hp : 2^n=2*2^(n-1) := by rw [Nat.mul_comm,← pow_succ,show n-1+1=n by omega]
  unfold leafConstant
  norm_num only
  omega

theorem root_weight (n : ℕ) (hn : 3 ≤ n) :
    weight (tree 2 n) (higherLabeling n hn) (root 2 n)=3*center 2 n :=
  binary_root_weight n hn _ (higherLabeling_label n hn)

theorem first_weight (n : ℕ) (hn : 3 ≤ n) (v : Vertex 2 n) (hv : v.1.val=1) :
    weight (tree 2 n) (higherLabeling n hn) v=if v.2.val=0 then 3*center 2 n+1 else 4*center 2 n-1 :=
  binary_first_weight n hn _ (higherLabeling_label n hn) v hv

theorem nonlast_weight_band (n : ℕ) (hn : 3 ≤ n) (v : Vertex 2 n) (hv : v.1.val+1<n) :
    internalEdges 2 n<weight (tree 2 n) (higherLabeling n hn) v ∧
    weight (tree 2 n) (higherLabeling n hn) v ≤ internalEdges 2 n+2^n := by
  have hc := binary_center n hn
  have hz := center_ge_three n hn
  have hp : 2^n=2*2^(n-1) := by rw [Nat.mul_comm,← pow_succ,show n-1+1=n by omega]
  by_cases h0 : v.1.val=0
  · rw [unique_depth_zero v h0,root_weight]
    omega
  · by_cases h1 : v.1.val=1
    · rw [first_weight n hn v h1]
      split_ifs <;> omega
    · rw [middle_weight n hn v (by omega) hv]
      have := internal_range n v.1.val v.2.val hn (by omega) (by omega) v.2.isLt
      omega

theorem higher_local (n : ℕ) (hn : 3 ≤ n) : IsLocal (tree 2 n) (higherLabeling n hn) := by
  have dir (u v : Vertex 2 n) (h : Child u v) :
      weight (tree 2 n) (higherLabeling n hn) u ≠ weight (tree 2 n) (higherLabeling n hn) v := by
    have hh := h.1
    have hu := u.1.isLt
    have hv := v.1.isLt
    have hc := leafConstant_large n hn
    by_cases h0 : u.1.val=0
    · rw [unique_depth_zero u h0,root_weight,first_weight n hn v (by omega)]
      have := binary_root_separation n hn
      split_ifs <;> omega
    · by_cases hb : v.1.val=n
      · rw [last_parent_weight n hn u (by omega),leaf_weight n hn v hb]
        have := formula_range_rows n v.1.val v.2.val hn (by omega) (by omega) v.2.isLt
        omega
      · by_cases hp : v.1.val=n-1
        · rw [last_parent_weight n hn v hp]
          have := nonlast_weight_band n hn u (by omega)
          omega
        · by_cases h1 : u.1.val=1
          · rw [first_weight n hn u h1,middle_weight n hn v (by omega) (by omega)]
            have hi : u.2.val<2 := by have := u.2.isLt; simpa only [h1,pow_one] using this
            have hv2 : v.1.val=2 := by omega
            have hv4 : v.2.val<4 := by have := v.2.isLt; simpa only [hv2, show (2:ℕ)^2=4 by decide] using this
            have hpar := h.2
            have he := binary_row_two n hn
            have hz := center_ge_three n hn
            rw [show internalLabel 2 n v.1.val v.2.val=internalLabel 2 n 2 v.2.val from congrArg (fun h => internalLabel 2 n h v.2.val) hv2]
            rcases (show v.2.val=0 ∨ v.2.val=1 ∨ v.2.val=2 ∨ v.2.val=3 by omega) with hj|hj|hj|hj
            all_goals simp only [hj] at hpar ⊢
            all_goals norm_num only at hpar
            · rw [he.1]
              have huval : u.2.val=0 := by omega
              simp only [huval,ite_true]
              omega
            · rw [he.2.1]
              have huval : u.2.val=0 := by omega
              simp only [huval,ite_true]
              omega
            · rw [he.2.2.1]
              have huval : u.2.val=1 := by omega
              simp only [huval,Nat.one_ne_zero,ite_false]
              omega
            · rw [he.2.2.2]
              have huval : u.2.val=1 := by omega
              simp only [huval,Nat.one_ne_zero,ite_false]
              omega
          · rw [middle_weight n hn u (by omega) (by omega),middle_weight n hn v (by omega) (by omega)]
            intro eq
            have := binary_internal_injective n u.1.val v.1.val u.2.val v.2.val hn
              (by omega) (by omega) (by omega) (by omega) u.2.isLt v.2.isLt (by omega)
            omega
  intro u v h
  rcases h with h|h
  · exact dir u v h
  · exact (dir v u h).symm
theorem leaf_color (n x : ℕ) (hn : 3  ≤  n)
    (hx : internalEdges 2 n<x ∧ x  ≤  internalEdges 2 n+2^n) :
    ∃ v : Vertex 2 n, depth v=n ∧
      weight (tree 2 n) (higherLabeling n hn) v=x := by
  obtain ⟨i,hi⟩ := (leafRowMap_bijective n hn).2
    ⟨x-(internalEdges 2 n+1),by omega⟩
  have he := congrArg Fin.val hi
  change largeLabel 2 n n i.val-(internalEdges 2 n+1)=x-(internalEdges 2 n+1) at he
  have ha := (leaf_range n i.val hn i.isLt).1
  let v : Vertex 2 n := ⟨⟨n,by omega⟩,i⟩
  refine ⟨v,rfl,?_⟩
  rw [leaf_weight n hn v rfl,label_large 2 n _ _ hn]
  change largeLabel 2 n n i.val=x
  omega

theorem higher_colors (n : ℕ) (hn : 3  ≤  n) :
    colorCount (tree 2 n) (higherLabeling n hn)=2^n+1 := by
  let w := weight (tree 2 n) (higherLabeling n hn)
  let leaves := (univ : Finset (Vertex 2 n)).filter (fun v => depth v=n)
  have hcard : leaves.card=2^n := by
    change (univ.filter fun v : Vertex 2 n => depth v=n).card=_
    rw [← Fintype.card_subtype,← Fintype.card_congr (bottomEquiv 2 n)]
    exact Fintype.card_fin _
  have hcover : univ.image w ⊆ insert (leafConstant 1 n) (leaves.image w) := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    have hv := v.1.isLt
    by_cases hb : depth v=n
    · exact mem_insert_of_mem (mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hb⟩,rfl⟩)
    · by_cases hp : v.1.val=n-1
      · exact mem_insert.mpr (Or.inl (last_parent_weight n hn v hp))
      · have hr : internalEdges 2 n<w v ∧ w v  ≤  internalEdges 2 n+2^n := by
          exact nonlast_weight_band n hn v (by unfold depth at hb; omega)
        obtain ⟨u,hu,he⟩ := leaf_color n (w v) hn hr
        exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩,he⟩)
  apply Nat.le_antisymm
  · change (univ.image w).card ≤ _
    calc
      _  ≤  (insert (leafConstant 1 n) (leaves.image w)).card := card_le_card hcover
      _  ≤  (leaves.image w).card+1 := card_insert_le _ _
      _  ≤  leaves.card+1 := Nat.add_le_add_right card_image_le 1
      _ = _ := by rw [hcard]
  · exact lowerBound 2 n (by omega) (by omega) _ (higher_local n hn)

theorem binaryHigherConstruction : Round3.BinaryHigherConstruction := by
  intro n hn
  refine ⟨higherLabeling n hn,?_,higher_local n hn,higher_colors n hn⟩
  intro u v h
  let a : Nonroot 2 n := ⟨v,by have := h.1; unfold depth; omega⟩
  have heq : (⟨s(u,v),(tree 2 n).mem_edgeSet.mpr (Or.inl h)⟩ : (tree 2 n).edgeSet) = incomingEdge (by omega) a := by
    apply Subtype.ext
    change s(u,v) = s(parent (by omega) a,v)
    rw [← child_parent_unique h (by omega)]
  rw [heq]
  exact higherLabeling_label n hn a
#print axioms binaryHigherConstruction
end Antimagic.Round7A
