import Antimagic6ARoot
namespace Antimagic.Round6A
open Finset Round5A

theorem middle_weight_band (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (v : Vertex (2*s) n) (hv : 1 ≤ v.1.val) (hm : v.1.val+1<n) :
    internalEdges (2*s) n < weight (tree (2*s) n) (higherLabeling s n hs hn) v ∧
    weight (tree (2*s) n) (higherLabeling s n hs hn) v ≤ internalEdges (2*s) n+(2*s)^n := by
  rw [middle_weight s n hs hn v hv hm]
  have hr := internal_range (2*s) n v.1.val v.2.val (by omega)
    (show Even (2*s) from ⟨s,by omega⟩) hn hv (by omega) v.2.isLt
  have hl := center_mul_ge_internal s n (by omega) hn
  have hu := center_le_last_row (2*s) n (by omega) hn
  have hp : (2*s)^n = (2*s)^(n-1)*(2*s) := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  constructor
  · omega
  · rw [hp]; nlinarith

theorem higher_local (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    IsLocal (tree (2*s) n) (higherLabeling s n hs hn) := by
  have dir (u v : Vertex (2*s) n) (h : Child u v) :
      weight (tree (2*s) n) (higherLabeling s n hs hn) u ≠
      weight (tree (2*s) n) (higherLabeling s n hs hn) v := by
    have hh := h.1
    have hu := u.1.isLt
    have hv := v.1.isLt
    have hc := leafConstant_large s n hs hn
    by_cases hz : u.1.val=0
    · rw [unique_depth_zero u hz,root_weight]
      rw [middle_weight s n hs hn v (by omega) (by omega)]
      have hr := internal_range (2*s) n v.1.val v.2.val (by omega)
        (show Even (2*s) from ⟨s,by omega⟩) hn (by omega) (by omega) v.2.isLt
      have hb := (rootColor_bounds s n hs hn).2.2
      omega
    · by_cases hb : v.1.val=n
      · rw [last_parent_weight s n hs hn u (by omega),leaf_weight s n hs hn v hb]
        have hr := formula_range_rows s n v.1.val v.2.val hs hn (by omega) (by omega) v.2.isLt
        omega
      · by_cases hp : v.1.val=n-1
        · rw [last_parent_weight s n hs hn v hp]
          have hr := middle_weight_band s n hs hn u (by omega) (by omega)
          omega
        · rw [middle_weight s n hs hn u (by omega) (by omega),middle_weight s n hs hn v (by omega) (by omega)]
          intro eq
          have hi := internalLabel_injective (2*s) n u.1.val v.1.val u.2.val v.2.val
            (by omega) (show Even (2*s) from ⟨s,by omega⟩) hn (by omega) (by omega)
            (by omega) (by omega) u.2.isLt v.2.isLt (by omega)
          omega
  intro u v h
  rcases h with h | h
  · exact dir u v h
  · exact (dir v u h).symm

/-- Every integer in the high interval occurs as a literal leaf weight. -/
theorem leaf_color (s n x : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n)
    (hx : internalEdges (2*s) n<x ∧ x ≤ internalEdges (2*s) n+(2*s)^n) :
    ∃ v : Vertex (2*s) n, depth v=n ∧
      weight (tree (2*s) n) (higherLabeling s n hs hn) v=x := by
  obtain ⟨i,hi⟩ := (leafRowMap_bijective s n hs hn).2
    ⟨x-(internalEdges (2*s) n+1),by omega⟩
  have he := congrArg Fin.val hi
  change largeLabel (2*s) n n i.val-(internalEdges (2*s) n+1)=x-(internalEdges (2*s) n+1) at he
  have ha := large_leaf_above s n i.val hs hn i.isLt
  let v : Vertex (2*s) n := ⟨⟨n,by omega⟩,i⟩
  refine ⟨v,rfl,?_⟩
  rw [leaf_weight s n hs hn v rfl,label_large (2*s) n _ _ hn]
  change largeLabel (2*s) n n i.val=x
  omega

theorem higher_colors (s n : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) :
    colorCount (tree (2*s) n) (higherLabeling s n hs hn)=(2*s)^n+1 := by
  let w := weight (tree (2*s) n) (higherLabeling s n hs hn)
  let leaves := (univ : Finset (Vertex (2*s) n)).filter (fun v => depth v=n)
  have hcard : leaves.card=(2*s)^n := by
    change (univ.filter fun v : Vertex (2*s) n => depth v=n).card=_
    rw [← Fintype.card_subtype,← Fintype.card_congr (bottomEquiv (2*s) n)]
    exact Fintype.card_fin _
  have hcover : univ.image w ⊆ insert (leafConstant s n) (leaves.image w) := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    have hv := v.1.isLt
    by_cases hb : depth v=n
    · exact mem_insert_of_mem (mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hb⟩,rfl⟩)
    · by_cases hp : v.1.val=n-1
      · exact mem_insert.mpr (Or.inl (last_parent_weight s n hs hn v hp))
      · have hr : internalEdges (2*s) n<w v ∧ w v ≤ internalEdges (2*s) n+(2*s)^n := by
          by_cases hz : v.1.val=0
          · change _ < weight _ _ v ∧ weight _ _ v ≤ _
            rw [unique_depth_zero v hz,root_weight]
            exact ⟨(rootColor_bounds s n hs hn).1,(rootColor_bounds s n hs hn).2.1⟩
          · exact middle_weight_band s n hs hn v (by omega) (by unfold depth at hb; omega)
        obtain ⟨u,hu,he⟩ := leaf_color s n (w v) hs hn hr
        exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,hu⟩,he⟩)
  apply Nat.le_antisymm
  · change (univ.image w).card≤_
    calc
      _ ≤ (insert (leafConstant s n) (leaves.image w)).card := card_le_card hcover
      _ ≤ (leaves.image w).card+1 := card_insert_le _ _
      _ ≤ leaves.card+1 := Nat.add_le_add_right card_image_le 1
      _ = _ := by rw [hcard]
  · exact lowerBound (2*s) n (by omega) (by omega) _ (higher_local s n hs hn)

theorem nonbinaryWeightCompletion : NonbinaryWeightCompletion := by
  intro s n hs hn
  exact ⟨higher_local s n hs hn,higher_colors s n hs hn⟩

theorem nonbinaryHigherConstruction : Round3.NonbinaryHigherConstruction :=
  nonbinaryHigherConstruction_of_weights nonbinaryWeightCompletion

#print axioms higher_local
#print axioms higher_colors
#print axioms nonbinaryWeightCompletion
#print axioms nonbinaryHigherConstruction
end Antimagic.Round6A
