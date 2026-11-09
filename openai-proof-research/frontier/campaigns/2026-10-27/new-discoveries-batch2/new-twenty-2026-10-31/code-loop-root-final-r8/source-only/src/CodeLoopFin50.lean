import CodeLoopLiteral

noncomputable section

theorem mem_D50 (i : Fin 2) (v : Fin 50 → ZMod 2) :
    v ∈ D50 i ↔ (transport50 i).symm v ∈ D i := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa using hw
  · intro hv
    exact ⟨(transport50 i).symm v,hv,(transport50 i).apply_symm_apply v⟩

def subspaceEquiv50 (i : Fin 2) : D i ≃ₗ[ZMod 2] D50 i where
  toFun v := ⟨transport50 i v.val,⟨v.val,v.property,rfl⟩⟩
  invFun v := ⟨(transport50 i).symm v.val,(mem_D50 i v.val).mp v.property⟩
  left_inv v := by apply Subtype.ext; exact (transport50 i).symm_apply_apply v.val
  right_inv v := by apply Subtype.ext; exact (transport50 i).apply_symm_apply v.val
  map_add' v w := by apply Subtype.ext; exact (transport50 i).map_add v.val w.val
  map_smul' a v := by apply Subtype.ext; exact (transport50 i).map_smul a v.val

theorem D50_rank (i : Fin 2) : Module.finrank (ZMod 2) (D50 i) = 7 := by
  rw [← (subspaceEquiv50 i).finrank_eq,D_rank_seven]

theorem transport50_weight (i : Fin 2) (v : Dcoord i → ZMod 2) :
    wordWeight (transport50 i v) = wordWeight v :=
  wordWeight_equiv (coordEquiv50 i).symm v

theorem D50_doubly_even (i : Fin 2) (v : D50 i) : wordWeight v.val % 4 = 0 := by
  have he := (subspaceEquiv50 i).apply_symm_apply v
  have hc := D_doubly_even i ((subspaceEquiv50 i).symm v)
  have hw := transport50_weight i ((subspaceEquiv50 i).symm v).val
  have hv : transport50 i ((subspaceEquiv50 i).symm v).val = v.val := congrArg Subtype.val he
  rw [hv] at hw
  rw [hw]
  exact hc

theorem D50_full_support (i : Fin 2) (c : Fin 50) : ∃ v ∈ D50 i, v c = 1 := by
  obtain ⟨v,hv,hc⟩ := D_full_support i ((coordEquiv50 i).symm c)
  exact ⟨transport50 i v,⟨v,hv,rfl⟩,hc⟩

theorem D50_no_permutation :
    ¬ ∃ e : Equiv.Perm (Fin 50), ∀ v, v ∈ D50 0 ↔ (fun c => v (e.symm c)) ∈ D50 1 := by
  rintro ⟨e,he⟩
  obtain ⟨v,hv,hw⟩ := D1_has_weight8
  have hm : transport50 0 v ∈ D50 0 := ⟨v,hv,rfl⟩
  have hn := (he (transport50 0 v)).mp hm
  let w : D 1 := (subspaceEquiv50 1).symm ⟨_,hn⟩
  apply D2_no_weight8 w
  have htrans : transport50 1 w.val = fun c => transport50 0 v (e.symm c) :=
    congrArg Subtype.val ((subspaceEquiv50 1).apply_symm_apply ⟨_,hn⟩)
  calc
    wordWeight w.val = wordWeight (transport50 1 w.val) := (transport50_weight 1 w.val).symm
    _ = wordWeight (fun c => transport50 0 v (e.symm c)) := congrArg wordWeight htrans
    _ = wordWeight (transport50 0 v) := wordWeight_equiv e.symm _
    _ = wordWeight v := transport50_weight 0 v
    _ = 8 := hw
