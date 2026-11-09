import CodeLoopSpace

/-- Hamming weight, literally the number of positions equal to one. -/
def wordWeight {α : Type*} [Fintype α] (v : α → ZMod 2) : Nat :=
  (Finset.univ.filter fun a => v a = 1).card

theorem wordWeight_sum {α : Type*} [Fintype α] (v : α → ZMod 2) :
    wordWeight v = ∑ a, if v a = 1 then 1 else 0 := by
  classical
  simp [wordWeight]

theorem cval_weight_sum (i : Fin 2) (w : W4) :
    wordWeight (cval i w) = ∑ a : {a : W4 // a ≠ 0},
      if dot4 w a = 1 then mult i a else 0 := by
  classical
  rw [wordWeight_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : dot4 w a = 1 <;> simp [cval,h]

theorem cval_weight_formula (i : Fin 2) (w : W4) :
    wordWeight (cval i w) =
      (Finset.univ.filter fun a : W4 => a ≠ 0 ∧ dot4 w a = 1).card +
      4 * ((HofI i).filter fun a => dot4 w a = 1).card := by
  classical
  rw [cval_weight_sum]
  have heq : ∀ a : {a : W4 // a ≠ 0},
      (if dot4 w a = 1 then mult i a else 0) =
      (if dot4 w a = 1 then 1 else 0) +
      4 * (if a.val ∈ HofI i ∧ dot4 w a = 1 then 1 else 0) := by
    intro a
    by_cases hd : dot4 w a = 1 <;> by_cases hh : a.val ∈ HofI i <;> simp [mult,hd,hh]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · simp only [Finset.sum_boole]
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property, (Finset.mem_filter.mp ha).2⟩
    · intro a ha b hb h
      exact Subtype.ext h
    · intro a ha
      obtain ⟨_, hn, hd⟩ := Finset.mem_filter.mp ha
      exact ⟨⟨a, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩
  · apply congrArg (4 * ·)
    simp only [Finset.sum_boole]
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      exact Finset.mem_filter.mpr (Finset.mem_filter.mp ha).2
    · intro a ha b hb h
      exact Subtype.ext h
    · intro a ha
      obtain ⟨hh, hd⟩ := Finset.mem_filter.mp ha
      exact ⟨⟨a, HofI_ne_zero hh⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hd⟩, rfl⟩


theorem nat_even_of_cast_zero (n : Nat) (h : (n : ZMod 2) = 0) : n % 2 = 0 := by
  have hh := congrArg ZMod.val h
  simpa using hh

theorem HofI_sum_zero (i : Fin 2) : ∑ a ∈ HofI i, a = 0 := by
  unfold HofI
  split
  · exact sum_H1_zero
  · exact sum_H2_zero

theorem HofI_count_even (i : Fin 2) (w : W4) :
    ((HofI i).filter fun a => dot4 w a = 1).card % 2 = 0 :=
  nat_even_of_cast_zero _ (count_even_of_sum_zero (HofI_sum_zero i) w)

theorem cval_weight_zero (i : Fin 2) : wordWeight (cval i 0) = 0 := by
  simp [wordWeight, cval, dot4_zero_left, Ne.symm zmod2_one_ne_zero]

theorem cval_weight_nonzero (i : Fin 2) {w : W4} (hw : w ≠ 0) :
    wordWeight (cval i w) = 8 + 4 * ((HofI i).filter fun a => dot4 w a = 1).card := by
  rw [cval_weight_formula, count8 hw]

theorem cval_weight_div8 (i : Fin 2) (w : W4) : wordWeight (cval i w) % 8 = 0 := by
  by_cases hw : w = 0
  · subst w; rw [cval_weight_zero]
  · rw [cval_weight_nonzero i hw]
    have he := HofI_count_even i w
    omega

theorem cval2_minimum {w : W4} (hw : w ≠ 0) : 16 ≤ wordWeight (cval 1 w) := by
  have hex : ∃ a ∈ H2, dot4 w a = 1 := by
    by_contra h
    apply hw
    apply H2_detector
    intro a ha
    rcases zmod2_cases (dot4 w a) with hz | ho
    · exact hz
    · exact (h ⟨a,ha,ho⟩).elim
  obtain ⟨a,ha,hd⟩ := hex
  have hp : 0 < ((HofI 1).filter fun a => dot4 w a = 1).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨by simpa [HofI] using ha, hd⟩⟩
  have he := HofI_count_even 1 w
  rw [cval_weight_nonzero 1 hw]
  omega

theorem cval1_weight8 : wordWeight (cval 0 (e4v 3)) = 8 := by
  rw [cval_weight_nonzero 0 (ne_zero_of_apply_one (e4v_self 3))]
  have hf : ((HofI 0).filter fun a => dot4 (e4v 3) a = 1).card = 0 := by
    apply filter_card_zero
    intro a ha hd
    have hz : a 3 = 0 := (mem_H1.mp (by simpa [HofI] using ha)).1
    rw [dot4_comm, dot4_e4v_left, hz] at hd
    exact zmod2_one_ne_zero hd.symm
  rw [hf]

theorem dot3_zero_right (w : W3) : dot3 w 0 = 0 := by simp [dot3]

theorem dot3_fiber_card {x : W3} (hx : x ≠ 0) :
    Fintype.card {b : W3 // dot3 x b = 1} = 4 := by
  have hex : ∃ j, x j = 1 := by
    by_contra h
    apply hx
    funext j
    exact (zmod2_cases (x j)).resolve_right (fun hj => h ⟨j,hj⟩)
  obtain ⟨j,hj⟩ := hex
  let tr : W3 ≃ W3 :=
    { toFun := fun b => b + e3v j
      invFun := fun b => b + e3v j
      left_inv := fun b => by funext k; simp only [Pi.add_apply]; rw [add_assoc, zmod2_add_self,add_zero]
      right_inv := fun b => by funext k; simp only [Pi.add_apply]; rw [add_assoc, zmod2_add_self,add_zero] }
  have hshift : Fintype.card {b : W3 // dot3 x b = 1} =
      Fintype.card {b : W3 // dot3 x b = 0} := by
    apply Fintype.card_congr (Equiv.subtypeEquiv tr _)
    intro b
    change dot3 x b = 1 ↔ dot3 x (b+e3v j) = 0
    rw [dot3_add_left, dot3_e3v_left, hj]
    rcases zmod2_cases (dot3 x b) with h | h <;> rw [h] <;> decide
  have hs := Fintype.card_congr (Equiv.sumCompl fun b : W3 => dot3 x b = 0)
  simp only [Fintype.card_sum, card_W3] at hs
  have hn : Fintype.card {b : W3 // ¬dot3 x b = 0} =
      Fintype.card {b : W3 // dot3 x b = 1} := by
    apply Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) _)
    intro b
    exact ⟨fun h => (zmod2_cases _).resolve_left h,
      fun h h0 => zmod2_one_ne_zero (h.symm.trans h0)⟩
  omega

theorem sval_weight (x : W3) : wordWeight (sval x) = if x = 0 then 0 else 4 := by
  classical
  by_cases hx : x = 0
  · subst x; simp [wordWeight,sval,dot3_zero_left,Ne.symm zmod2_one_ne_zero]
  · rw [ite_eq_right hx]
    have he : wordWeight (sval x) = Fintype.card {b : W3 // dot3 x b = 1} := by
      unfold wordWeight
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine
        { toFun := fun a => ⟨a.val.val, (Finset.mem_filter.mp a.property).2⟩
          invFun := fun b => ⟨⟨b.val, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.property⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      intro hz
      have hh := b.property
      rw [hz,dot3_zero_right] at hh
      exact zmod2_one_ne_zero hh.symm
    rw [he, dot3_fiber_card hx]

theorem dval_weight (i : Fin 2) (w : W4) (x : W3) :
    wordWeight (dval i w x) = wordWeight (cval i w) + wordWeight (sval x) := by
  rw [wordWeight_sum, Fintype.sum_sum_type, wordWeight_sum, wordWeight_sum]
  rfl


theorem D_doubly_even (i : Fin 2) (v : D i) : wordWeight v.val % 4 = 0 := by
  obtain ⟨⟨w,x⟩,h⟩ := v.property
  change dval i w x = v.val at h
  rw [← h, dval_weight, sval_weight]
  have hc := cval_weight_div8 i w
  split <;> omega

theorem D1_has_weight8 : ∃ v ∈ D 0, wordWeight v = 8 := by
  refine ⟨dval 0 (e4v 3) 0, ⟨(e4v 3,0),rfl⟩, ?_⟩
  rw [dval_weight,cval1_weight8,sval_weight]
  simp

theorem D2_no_weight8 (v : D 1) : wordWeight v.val ≠ 8 := by
  obtain ⟨⟨w,x⟩,h⟩ := v.property
  change dval 1 w x = v.val at h
  rw [← h,dval_weight,sval_weight]
  by_cases hw : w = 0
  · subst w; rw [cval_weight_zero]; split <;> omega
  · have hc := cval2_minimum hw
    split <;> omega

theorem wordWeight_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (v : β → ZMod 2) : wordWeight (v ∘ e) = wordWeight v := by
  classical
  rw [wordWeight_sum, wordWeight_sum]
  exact Equiv.sum_comp e (fun a => if v a = 1 then 1 else 0)

/-- All coordinate bijections are excluded; there is no generator-basis restriction. -/
theorem D_no_coordinate_equivalence :
    ¬ ∃ e : Dcoord 0 ≃ Dcoord 1,
      ∀ v, v ∈ D 0 ↔ (fun c => v (e.symm c)) ∈ D 1 := by
  rintro ⟨e,he⟩
  obtain ⟨v,hv,hw⟩ := D1_has_weight8
  have hm := (he v).mp hv
  have hn := D2_no_weight8 ⟨_,hm⟩
  apply hn
  exact (wordWeight_equiv e.symm v).trans hw
