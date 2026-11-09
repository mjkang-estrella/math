import CodeLoopWeight

def pairWeight {α : Type*} [Fintype α] (u v : α → ZMod 2) : Nat :=
  (Finset.univ.filter fun a => u a = 1 ∧ v a = 1).card

def tripleWeight {α : Type*} [Fintype α] (u v w : α → ZMod 2) : Nat :=
  (Finset.univ.filter fun a => u a = 1 ∧ v a = 1 ∧ w a = 1).card

theorem weight_pair_identity {α : Type*} [Fintype α] (u v : α → ZMod 2) :
    wordWeight (u+v) + 2 * pairWeight u v = wordWeight u + wordWeight v := by
  classical
  have hs : pairWeight u v = ∑ a, if u a = 1 ∧ v a = 1 then 1 else 0 := by
    simp [pairWeight]
  rw [hs]
  simp only [wordWeight_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.add_apply]
  rcases zmod2_cases (u a) with hu | hu <;>
  rcases zmod2_cases (v a) with hv | hv <;>
  simp only [hu,hv] <;> decide

theorem weight_triple_identity {α : Type*} [Fintype α] (u v w : α → ZMod 2) :
    wordWeight (u+v+w) + wordWeight u + wordWeight v + wordWeight w =
      wordWeight (u+v) + wordWeight (u+w) + wordWeight (v+w) +
        4 * tripleWeight u v w := by
  classical
  have hs : tripleWeight u v w = ∑ a, if u a = 1 ∧ v a = 1 ∧ w a = 1 then 1 else 0 := by
    simp [tripleWeight]
  rw [hs]
  simp only [wordWeight_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Pi.add_apply]
  rcases zmod2_cases (u a) with hu | hu <;>
  rcases zmod2_cases (v a) with hv | hv <;>
  rcases zmod2_cases (w a) with hw | hw <;>
  simp only [hu,hv,hw] <;> decide

theorem Q_zero : codeLoopQ (0 : W3) = 0 := by decide

theorem Q_nonzero {x : W3} (hx : x ≠ 0) : codeLoopQ x = 1 := by
  have hex : ∃ j, x j = 1 := by
    by_contra h
    apply hx
    funext j
    exact (zmod2_cases (x j)).resolve_right (fun hj => h ⟨j,hj⟩)
  obtain ⟨j,hj⟩ := hex
  unfold codeLoopQ
  fin_cases j <;> dsimp at hj
  all_goals rw [hj,zmod2_add_self]; simp

theorem dval_diagonal_parity (i : Fin 2) (w : W4) (x : W3) :
    ((wordWeight (dval i w x) / 4 : Nat) : ZMod 2) = codeLoopQ x := by
  rw [dval_weight,sval_weight]
  have hc := cval_weight_div8 i w
  by_cases hx : x = 0
  · subst x
    simp only [ite_true,add_zero,Q_zero]
    apply ZMod.val_injective 2
    simp only [ZMod.val_natCast,ZMod.val_zero]
    omega
  · rw [ite_eq_right hx,Q_nonzero hx]
    apply ZMod.val_injective 2
    simp only [ZMod.val_natCast,zmod2_val_one]
    omega


theorem pair_parity_of_weights {α : Type*} [Fintype α] (u v : α → ZMod 2)
    (hu : wordWeight u % 4 = 0) (hv : wordWeight v % 4 = 0)
    (huv : wordWeight (u+v) % 4 = 0) :
    ((pairWeight u v / 2 : Nat) : ZMod 2) =
      ((wordWeight (u+v) / 4 : Nat) : ZMod 2) +
      ((wordWeight u / 4 : Nat) : ZMod 2) +
      ((wordWeight v / 4 : Nat) : ZMod 2) := by
  have hi := weight_pair_identity u v
  apply ZMod.val_injective 2
  simp only [ZMod.val_add, ZMod.val_natCast]
  omega

theorem triple_parity_of_weights {α : Type*} [Fintype α] (u v w : α → ZMod 2)
    (hu : wordWeight u % 4 = 0) (hv : wordWeight v % 4 = 0)
    (hw : wordWeight w % 4 = 0) (huv : wordWeight (u+v) % 4 = 0)
    (huw : wordWeight (u+w) % 4 = 0) (hvw : wordWeight (v+w) % 4 = 0)
    (huvw : wordWeight (u+v+w) % 4 = 0) :
    (tripleWeight u v w : ZMod 2) =
      ((wordWeight (u+v+w) / 4 : Nat) : ZMod 2) +
      ((wordWeight u / 4 : Nat) : ZMod 2) +
      ((wordWeight v / 4 : Nat) : ZMod 2) +
      ((wordWeight w / 4 : Nat) : ZMod 2) +
      ((wordWeight (u+v) / 4 : Nat) : ZMod 2) +
      ((wordWeight (u+w) / 4 : Nat) : ZMod 2) +
      ((wordWeight (v+w) / 4 : Nat) : ZMod 2) := by
  have hi := weight_triple_identity u v w
  apply ZMod.val_injective 2
  simp only [ZMod.val_add, ZMod.val_natCast]
  omega

theorem codeLoopQ_cubic (x y z : W3) :
    codeLoopQ (x+y+z) + codeLoopQ x + codeLoopQ y + codeLoopQ z +
      codeLoopQ (x+y) + codeLoopQ (x+z) + codeLoopQ (y+z) =
      codeLoopF x y + codeLoopF (x+y) z + codeLoopF y z + codeLoopF x (y+z) := by
  simp only [codeLoopQ,codeLoopF,Pi.add_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
    show (14 : ZMod 2) = 0 by decide,mul_zero,zero_add,add_zero]
