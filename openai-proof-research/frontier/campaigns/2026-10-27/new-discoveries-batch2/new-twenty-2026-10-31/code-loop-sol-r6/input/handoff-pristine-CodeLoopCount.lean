import CodeLoopFactor

/-!
# MathDB 343790 counting layer: fibres of the coordinate evaluation

First counting module for the literal 343790 endpoint.  Honest kernel
cardinalities of the fibres of the evaluation pairing `a |-> dot4 w a` on all
of `W4`, by explicit bijections; no enumeration, no sampled checks, no oracle.
-/

/-- The two elements of `ZMod 2` differ. -/
theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
  intro h
  have hv : (1 : ZMod 2).val = (0 : ZMod 2).val := by rw [h]
  rw [zmod2_val_one, ZMod.val_zero] at hv
  exact Nat.one_ne_zero hv

/-- Adding any vector of `W4` twice is the identity. -/
theorem add_k_self (k a : W4) : a + k + k = a := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, zmod2_add_self, add_zero]

/-- Translation by `k` is an involutive permutation of `W4`. -/
def addSelfInv (k : W4) : W4 ≃ W4 where
  toFun a := a + k
  invFun a := a + k
  left_inv a := add_k_self k a
  right_inv a := add_k_self k a

/-- Translation by a vector of pairing value one exchanges the two fibres of
`a |-> dot4 w a`. -/
def fibreShift (w : W4) (k : W4) (hk : dot4 w k = 1) :
    {a : W4 // dot4 w a = 1} ≃ {a : W4 // dot4 w a = 0} :=
  Equiv.subtypeEquiv (addSelfInv k) (fun a : W4 =>
    (⟨fun h1 : dot4 w a = 1 => by
        rw [dot4_add_left, h1, hk, zmod2_add_self],
      fun h0 : dot4 w (a + k) = 0 => by
        rw [← add_k_self k a, dot4_add_left, h0, hk, zero_add]⟩ :
      dot4 w a = 1 ↔ dot4 w (a + k) = 0))

/-- The nonvanishing fibre and the unit fibre of a `ZMod 2`-valued function on
`W4` are equivalent. -/
def fibreNeEquiv (f : W4 → ZMod 2) :
    {a : W4 // ¬(f a = 0)} ≃ {a : W4 // f a = 1} :=
  Equiv.subtypeEquiv (Equiv.refl W4) fun a : W4 =>
    ⟨fun h : ¬(f a = 0) => (zmod2_cases (f a)).resolve_left h,
     fun h : f a = 1 => fun h0 : f a = 0 => zmod2_one_ne_zero (h.symm.trans h0)⟩

/-- Evaluating against the `j`-th unit coordinate reads off coordinate `j`. -/
theorem dot4_e4v_left (w : W4) (j : Fin 4) : dot4 w (e4v j) = w j := by
  simp only [dot4, e4v]
  exact (Finset.sum_eq_single j
    (fun b _ hb => by rw [ite_eq_right hb, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)).trans (by simp)

/-- For nonzero `w` the fibre `dot4 w a = 1` has cardinality eight: the two
fibres of the pairing on the sixteen-point `W4` have equal cardinality by the
explicit fibre translation, and partition `W4`. -/
theorem dot4_fiber_one_card {w : W4} (hw : w ≠ 0) :
    Fintype.card {a : W4 // dot4 w a = 1} = 8 := by
  obtain ⟨j, hj⟩ := exists_one_of_ne_zero4 hw
  have hk : dot4 w (e4v j) = 1 := by rw [dot4_e4v_left, hj]
  have hdec : Fintype.card W4 =
      Fintype.card {a : W4 // dot4 w a = 0} +
        Fintype.card {a : W4 // ¬(dot4 w a = 0)} := by
    have h1 : Fintype.card W4 =
        Fintype.card ({a : W4 // dot4 w a = 0} ⊕
          {a : W4 // ¬(dot4 w a = 0)}) :=
      Fintype.card_congr (Equiv.sumCompl fun a : W4 => dot4 w a = 0).symm
    rw [h1, Fintype.card_sum]
  have htra : Fintype.card {a : W4 // ¬(dot4 w a = 0)}
      = Fintype.card {a : W4 // dot4 w a = 1} :=
    Fintype.card_congr (fibreNeEquiv fun a : W4 => dot4 w a)
  have hshift : Fintype.card {a : W4 // dot4 w a = 1}
      = Fintype.card {a : W4 // dot4 w a = 0} :=
    Fintype.card_congr (fibreShift w (e4v j) hk)
  have key : Fintype.card W4
      = 2 * Fintype.card {a : W4 // dot4 w a = 0} := by
    rw [two_mul, hdec, htra, hshift]
  have h2 : 2 * Fintype.card {a : W4 // dot4 w a = 0} = 2 * 8 := by
    rw [← key, card_W4]
  have hc0 : Fintype.card {a : W4 // dot4 w a = 0} = 8 :=
    Nat.eq_of_mul_eq_mul_left (by decide) h2
  exact hshift.trans hc0

/-- For nonzero `w` the fibre `dot4 w a = 0` has cardinality eight. -/
theorem dot4_fiber_zero_card {w : W4} (hw : w ≠ 0) :
    Fintype.card {a : W4 // dot4 w a = 0} = 8 := by
  obtain ⟨j, hj⟩ := exists_one_of_ne_zero4 hw
  have hk : dot4 w (e4v j) = 1 := by rw [dot4_e4v_left, hj]
  exact (Fintype.card_congr (fibreShift w (e4v j) hk)).symm.trans
    (dot4_fiber_one_card hw)
