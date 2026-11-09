import CodeLoopCount

/-!
# MathDB 343790 parity layer: coordinate cubes and value fibres

Honest finset combinatorics for the counting stage: the parity bridge between
`ZMod 2` value sums and fibre cardinalities, and flip symmetries of coordinate
subcubes.  No enumeration, no oracle.
-/

/-- Half of a natural is zero in `ZMod 2`. -/
theorem cast_two_mul (m : Nat) : ((2 * m : Nat) : ZMod 2) = 0 := by
  rw [two_mul, Nat.cast_add]
  exact zmod2_add_self _

theorem e4v_self (j : Fin 4) : e4v j j = 1 := by simp [e4v]

theorem e4v_apply (k j : Fin 4) : e4v k j = if j = k then 1 else 0 := rfl

theorem e4v_apply_ne {k i : Fin 4} (h : i ≠ k) : e4v k i = 0 := by
  simp [e4v, h]

theorem dot4_zero_right (w : W4) : dot4 w 0 = 0 := by
  simp [dot4]

/-- A vector with a unit coordinate is nonzero. -/
theorem ne_zero_of_apply_one {a : W4} {j : Fin 4} (h : a j = 1) : a ≠ 0 := by
  intro h0
  have hz : a j = 0 := by rw [h0]; simp
  exact zmod2_one_ne_zero (h.symm.trans hz)

/-- Parity bridge: in `ZMod 2`, the size of the value-one fibre of a function
equals the total sum of its values. -/
theorem cast_filter_one_card_eq_sum {s : Finset W4} (v : W4 → ZMod 2) :
    ((s.filter (fun a => v a = 1)).card : ZMod 2) = ∑ a ∈ s, v a := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s)
    (p := fun a => v a = 1) (fun a => v a)
  have h1 : ((s.filter (fun a => v a = 1)).card : ZMod 2)
      = ∑ a ∈ s.filter (fun a => v a = 1), v a := by
    rw [Finset.card_eq_sum_ones, Finset.cast_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hv := (Finset.mem_filter.mp ha).2
    rw [Nat.cast_one]
    exact hv.symm
  have h0 : ∑ a ∈ s.filter (fun a => ¬(v a = 1)), v a = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    exact (zmod2_cases (v a)).resolve_right (Finset.mem_filter.mp ha).2
  calc ((s.filter (fun a => v a = 1)).card : ZMod 2)
      = ∑ a ∈ s.filter (fun a => v a = 1), v a := h1
    _ = ∑ a ∈ s.filter (fun a => v a = 1), v a
        + ∑ a ∈ s.filter (fun a => ¬(v a = 1)), v a := by
        rw [h0, add_zero]
    _ = ∑ a ∈ s, v a := hsplit

/-- Coordinatewise evaluation of finset sums in `W4`. -/
theorem sum_apply4 (s : Finset W4) (j : Fin 4) : (∑ a ∈ s, a) j = ∑ a ∈ s, a j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Pi.add_apply, ih]

/-- Additivity of the pairing over finset sums. -/
theorem dot4_sum (w : W4) (s : Finset W4) :
    dot4 w (∑ a ∈ s, a) = ∑ a ∈ s, dot4 w a := by
  classical
  induction s using Finset.induction with
  | empty => simp [dot4_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, dot4_add_left, ih, Finset.sum_insert ha]

/-- Flip symmetries swap the value-one and value-zero fibres of a coordinate on
any set of vectors closed under the flip. -/
theorem flip_card_eq (C : Finset W4) (j : Fin 4)
    (hc : ∀ a ∈ C, a + e4v j ∈ C) :
    (C.filter (fun a => a j = 1)).card = (C.filter (fun a => a j = 0)).card := by
  classical
  have hflipJ : ∀ a : W4, (a + e4v j) j = a j + 1 := by
    intro a; simp only [Pi.add_apply, e4v_self]
  have hinj : Function.Injective fun a : W4 => a + e4v j := by
    intro a b h
    rw [← add_k_self (e4v j) a, ← add_k_self (e4v j) b, h]
  have himg : (C.filter (fun a => a j = 1)).image
        (fun a : W4 => a + e4v j)
      = C.filter (fun a => a j = 0) := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro ⟨a, haC, haj, heq⟩
      subst heq
      constructor
      · exact hc a haC
      · rw [hflipJ, haj, zmod2_add_self]
    · rintro ⟨hbC, hb0⟩
      refine ⟨b + e4v j, ?_, ?_, ?_⟩
      · constructor
        · exact hc b hbC
        · rw [hflipJ, hb0, zero_add]
      · exact add_k_self (e4v j) b
  rw [← Finset.card_image_of_injective _ hinj, himg]
