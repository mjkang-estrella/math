import CodeLoopGeom

/-!
# Coordinate types for the two length-50 codes

Label sets `H1`/`H2` (seven elements each) carry multiplicity five, the other eight
nonzero vectors of `W` multiplicity one: 43 coordinates.  The simplex part `B`
(nonzero vectors with last coordinate zero) adds seven: 50 in total.
-/

/-- The label set of code `i`: `H1` for `i = 0`, `H2` for `i = 1`. -/
def HofI (i : Fin 2) : Finset W4 := if i = 0 then H1 else H2

theorem H1_card : H1.card = 7 := by
  have h0 : 0 ∈ cube0 := mem_cube0.mpr rfl
  have hc : (cube0.erase 0).card = cube0.card - 1 := Finset.card_erase_of_mem h0
  have hE1 : H1 = cube0.erase 0 := rfl
  rw [hE1, hc, cube0_card]

theorem HofI_card (i : Fin 2) : (HofI i).card = 7 := by
  unfold HofI
  split
  · exact H1_card
  · exact H2_card

/-- The seven labels are nonzero vectors. -/
theorem HofI_ne_zero {i : Fin 2} {a : W4} (h : a ∈ HofI i) : a ≠ 0 := by
  unfold HofI at h
  split at h
  · exact (mem_H1.mp h).2
  · rcases mem_H2.mp h with hP | hL
    · exact ne_zero_of_apply_one hP.1
    · exact hL.2.2

/-- Column multiplicity: five on the label set, one elsewhere. -/
def mult (i : Fin 2) (a : W4) : Nat := if a ∈ HofI i then 5 else 1

theorem HofI_card_of_mem {i : Fin 2} {a : W4} (h : a ∈ HofI i) : mult i a = 5 := by
  unfold mult; simp [h]

theorem HofI_card_of_not_mem {i : Fin 2} {a : W4} (h : ¬ a ∈ HofI i) : mult i a = 1 := by
  unfold mult; simp [h]

/-- A coordinate of code `i`: a nonzero vector and a copy index below the multiplicity. -/
abbrev Coord (i : Fin 2) : Type := Σ a : {a : W4 // a ≠ 0}, Fin (mult i ↑a)

/-- The coordinate cardinality: seven label columns of multiplicity five and eight
single columns: `35 + 8 = 43`. -/
theorem coord_card (i : Fin 2) : Fintype.card (Coord i) = 43 := by
  classical
  rw [Fintype.card_sigma]
  have hc : ∀ a : {a : W4 // a ≠ 0}, Fintype.card (Fin (mult i a)) = mult i a :=
    fun _ => Fintype.card_fin _
  have hsum : ∑ x : {a : W4 // a ≠ 0}, Fintype.card (Fin (mult i x))
      = ∑ x : {a : W4 // a ≠ 0}, mult i x := Fintype.sum_congr _ _ hc
  rw [hsum]
  have hmem : ∀ a : W4, a ∈ (Finset.univ.erase 0 : Finset W4) ↔ a ≠ 0 :=
    fun _ => ⟨fun h => (Finset.mem_erase.mp h).1,
      fun h => Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩
  rw [← Finset.sum_subtype (Finset.univ.erase 0 : Finset W4) hmem (fun a => mult i a)]
  have hE : (Finset.univ : Finset W4).card = 16 := by
    rw [Finset.card_univ]; exact card_W4
  have h15 : ((Finset.univ.erase 0 : Finset W4)).card = 15 := by
    have hc15 := Finset.card_erase_of_mem (Finset.mem_univ (0:W4))
    rw [hc15, hE]
  have hHsub : ∀ a ∈ HofI i, a ≠ 0 := fun _ h => HofI_ne_zero h
  have heH : (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => a ∈ HofI i) = HofI i := by
    apply Finset.ext; intro a
    constructor
    · intro h
      have h1 := Finset.mem_filter.mp h
      exact h1.2
    · intro h
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨HofI_ne_zero h, Finset.mem_univ _⟩, h⟩
  have hF : ((Finset.univ.erase 0 : Finset W4).filter fun a : W4 => a ∈ HofI i).card = 7 := by
    rw [heH]; exact HofI_card i
  have h5s : (∑ a ∈ (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => a ∈ HofI i),
      mult i a) = 35 := by
    have hfun : ∀ a ∈ (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => a ∈ HofI i),
        mult i a = (5:Nat) := by
      intro a ha
      rw [HofI_card_of_mem (Finset.mem_filter.mp ha).2]
    rw [Finset.sum_congr rfl hfun, Finset.sum_const, smul_eq_mul, hF]
  have h1s : (∑ a ∈ (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => ¬ a ∈ HofI i),
      mult i a) = 8 := by
    have hfun : ∀ a ∈ (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => ¬ a ∈ HofI i),
        mult i a = (1:Nat) := by
      intro a ha
      rw [HofI_card_of_not_mem (Finset.mem_filter.mp ha).2]
    have hY : ((Finset.univ.erase 0 : Finset W4).filter fun a : W4 => ¬ a ∈ HofI i).card = 8 := by
      have hsplit2 : ((Finset.univ.erase 0 : Finset W4).filter
          fun a : W4 => a ∈ HofI i).card
          + ((Finset.univ.erase 0 : Finset W4).filter
            fun a : W4 => ¬ a ∈ HofI i).card
          = (Finset.univ.erase 0 : Finset W4).card :=
        @Finset.card_filter_add_card_filter_not W4 (Finset.univ.erase 0)
          (fun a : W4 => a ∈ HofI i) _ _
      rw [heH, HofI_card, h15] at hsplit2
      omega
    rw [Finset.sum_congr rfl hfun, Finset.sum_const, smul_eq_mul, mul_one]; exact hY
  have hsplit : (∑ a ∈ (Finset.univ.erase 0 : Finset W4).filter (fun a : W4 => a ∈ HofI i),
      mult i a) + (∑ a ∈ (Finset.univ.erase 0 : Finset W4).filter
        (fun a : W4 => ¬ a ∈ HofI i), mult i a)
      = ∑ a ∈ Finset.univ.erase 0, mult i a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit, h5s, h1s]

/-!
## The simplex part and the full 50-coordinate space

The simplex labels are the nonzero vectors of `W3` (seven of them; `Fintype`
instance inherited from the subtype), the pairing `dot3` from `CodeLoopFactor`.
-/

/-- The simplex label type: nonzero ternary vectors. -/
abbrev B3 : Type := {x : W3 // x ≠ 0}

/-- A standard basis vector of `W3` is nonzero. -/
theorem e3v_ne_zero (j : Fin 3) : e3v j ≠ 0 := by
  intro h0
  have h1 : e3v j j = 1 := by simp [e3v]
  rw [h0] at h1
  simp at h1

/-- The simplex pairing reads off coordinates. -/
theorem dot3_e3v_left (x : W3) (j : Fin 3) : dot3 x (e3v j) = x j := by
  fin_cases j
  all_goals simp [dot3, e3v]

theorem B3_card : Fintype.card B3 = 7 := by
  have h := Fintype.card_congr (Equiv.sumCompl fun x : W3 => x = 0)
  simp only [Fintype.card_sum, Fintype.card_subtype_eq, card_W3] at h
  change 1 + Fintype.card B3 = 8 at h
  omega

/-- The full 50-coordinate label type of code `i`. -/
abbrev Dcoord (i : Fin 2) : Type := Coord i ⊕ B3

instance dimeFintype (i : Fin 2) : Fintype (Dcoord i) := inferInstance

theorem dcoord_card (i : Fin 2) : Fintype.card (Dcoord i) = 50 := by
  rw [Fintype.card_sum, coord_card, B3_card]

/-- The evaluation of codeword `w` on code-coordinate `c`. -/
def cval (i : Fin 2) (w : W4) : Coord i → ZMod 2 := fun c => dot4 w c.1

/-- The simplex evaluation of `x` on a ternary label. -/
def sval (x : W3) : B3 → ZMod 2 := fun b => dot3 x b

/-- The full codeword map. -/
def dval (i : Fin 2) (w : W4) (x : W3) : Dcoord i → ZMod 2 :=
  Sum.elim (cval i w) (sval x)

/-- Injectivity of the coordinate evaluation: basis columns separate points. -/
theorem cval_inj (i : Fin 2) {w w' : W4} (h : cval i w = cval i w') : w = w' := by
  have hcol : ∀ k : Fin 4, w k = w' k := by
    intro k
    have hc : dot4 w (e4v k) = dot4 w' (e4v k) :=
      congrFun h ⟨⟨e4v k, ne_zero_of_apply_one (e4v_self k)⟩,
        ⟨0, by unfold mult; split <;> decide⟩⟩
    rw [dot4_e4v_left, dot4_e4v_left] at hc
    exact hc
  funext k; exact hcol k

/-- Injectivity of the joint codeword map. -/
theorem dval_inj (i : Fin 2) {w w' : W4} {x x' : W3}
    (h : dval i w x = dval i w' x') : w = w' ∧ x = x' := by
  constructor
  · have hc : cval i w = cval i w' := by
      funext c
      exact congrFun h (Sum.inl c)
    exact cval_inj i hc
  · have hcol : ∀ j : Fin 3, x j = x' j := by
      intro j
      have hcc : dot3 x (e3v j) = dot3 x' (e3v j) :=
        congrFun h (Sum.inr ⟨e3v j, e3v_ne_zero j⟩)
      rw [dot3_e3v_left, dot3_e3v_left] at hcc
      exact hcc
    funext j; exact hcol j
