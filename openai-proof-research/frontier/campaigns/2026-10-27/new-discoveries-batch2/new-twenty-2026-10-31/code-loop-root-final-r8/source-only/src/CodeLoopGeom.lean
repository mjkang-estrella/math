import Mathlib.Data.Finset.Lattice.Basic
import CodeLoopSets

/-!
# MathDB 343790 geometry: the column sets H1 and H2

The two seven-element column sets of the witness, their zero vector sums, and
the parity of evaluation counts.  Every cardinality is obtained from explicit
fibre symmetries (coordinate flips) or the fibre theorem of `CodeLoopCount`;
no enumeration, no oracle.
-/

/-- Symmetry of the pairing on `W4`. -/
theorem dot4_comm (u v : W4) : dot4 u v = dot4 v u := by
  simp only [dot4]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The cube of vectors with vanishing fourth coordinate (0-based index 3):
the span of the first three unit vectors. -/
def cube0 : Finset W4 := Finset.univ.filter fun a : W4 => a 3 = 0

theorem mem_cube0 {a : W4} : a ∈ cube0 ↔ a 3 = 0 :=
  Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Membership in the filtered universe, as an iff on the predicate. -/
theorem mem_univ_filter {p : W4 → Prop} [DecidablePred p] {a : W4} :
    a ∈ Finset.univ.filter p ↔ p a :=
  Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem cube0_card : cube0.card = 8 := by
  have hsub : Fintype.card {a : W4 // a 3 = 0}
      = Fintype.card {a : W4 // dot4 (e4v 3) a = 0} :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl W4) fun a =>
      ⟨fun h => by rw [dot4_comm, dot4_e4v_left]; exact h,
       fun h => by
         have h' : dot4 (e4v 3) a = 0 := h
         rw [show (a 3 : ZMod 2) = dot4 a (e4v 3) from
           (dot4_e4v_left a 3).symm, dot4_comm]
         exact h'⟩)
  have hmem : ∀ a : W4, a ∈ cube0 ↔ a 3 = 0 := fun _ => mem_cube0
  rw [← Fintype.card_of_subtype cube0 hmem, hsub,
    dot4_fiber_zero_card (ne_zero_of_apply_one (e4v_self 3))]

/-- `H1`: the nonzero vectors with vanishing last coordinate; the source
span(e1,e2,e3) minus zero, zero-based. -/
def H1 : Finset W4 := cube0.erase 0

theorem mem_H1 {a : W4} : a ∈ H1 ↔ a 3 = 0 ∧ a ≠ 0 :=
  Finset.mem_erase.trans
    ⟨fun h => ⟨mem_cube0.mp h.2, h.1⟩, fun h => ⟨h.2, mem_cube0.mpr h.1⟩⟩

/-- The flip half of any set closed under a coordinate flip has half the
cardinality: the one-fibre version. -/
theorem flip_half_one (C : Finset W4) (j : Fin 4)
    (hc : ∀ a ∈ C, a + e4v j ∈ C) :
    2 * (C.filter (fun x => x j = 1)).card = C.card := by
  have hflip := flip_card_eq C j hc
  have hsplit : (C.filter (fun x => x j = 1)).card
      + (C.filter fun x => ¬(x j = 1)).card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) (p := fun x : W4 => x j = 1)
  have hs : (C.filter (fun x => x j = 0))
      = C.filter fun x => ¬(x j = 1) := by
    apply Finset.ext; intro x
    constructor
    · intro h
      obtain ⟨hC, h0⟩ := Finset.mem_filter.mp h
      have h0' : x j = 0 := h0
      exact Finset.mem_filter.mpr ⟨hC, fun h1 => by
        rw [h0'] at h1; exact zmod2_one_ne_zero h1.symm⟩
    · intro h
      obtain ⟨hC, h1⟩ := Finset.mem_filter.mp h
      have h1' : ¬(x j = 1) := h1
      exact Finset.mem_filter.mpr ⟨hC, (zmod2_cases (x j)).resolve_right h1'⟩
  have heq : (C.filter (fun x => x j = 0)).card
      = (C.filter fun x => ¬(x j = 1)).card := congrArg Finset.card hs
  have hflip := flip_card_eq C j hc
  omega

/-- The flip half of any set closed under a coordinate flip has half the
cardinality: the zero-fibre version. -/
theorem flip_half_zero (C : Finset W4) (j : Fin 4)
    (hc : ∀ a ∈ C, a + e4v j ∈ C) :
    2 * (C.filter (fun x => x j = 0)).card = C.card := by
  have hsplit : (C.filter (fun x => x j = 1)).card
      + (C.filter fun x => ¬(x j = 1)).card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) (p := fun x : W4 => x j = 1)
  have hs : (C.filter (fun x => x j = 0))
      = C.filter fun x => ¬(x j = 1) := by
    apply Finset.ext; intro x
    constructor
    · intro h
      obtain ⟨hC, h0⟩ := Finset.mem_filter.mp h
      have h0' : x j = 0 := h0
      exact Finset.mem_filter.mpr ⟨hC, fun h1 => by
        rw [h0'] at h1; exact zmod2_one_ne_zero h1.symm⟩
    · intro h
      obtain ⟨hC, h1⟩ := Finset.mem_filter.mp h
      have h1' : ¬(x j = 1) := h1
      exact Finset.mem_filter.mpr ⟨hC, (zmod2_cases (x j)).resolve_right h1'⟩
  have heq : (C.filter (fun x => x j = 0)).card
      = (C.filter fun x => ¬(x j = 1)).card := congrArg Finset.card hs
  have hflip := flip_card_eq C j hc
  omega

/-- A filtered subset whose predicate fails on all of `s` is empty. -/
theorem filter_card_zero {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ x ∈ s, ¬ p x) : (s.filter p).card = 0 := by
  have hE : s.filter p = ∅ := by
    apply Finset.ext; intro x
    constructor
    · intro hm
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
      exact absurd h2 (h x h1)
    · intro hm; exact absurd hm (Finset.notMem_empty x)
  rw [hE, Finset.card_empty]

theorem card_union_disjoint {α : Type*} [DecidableEq α] {s t : Finset α}
    (hd : Disjoint s t) :
    (s ∪ t).card = s.card + t.card := by
  classical
  have hc0 : (s ∩ t).card = 0 := by
    have hE : s ∩ t = ∅ := by
      apply Finset.ext; intro a
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := Finset.mem_inter.mp h
        exact absurd h2 (Finset.disjoint_left.mp hd h1)
      · intro h; exact absurd h (Finset.notMem_empty a)
    rw [hE, Finset.card_empty]
  have hadd := Finset.card_union_add_card_inter s t
  omega

/-- Cancellation of a repeated summand in characteristic two. -/
theorem zmod2_cancel (a b : ZMod 2) : a + b + a = b := by
  rw [add_assoc, add_comm b a, ← add_assoc, zmod2_add_self, zero_add]

/-- A `W4` vector is zero once all four coordinates are. -/
theorem W4eq_of_coords {w : W4} (h0 : w 0 = 0) (h1 : w 1 = 0) (h2 : w 2 = 0)
    (h3 : w 3 = 0) : w = 0 := by
  funext i
  refine Fin.cases (motive := fun i => w i = 0) h0 ?_ i
  intro a
  refine Fin.cases (motive := fun i => w i.succ = 0) h1 ?_ a
  intro b
  refine Fin.cases (motive := fun i => w i.succ.succ = 0) h2 ?_ b
  intro c
  refine Fin.cases (motive := fun i => w i.succ.succ.succ = 0) h3 ?_ c
  intro d
  exact Fin.elim0 d

/-- A coordinate of `Fin 4` distinct from `0`, `1` and `2` is `3`. -/
theorem fin_eq_three {j : Fin 4} (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) : j = 3 := by
  have hlt : j.val < 4 := j.isLt
  have hv : j.val = 3 := by
    rcases Nat.lt_or_ge j.val 3 with hl | hl
    · rcases Nat.lt_or_ge j.val 2 with hl2 | hl2
      · rcases Nat.lt_or_ge j.val 1 with hl1 | hl1
        · refine absurd (Fin.ext ?_) h0
          show j.val = (0 : Fin 4).val
          omega
        · refine absurd (Fin.ext ?_) h1
          show j.val = (1 : Fin 4).val
          omega
      · refine absurd (Fin.ext ?_) h2
        show j.val = (2 : Fin 4).val
        omega
    · omega
  exact Fin.ext hv

/-- The nonzero vectors of the hyperplane sum to zero: each nontrivial
coordinate splits the cube into two equal flip halves. -/
theorem sum_H1_zero : ∑ a ∈ H1, a = 0 := by
  funext j
  rw [sum_apply4, Pi.zero_apply]
  have hAB : ((H1.filter (fun x => x j = 1)).card : ZMod 2) = ∑ x ∈ H1, x j :=
    cast_filter_one_card_eq_sum (s := H1) (v := fun x => x j)
  rw [← hAB]
  by_cases h3 : j = 3
  · subst h3
    have hempty : H1.filter (fun x => x 3 = 1) = ∅ := by
      apply Finset.ext; intro a
      constructor
      · intro h
        obtain ⟨hH, h1⟩ := Finset.mem_filter.mp h
        have h1' : a 3 = 1 := h1
        have h0' : a 3 = 0 := (mem_H1.mp hH).1
        exact absurd (h1'.symm.trans h0') (by
          intro hh; exact zmod2_one_ne_zero hh)
      · intro h; exact absurd h (Finset.notMem_empty a)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  · have hc : ∀ a ∈ cube0, a + e4v j ∈ cube0 := by
      intro a haC
      rw [mem_cube0] at haC ⊢
      rw [Pi.add_apply, e4v_apply_ne (Ne.symm h3), haC, add_zero]
    have hc1 := flip_half_one cube0 j hc
    have h8 : cube0.card = 8 := cube0_card
    have hlt : j.val < 4 := j.isLt
    have hc4 : (cube0.filter (fun x => x j = 1)).card = 4 := by omega
    have heqF : H1.filter (fun x => x j = 1) = cube0.filter (fun x => x j = 1) := by
      apply Finset.ext; intro a
      constructor
      · intro h
        obtain ⟨hH, hj⟩ := Finset.mem_filter.mp h
        have hj' : a j = 1 := hj
        exact Finset.mem_filter.mpr ⟨mem_cube0.mpr (mem_H1.mp hH).1, hj'⟩
      · intro h
        obtain ⟨hC, hj⟩ := Finset.mem_filter.mp h
        have hj' : a j = 1 := hj
        exact Finset.mem_filter.mpr
          ⟨mem_H1.mpr ⟨mem_cube0.mp hC, ne_zero_of_apply_one hj'⟩, hj'⟩
    rw [heqF, hc4]
    exact cast_two_mul 2

/-- The affine plane block of `H2`: last coordinate one, third zero
(one-based: the e4, e4+e1, e4+e2, e4+e1+e2 block). -/
def planeP : Finset W4 := Finset.univ.filter fun a : W4 => a 3 = 1 ∧ a 2 = 0

/-- The ambient cube of the line block of `H2`: first and last coordinates
zero. -/
def lineC : Finset W4 := Finset.univ.filter fun a : W4 => a 1 = 0 ∧ a 3 = 0

/-- The line block of `H2` without zero (e1, e3, e1+e3). -/
def lineE : Finset W4 := lineC.erase 0

/-- `H2`: the seven-element column set of the witness. -/
def H2 : Finset W4 := planeP ∪ lineE

theorem mem_planeP {a : W4} : a ∈ planeP ↔ a 3 = 1 ∧ a 2 = 0 := mem_univ_filter

theorem mem_lineC {a : W4} : a ∈ lineC ↔ a 1 = 0 ∧ a 3 = 0 := mem_univ_filter

theorem mem_lineE {a : W4} : a ∈ lineE ↔ a 1 = 0 ∧ a 3 = 0 ∧ a ≠ 0 :=
  Finset.mem_erase.trans
    ⟨fun h => let hc := mem_lineC.mp h.2; ⟨hc.1, hc.2, h.1⟩,
      fun h => ⟨h.2.2, mem_lineC.mpr ⟨h.1, h.2.1⟩⟩⟩

theorem mem_H2 {a : W4} :
    a ∈ H2 ↔ (a 3 = 1 ∧ a 2 = 0) ∨ (a 1 = 0 ∧ a 3 = 0 ∧ a ≠ 0) := by
  rw [show H2 = planeP ∪ lineE from rfl, Finset.mem_union]
  exact or_congr mem_planeP mem_lineE

theorem planeP_card : planeP.card = 4 := by
  have hc : ∀ a ∈ Finset.univ.filter (fun a : W4 => a 3 = 1),
      a + e4v 2 ∈ Finset.univ.filter (fun a : W4 => a 3 = 1) := by
    intro a ha
    have h1 : a 3 = 1 := (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Pi.add_apply, e4v_apply_ne (by decide), h1, add_zero]
  have hsub : Fintype.card {a : W4 // a 3 = 1}
      = Fintype.card {a : W4 // dot4 (e4v 3) a = 1} :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl W4) fun a =>
      ⟨fun h => by rw [dot4_comm, dot4_e4v_left]; exact h,
       fun h => by
         have h' : dot4 (e4v 3) a = 1 := h
         rw [show (a 3 : ZMod 2) = dot4 a (e4v 3) from
           (dot4_e4v_left a 3).symm, dot4_comm]
         exact h'⟩)
  have h8 : (Finset.univ.filter (fun a : W4 => a 3 = 1)).card = 8 := by
    rw [← Fintype.card_of_subtype
      (Finset.univ.filter fun a : W4 => a 3 = 1)
      (fun a => mem_univ_filter), hsub,
      dot4_fiber_one_card (ne_zero_of_apply_one (e4v_self 3))]
  have hc0 := flip_half_zero (Finset.univ.filter fun a : W4 => a 3 = 1) 2 hc
  have heqP : planeP
      = (Finset.univ.filter (fun a : W4 => a 3 = 1)).filter (fun x => x 2 = 0) := by
    apply Finset.ext; intro a
    rw [mem_planeP, Finset.mem_filter, mem_univ_filter]
  have hc4 : ((Finset.univ.filter (fun a : W4 => a 3 = 1)).filter
      (fun x => x 2 = 0)).card = 4 := by omega
  rw [heqP]; exact hc4

/-- The line cube has four elements: the flip in the second coordinate halves
the eight-point cube `cube0`. -/
theorem lineC_card : lineC.card = 4 := by
  have hc : ∀ a ∈ cube0, a + e4v 1 ∈ cube0 := by
    intro a haC
    rw [mem_cube0] at haC ⊢
    rw [Pi.add_apply, e4v_apply_ne (by decide), haC, add_zero]
  have h8 := cube0_card
  have hc0 := flip_half_zero cube0 1 hc
  have hc4 : (cube0.filter (fun x => x 1 = 0)).card = 4 := by omega
  have heqL : lineC = cube0.filter (fun x => x 1 = 0) := by
    apply Finset.ext; intro a
    rw [mem_lineC, Finset.mem_filter, mem_cube0]
    constructor
    · intro h; exact ⟨h.2, h.1⟩
    · intro h; exact ⟨h.2, h.1⟩
  rw [heqL]; exact hc4

theorem lineE_card : lineE.card = 3 := by
  have h0 : (0 : W4) ∈ lineC := by
    rw [mem_lineC]; exact ⟨rfl, rfl⟩
  rw [show lineE = lineC.erase 0 from rfl, Finset.card_erase_of_mem h0, lineC_card]

theorem H2_disjoint : Disjoint planeP lineE := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  have h3 := (mem_planeP.mp h1).1
  have h0 := (mem_lineE.mp h2).2.1
  exact zmod2_one_ne_zero (h3.symm.trans h0)

theorem H2_card : H2.card = 7 := by
  rw [show H2 = planeP ∪ lineE from rfl, card_union_disjoint H2_disjoint,
    planeP_card, lineE_card]

/-- The parity of the evaluation count on any zero-sum set: for `w` and a
finset `H` of vectors with `∑ H = 0`, the number of `a ∈ H` with
`dot w a = 1` is even. -/
theorem count_even_of_sum_zero {H : Finset W4} (hsum : ∑ x ∈ H, x = 0) (w : W4) :
    ((H.filter (fun x => dot4 w x = 1)).card : ZMod 2) = 0 := by
  have hAB : ((H.filter (fun x => dot4 w x = 1)).card : ZMod 2)
      = ∑ x ∈ H, dot4 w x :=
    cast_filter_one_card_eq_sum (s := H) (v := fun x => dot4 w x)
  rw [hAB, ← dot4_sum, hsum, dot4_zero_right]

/-- Every nonzero `w` takes the value one on exactly eight nonzero vectors. -/
theorem count8 {w : W4} (hw : w ≠ 0) :
    (Finset.univ.filter (fun a : W4 => a ≠ 0 ∧ dot4 w a = 1)).card = 8 := by
  have he : (Finset.univ.filter fun a : W4 => a ≠ 0 ∧ dot4 w a = 1)
      = Finset.univ.filter (fun a : W4 => dot4 w a = 1) := by
    apply Finset.ext; intro a
    constructor
    · intro h
      have hm := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hm.1, hm.2.2⟩
    · intro h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro h0
        have h1 := Finset.mem_filter.mp h
        have h2 := h1.2
        rw [show (a : W4) = 0 from h0, dot4_zero_right] at h2
        exact zmod2_one_ne_zero h2.symm
      · exact (Finset.mem_filter.mp h).2
  rw [he, ← Fintype.card_of_subtype
    (Finset.univ.filter fun a : W4 => dot4 w a = 1)
    (fun a => Finset.mem_filter.trans
      ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩),
    dot4_fiber_one_card hw]

/-- `H2` detects every nonzero vector: a vector pairing to zero with all of
`H2` is zero, i.e. the columns of `H2` span `W4`. -/
theorem H2_detector {w : W4} (h : ∀ a ∈ H2, dot4 w a = 0) : w = 0 := by
  have m1 : e4v 3 ∈ H2 := mem_H2.mpr (Or.inl ⟨by simp [e4v], by simp [e4v]⟩)
  have m2 : e4v 3 + e4v 0 ∈ H2 :=
    mem_H2.mpr (Or.inl ⟨by simp [Pi.add_apply, e4v], by simp [Pi.add_apply, e4v]⟩)
  have m3 : e4v 3 + e4v 1 ∈ H2 :=
    mem_H2.mpr (Or.inl ⟨by simp [Pi.add_apply, e4v], by simp [Pi.add_apply, e4v]⟩)
  have m4 : e4v 3 + e4v 0 + e4v 1 ∈ H2 :=
    mem_H2.mpr (Or.inl ⟨by simp [Pi.add_apply, e4v], by simp [Pi.add_apply, e4v]⟩)
  have m5 : e4v 0 ∈ H2 := mem_H2.mpr (Or.inr
    ⟨by simp [e4v], by simp [e4v], ne_zero_of_apply_one (e4v_self 0)⟩)
  have m6 : e4v 2 ∈ H2 := mem_H2.mpr (Or.inr
    ⟨by simp [e4v], by simp [e4v], ne_zero_of_apply_one (e4v_self 2)⟩)
  have c3 : w 3 = 0 := by
    have hh := h _ m1
    rw [dot4_e4v_left] at hh
    exact hh
  have c0 : w 0 = 0 := by
    have hh := h _ m5
    rw [dot4_e4v_left] at hh
    exact hh
  have c2 : w 2 = 0 := by
    have hh := h _ m6
    rw [dot4_e4v_left] at hh
    exact hh
  have c31 : w 3 + w 1 = 0 := by
    have hh := h _ m3
    rw [dot4_add_left, dot4_e4v_left, dot4_e4v_left] at hh
    exact hh
  have c1 : w 1 = 0 := by
    have e1 : w 1 = w 3 + w 1 + w 3 := (zmod2_cancel (w 3) (w 1)).symm
    rw [e1, c31, zero_add, c3]
  exact W4eq_of_coords c0 c1 c2 c3

/-- The seven vectors of `H2` sum to zero. -/
theorem sum_H2_zero : ∑ x ∈ H2, x = 0 := by
  funext j
  rw [sum_apply4, Pi.zero_apply]
  have hAB : ((H2.filter (fun x => x j = 1)).card : ZMod 2) = ∑ x ∈ H2, x j :=
    cast_filter_one_card_eq_sum (s := H2) (v := fun x => x j)
  rw [← hAB]
  have hsplit : (H2.filter (fun x => x j = 1)).card
      = (planeP.filter (fun x => x j = 1)).card
        + (lineE.filter (fun x => x j = 1)).card := by
    have hfu : (H2.filter (fun x => x j = 1))
        = (planeP ∪ lineE).filter (fun x => x j = 1) := by rfl
    rw [hfu, Finset.filter_union]
    have hd : Disjoint (planeP.filter (fun x => x j = 1))
        (lineE.filter (fun x => x j = 1)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have h1a : x ∈ planeP := (Finset.mem_filter.mp h1).1
      have h2a : x ∈ lineE := (Finset.mem_filter.mp h2).1
      exact absurd h2a (Finset.disjoint_left.mp H2_disjoint h1a)
    exact card_union_disjoint hd
  rw [hsplit, Nat.cast_add]
  have hpc0 : ∀ a ∈ planeP, a + e4v 0 ∈ planeP := by
    intro a ha
    obtain ⟨h3, h2⟩ := mem_planeP.mp ha
    refine mem_planeP.mpr ⟨?_, ?_⟩
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h3, add_zero]
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h2, add_zero]
  have hpc1 : ∀ a ∈ planeP, a + e4v 1 ∈ planeP := by
    intro a ha
    obtain ⟨h3, h2⟩ := mem_planeP.mp ha
    refine mem_planeP.mpr ⟨?_, ?_⟩
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h3, add_zero]
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h2, add_zero]
  have hlc0 : ∀ a ∈ lineC, a + e4v 0 ∈ lineC := by
    intro a ha
    obtain ⟨h1, h3⟩ := mem_lineC.mp ha
    refine mem_lineC.mpr ⟨?_, ?_⟩
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h1, add_zero]
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h3, add_zero]
  have hlc2 : ∀ a ∈ lineC, a + e4v 2 ∈ lineC := by
    intro a ha
    obtain ⟨h1, h3⟩ := mem_lineC.mp ha
    refine mem_lineC.mpr ⟨?_, ?_⟩
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h1, add_zero]
    · rw [Pi.add_apply, e4v_apply_ne (by decide), h3, add_zero]
  have hle0 : (lineE.filter fun x : W4 => x 0 = 1)
      = lineC.filter (fun x => x 0 = 1) := by
    apply Finset.ext; intro x
    constructor
    · intro hh
      have hh' : x ∈ lineE ∧ (fun x : W4 => x 0 = 1) x := Finset.mem_filter.mp hh
      have hE : x 1 = 0 ∧ x 3 = 0 ∧ x ≠ 0 := mem_lineE.mp hh'.1
      exact Finset.mem_filter.mpr ⟨mem_lineC.mpr ⟨hE.1, hE.2.1⟩, hh'.2⟩
    · intro hh
      have hh' : x ∈ lineC ∧ (fun x : W4 => x 0 = 1) x := Finset.mem_filter.mp hh
      have hC : x 1 = 0 ∧ x 3 = 0 := mem_lineC.mp hh'.1
      have hn : x ≠ 0 := ne_zero_of_apply_one hh'.2
      exact Finset.mem_filter.mpr
        ⟨mem_lineE.mpr ⟨hC.1, hC.2, hn⟩, hh'.2⟩
  have hle2 : (lineE.filter fun x : W4 => x 2 = 1)
      = lineC.filter (fun x => x 2 = 1) := by
    apply Finset.ext; intro x
    constructor
    · intro hh
      have hh' : x ∈ lineE ∧ (fun x : W4 => x 2 = 1) x := Finset.mem_filter.mp hh
      have hE : x 1 = 0 ∧ x 3 = 0 ∧ x ≠ 0 := mem_lineE.mp hh'.1
      exact Finset.mem_filter.mpr ⟨mem_lineC.mpr ⟨hE.1, hE.2.1⟩, hh'.2⟩
    · intro hh
      have hh' : x ∈ lineC ∧ (fun x : W4 => x 2 = 1) x := Finset.mem_filter.mp hh
      have hC : x 1 = 0 ∧ x 3 = 0 := mem_lineC.mp hh'.1
      have hn : x ≠ 0 := ne_zero_of_apply_one hh'.2
      exact Finset.mem_filter.mpr
        ⟨mem_lineE.mpr ⟨hC.1, hC.2, hn⟩, hh'.2⟩
  by_cases hj0 : j = 0
  · subst hj0
    have hp := flip_half_one planeP 0 hpc0
    have hp4 := planeP_card
    have hpv : (planeP.filter fun x : W4 => x 0 = 1).card = 2 := by omega
    have hc := flip_half_one lineC 0 hlc0
    have hl4 := lineC_card
    have hlv : (lineC.filter fun x : W4 => x 0 = 1).card = 2 := by omega
    rw [hle0, hlv, hpv]
    exact congrArg₂ (· + ·) (cast_two_mul 1) (cast_two_mul 1)
  · by_cases hj1 : j = 1
    · subst hj1
      have hp := flip_half_one planeP 1 hpc1
      have hp4 := planeP_card
      have hpv : (planeP.filter fun x : W4 => x 1 = 1).card = 2 := by omega
      have hlv : (lineE.filter fun x : W4 => x 1 = 1).card = 0 :=
        filter_card_zero lineE _ (fun x hx h1 => by
          have h1' : x 1 = 0 := (mem_lineE.mp hx).1
          have h1'' : x 1 = 1 := h1
          exact zmod2_one_ne_zero (h1''.symm.trans h1'))
      rw [hpv, hlv, Nat.cast_zero, add_zero]
      exact cast_two_mul 1
    · by_cases hj2 : j = 2
      · subst hj2
        have hp0 : (planeP.filter fun x : W4 => x 2 = 1).card = 0 :=
          filter_card_zero planeP _ (fun x hx h1 => by
            have h2 : x 2 = 0 := (mem_planeP.mp hx).2
            have h2' : x 2 = 1 := h1
            exact zmod2_one_ne_zero (h2'.symm.trans h2))
        have hc := flip_half_one lineC 2 hlc2
        have hl4 := lineC_card
        have hlv : (lineC.filter fun x : W4 => x 2 = 1).card = 2 := by omega
        rw [hp0, hle2, hlv, Nat.cast_zero, zero_add]
        exact cast_two_mul 1
      · have hj3 : j = 3 := fin_eq_three hj0 hj1 hj2
        subst hj3
        have hpE : (planeP.filter (fun x => x 3 = 1)) = planeP := by
          apply Finset.ext; intro x
          rw [Finset.mem_filter, mem_planeP]
          exact ⟨fun hh => hh.1, fun hh => ⟨hh, hh.1⟩⟩
        have hpv : (planeP.filter fun x : W4 => x 3 = 1).card = 4 := by
          rw [hpE, planeP_card]
        have hlv : (lineE.filter fun x : W4 => x 3 = 1).card = 0 :=
          filter_card_zero lineE _ (fun x hx h1 => by
            have h3' : x 3 = 0 := (mem_lineE.mp hx).2.1
            have h3'' : x 3 = 1 := h1
            exact zmod2_one_ne_zero (h3''.symm.trans h3'))
        rw [hpv, hlv, Nat.cast_zero, add_zero]
        exact cast_two_mul 2
