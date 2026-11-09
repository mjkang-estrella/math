import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# MathDB 343790 code-loop factor: binary factor, normalization, identities

Faithful 0-based transcription of the reviewed source factor.  Every identity
below is proved for all inputs by kernel case analysis on the coordinates
(`ZMod 2` has exactly the elements 0 and 1); no sampled checks, no oracle.
-/

/-- The reviewed factor `f` on coordinate triples over `ZMod 2`:
`f(x,y) = x0*y0 + x1*y1 + x2*y2 + x0*y1 + x0*y2 + x1*y2
        + x0*x1*y2 + x0*x2*y1 + x1*x2*y0`. -/
def codeLoopF (x y : Fin 3 → ZMod 2) : ZMod 2 :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2
    + x 0 * y 1 + x 0 * y 2 + x 1 * y 2
    + x 0 * x 1 * y 2 + x 0 * x 2 * y 1 + x 1 * x 2 * y 0

/-- The reviewed companion polynomial `q(x) = 1 + (1+x0)*(1+x1)*(1+x2)`. -/
def codeLoopQ (x : Fin 3 → ZMod 2) : ZMod 2 :=
  1 + (1 + x 0) * (1 + x 1) * (1 + x 2)

/-- Normalization, all inputs: `f(0,y) = 0`. -/
theorem codeLoopF_zero_left (y : Fin 3 → ZMod 2) : codeLoopF 0 y = 0 := by
  simp only [codeLoopF, Pi.zero_apply]
  ring

/-- Normalization, all inputs: `f(x,0) = 0`. -/
theorem codeLoopF_zero_right (x : Fin 3 → ZMod 2) : codeLoopF x 0 = 0 := by
  simp only [codeLoopF, Pi.zero_apply]
  ring

/-- `(1 : ZMod 2).val = 1`. -/
theorem zmod2_val_one : (1 : ZMod 2).val = 1 :=
  @ZMod.val_one 2 ⟨by decide⟩

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val < 2 := ZMod.val_lt a
  rcases Nat.lt_or_ge a.val 1 with c | c
  · exact Or.inl (ZMod.val_injective 2 ((Nat.lt_one_iff.mp c).trans ZMod.val_zero.symm))
  · exact Or.inr (ZMod.val_injective 2
      ((Nat.le_antisymm (Nat.lt_succ_iff.mp h) c).trans zmod2_val_one.symm))

/-- Elements of `ZMod 2` are idempotent. -/
theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  rcases zmod2_cases a with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- Elements of `ZMod 2` satisfy `a + a = 0`. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- The unit-cancellation step used in characteristic two. -/
theorem zmod2_one_add (x : ZMod 2) : x = 1 + (1 + x) := by
  rw [← add_assoc, zmod2_add_self, zero_add]

/-- Identity 1, all inputs: `f(x,x) = q(x)`. -/
theorem codeLoopF_self (x : Fin 3 → ZMod 2) : codeLoopF x x = codeLoopQ x := by
  simp only [codeLoopF, codeLoopQ]
  rcases zmod2_cases (x 0) with hx0 | hx0 <;> rw [hx0] <;>
  rcases zmod2_cases (x 1) with hx1 | hx1 <;> rw [hx1] <;>
  rcases zmod2_cases (x 2) with hx2 | hx2 <;> rw [hx2] <;>
  decide

/-- Identity 2, all inputs: `f(x,y) + f(y,x) = q(x+y) + q(x) + q(y)`. -/
theorem codeLoopF_symmetry (x y : Fin 3 → ZMod 2) :
    codeLoopF x y + codeLoopF y x
      = codeLoopQ (x + y) + codeLoopQ x + codeLoopQ y := by
  simp only [codeLoopF, codeLoopQ, Pi.add_apply]
  rcases zmod2_cases (x 0) with hx0 | hx0 <;> rw [hx0] <;>
  rcases zmod2_cases (x 1) with hx1 | hx1 <;> rw [hx1] <;>
  rcases zmod2_cases (x 2) with hx2 | hx2 <;> rw [hx2] <;>
  rcases zmod2_cases (y 0) with hy0 | hy0 <;> rw [hy0] <;>
  rcases zmod2_cases (y 1) with hy1 | hy1 <;> rw [hy1] <;>
  rcases zmod2_cases (y 2) with hy2 | hy2 <;> rw [hy2] <;>
  decide

/-- Identity 3, all inputs: the coboundary of `f` is the alternating triple form. -/
theorem codeLoopF_coboundary (x y z : Fin 3 → ZMod 2) :
    codeLoopF x y + codeLoopF (x + y) z + codeLoopF y z + codeLoopF x (y + z)
      = x 0 * y 1 * z 2 + x 0 * y 2 * z 1 + x 1 * y 0 * z 2
        + x 1 * y 2 * z 0 + x 2 * y 0 * z 1 + x 2 * y 1 * z 0 := by
  simp only [codeLoopF, Pi.add_apply]
  rcases zmod2_cases (x 0) with hx0 | hx0 <;> rw [hx0] <;>
  rcases zmod2_cases (x 1) with hx1 | hx1 <;> rw [hx1] <;>
  rcases zmod2_cases (x 2) with hx2 | hx2 <;> rw [hx2] <;>
  rcases zmod2_cases (y 0) with hy0 | hy0 <;> rw [hy0] <;>
  rcases zmod2_cases (y 1) with hy1 | hy1 <;> rw [hy1] <;>
  rcases zmod2_cases (y 2) with hy2 | hy2 <;> rw [hy2] <;>
  rcases zmod2_cases (z 0) with hz0 | hz0 <;> rw [hz0] <;>
  rcases zmod2_cases (z 1) with hz1 | hz1 <;> rw [hz1] <;>
  rcases zmod2_cases (z 2) with hz2 | hz2 <;> rw [hz2] <;>
  decide

/-!
## Ground layer for the code-loop witness

`W4` is the source four-dimensional space `F2^4`; `W3` is the simplex space.
-/

/-- The four-dimensional ground space. -/
abbrev W4 := Fin 4 → ZMod 2

/-- The three-dimensional simplex space. -/
abbrev W3 := Fin 3 → ZMod 2

/-- Standard unit vector of `W4`. -/
def e4v (k : Fin 4) : W4 := fun j => if j = k then (1 : ZMod 2) else 0

/-- Standard unit vector of `W3`. -/
def e3v (k : Fin 3) : W3 := fun j => if j = k then (1 : ZMod 2) else 0

/-- Dot product on `W4`. -/
def dot4 (u v : W4) : ZMod 2 := ∑ i : Fin 4, u i * v i

/-- Dot product on `W3`. -/
def dot3 (u v : W3) : ZMod 2 := ∑ i : Fin 3, u i * v i

theorem dot4_add_left (w u v : W4) : dot4 w (u + v) = dot4 w u + dot4 w v := by
  simp only [dot4, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot3_add_left (w u v : W3) : dot3 w (u + v) = dot3 w u + dot3 w v := by
  simp only [dot3, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot4_add_right (u v w : W4) : dot4 (u + v) w = dot4 u w + dot4 v w := by
  simp only [dot4, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot4_zero_left (w : W4) : dot4 0 w = 0 := by
  simp only [dot4, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem dot3_zero_left (w : W3) : dot3 0 w = 0 := by
  simp only [dot3, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- Cardinality of `W4`. -/
theorem card_W4 : Fintype.card W4 = 16 := by
  rw [Fintype.card_pi, ZMod.card 2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- Cardinality of `W3`. -/
theorem card_W3 : Fintype.card W3 = 8 := by
  rw [Fintype.card_pi, ZMod.card 2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- A nonzero vector of `W4` has a coordinate equal to `1`. -/
theorem exists_one_of_ne_zero4 {w : W4} (hw : w ≠ 0) : ∃ k : Fin 4, w k = 1 := by
  by_contra hc
  have h1 : ∀ k : Fin 4, w k = 0 := by
    intro k
    rcases zmod2_cases (w k) with h0 | h0
    · exact h0
    · exact absurd (⟨k, h0⟩ : ∃ k : Fin 4, w k = 1) hc
  exact hw (funext fun i => by rw [h1 i, Pi.zero_apply])
