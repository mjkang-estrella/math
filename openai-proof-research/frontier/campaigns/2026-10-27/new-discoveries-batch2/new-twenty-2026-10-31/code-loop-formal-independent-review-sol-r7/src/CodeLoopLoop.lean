import CodeLoopSpace
import Mathlib.Tactic.Abel

/-! The common multiplication is explicit and independent of either representation. -/
abbrev CommonLoop := ZMod 2 × (W4 × W3)

def commonMul (a b : CommonLoop) : CommonLoop :=
  (a.1 + b.1 + codeLoopF a.2.2 b.2.2, a.2.1 + b.2.1, a.2.2 + b.2.2)

def commonOne : CommonLoop := (0, 0, 0)

theorem common_one_mul (a : CommonLoop) : commonMul commonOne a = a := by
  rcases a with ⟨s,w,x⟩
  simp [commonMul, commonOne, codeLoopF_zero_left]

theorem common_mul_one (a : CommonLoop) : commonMul a commonOne = a := by
  rcases a with ⟨s,w,x⟩
  simp [commonMul, commonOne, codeLoopF_zero_right]

theorem codeLoopF_moufang (x y z : W3) :
    codeLoopF x y + codeLoopF z x + codeLoopF (x+y) (z+x) =
      codeLoopF y z + codeLoopF (y+z) x + codeLoopF x (y+z+x) := by
  simp only [codeLoopF, Pi.add_apply]
  ring_nf
  simp only [show (3 : ZMod 2) = 1 by decide, show (2 : ZMod 2) = 0 by decide,
    mul_one, mul_zero, add_zero]

theorem common_moufang (a b c : CommonLoop) :
    commonMul (commonMul a b) (commonMul c a) =
      commonMul a (commonMul (commonMul b c) a) := by
  apply Prod.ext
  · change (a.1 + b.1 + codeLoopF a.2.2 b.2.2) +
      (c.1 + a.1 + codeLoopF c.2.2 a.2.2) +
      codeLoopF (a.2.2+b.2.2) (c.2.2+a.2.2) =
      a.1 + ((b.1+c.1+codeLoopF b.2.2 c.2.2)+a.1+
      codeLoopF (b.2.2+c.2.2) a.2.2) +
      codeLoopF a.2.2 (b.2.2+c.2.2+a.2.2)
    calc
      _ = (a.1+b.1+c.1+a.1) + (codeLoopF a.2.2 b.2.2 +
        codeLoopF c.2.2 a.2.2 + codeLoopF (a.2.2+b.2.2) (c.2.2+a.2.2)) := by ring
      _ = _ := by rw [codeLoopF_moufang]; ring
  · apply Prod.ext <;> dsimp [commonMul] <;> abel

theorem common_nonassociative :
    ¬ ∀ a b c : CommonLoop, commonMul (commonMul a b) c = commonMul a (commonMul b c) := by
  intro h
  have hh := congrArg Prod.fst (h (0,0,e3v 0) (0,0,e3v 1) (0,0,e3v 2))
  norm_num [commonMul, codeLoopF, e3v] at hh
  exact (by decide : (4 : ZMod 2) ≠ 3) hh

theorem common_left_cancel (a b c : CommonLoop)
    (h : commonMul a b = commonMul a c) : b = c := by
  have hw : b.2.1 = c.2.1 := add_left_cancel (congrArg (fun p : CommonLoop => p.2.1) h)
  have hx : b.2.2 = c.2.2 := add_left_cancel (congrArg (fun p : CommonLoop => p.2.2) h)
  have hs := congrArg Prod.fst h
  change a.1 + b.1 + codeLoopF a.2.2 b.2.2 = a.1 + c.1 + codeLoopF a.2.2 c.2.2 at hs
  rw [hx] at hs
  exact Prod.ext (add_left_cancel (add_right_cancel hs)) (Prod.ext hw hx)

theorem common_right_cancel (a b c : CommonLoop)
    (h : commonMul b a = commonMul c a) : b = c := by
  have hw : b.2.1 = c.2.1 := add_right_cancel (congrArg (fun p : CommonLoop => p.2.1) h)
  have hx : b.2.2 = c.2.2 := add_right_cancel (congrArg (fun p : CommonLoop => p.2.2) h)
  have hs := congrArg Prod.fst h
  change b.1 + a.1 + codeLoopF b.2.2 a.2.2 = c.1 + a.1 + codeLoopF c.2.2 a.2.2 at hs
  rw [hx] at hs
  exact Prod.ext (add_right_cancel (add_right_cancel hs)) (Prod.ext hw hx)

theorem common_left_division (a c : CommonLoop) : ∃! b, commonMul a b = c := by
  let b : CommonLoop := (c.1-a.1-codeLoopF a.2.2 (c.2.2-a.2.2),
    c.2.1-a.2.1, c.2.2-a.2.2)
  have hb : commonMul a b = c := by
    apply Prod.ext
    · dsimp [commonMul,b]; abel
    · apply Prod.ext <;> dsimp [commonMul,b] <;> abel
  exact ⟨b, hb, fun y hy => common_left_cancel a y b (hy.trans hb.symm)⟩

theorem common_right_division (a c : CommonLoop) : ∃! b, commonMul b a = c := by
  let b : CommonLoop := (c.1-a.1-codeLoopF (c.2.2-a.2.2) a.2.2,
    c.2.1-a.2.1, c.2.2-a.2.2)
  have hb : commonMul b a = c := by
    apply Prod.ext
    · dsimp [commonMul,b]; abel
    · apply Prod.ext <;> dsimp [commonMul,b] <;> abel
  exact ⟨b, hb, fun y hy => common_right_cancel a y b (hy.trans hb.symm)⟩
