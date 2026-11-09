import SSA5.Data

/-!
# Kernel-checked finite certificate facts

All statements quantify over the 1024 words `[a, b, c, d, e]` of length five and are
checked by kernel evaluation (`decide +kernel`); no native code evaluation is used.
-/

namespace SSA

/-- Membership of a length-five letter list in the improved generating set. -/
def inS (l : List Base) : Bool := sTree.get l

/-- Is a letter `T` or `C`? -/
def isTCb (b : Base) : Bool := b == .T || b == .C

/-- TC-dominance of a length-five letter list (at least three `T`/`C`). -/
def inTC (l : List Base) : Bool := decide (3 ≤ l.countP isTCb)

/-- Lower vector entry, zero outside `S`. -/
def vS (l : List Base) : ℕ := if inS l then vTree.get l else 0

/-- Upper vector entry, zero outside the TC-dominant set. -/
def uT (l : List Base) : ℕ := if inTC l then uTree.get l else 0

/-- The improved set contains no reverse-complement pair and meets every pair. -/
theorem check_gen : ∀ a b c d e : Base,
    (inS [a, b, c, d, e] = true → inS [e.comp, d.comp, c.comp, b.comp, a.comp] = false) ∧
    (inS [a, b, c, d, e] = true ∨ inS [e.comp, d.comp, c.comp, b.comp, a.comp] = true) := by
  decide +kernel

/-- Collatz–Wielandt lower certificate: `λ v ≤ A v` on `S`, with `λ = lamNum / lamDen`. -/
theorem check_lower : ∀ a b c d e : Base, inS [a, b, c, d, e] = true →
    lamNum * vS [a, b, c, d, e] ≤
      lamDen * (vS [b, c, d, e, .A] + vS [b, c, d, e, .C] + vS [b, c, d, e, .G] +
        vS [b, c, d, e, .T]) := by
  decide +kernel

/-- Collatz–Wielandt upper certificate: `B u ≤ μ u` on the TC-dominant set,
with `μ = muNum / muDen`. -/
theorem check_upper : ∀ a b c d e : Base, inTC [a, b, c, d, e] = true →
    muDen * (uT [b, c, d, e, .A] + uT [b, c, d, e, .C] + uT [b, c, d, e, .G] +
        uT [b, c, d, e, .T]) ≤ muNum * uT [a, b, c, d, e] := by
  decide +kernel

/-- Bounds on the certificate vectors. -/
theorem check_bounds : ∀ a b c d e : Base,
    vS [a, b, c, d, e] ≤ vMax ∧ uT [a, b, c, d, e] ≤ uMax ∧
      (inTC [a, b, c, d, e] = true → uMin ≤ uT [a, b, c, d, e]) := by
  decide +kernel

/-- A word of `S` with positive lower-vector entry. -/
theorem check_witness : inS [.T, .T, .A, .C, .A] = true ∧ 0 < vS [.T, .T, .A, .C, .A] := by
  decide +kernel

/-- The numerical constants: `0 < μ < λ`, `uMin > 0`. -/
theorem check_consts : muNum * lamDen < lamNum * muDen ∧ 0 < muNum ∧ 0 < muDen ∧
    0 < lamDen ∧ 0 < uMin ∧ 0 < vMax := by
  decide +kernel

end SSA
