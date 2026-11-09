import Range
namespace Hetyei347230
def a : Bool := false
def b : Bool := true

/-- 20-term symmetric degree-5 kernel element (outputs/hetyei-certificates-v2.json). -/
def uList : FSum :=
  [([a,a,a,b,a], 1), ([a,a,a,b,b], 1), ([a,a,b,a,a], -2), ([a,a,b,b,a], -1), ([a,a,b,b,b], 1),
   ([a,b,a,a,a], 1), ([a,b,a,a,b], 1), ([a,b,b,a,a], -1), ([a,b,b,a,b], 1), ([a,b,b,b,a], -2),
   ([b,a,a,a,b], -2), ([b,a,a,b,a], 1), ([b,a,a,b,b], -1), ([b,a,b,b,a], 1), ([b,a,b,b,b], 1),
   ([b,b,a,a,a], 1), ([b,b,a,a,b], -1), ([b,b,a,b,b], -2), ([b,b,b,a,a], 1), ([b,b,b,a,b], 1)]

noncomputable def uCert : ABPoly := toPoly uList

def coeffL (l : FSum) (w : Word) : ℤ := ((l.filter fun p => p.1 == w).map Prod.snd).sum

/-- I2 applied to a formal sum, computably. -/
def I2L (l : FSum) : FSum := l.flatMap fun p => (I2w p.1).map fun q => (q.1, p.2 * q.2)

def allWords : ℕ → List Word :=
  Nat.rec [[]] (fun _ prev => prev.flatMap fun w => [false :: w, true :: w])
@[simp] theorem allWords_zero : allWords 0 = [[]] := rfl
@[simp] theorem allWords_succ (n : ℕ) : allWords (n + 1) =
    (allWords n).flatMap (fun w => [false :: w, true :: w]) := rfl
end Hetyei347230
