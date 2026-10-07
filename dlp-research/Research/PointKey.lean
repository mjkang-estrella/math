import Research.OrbitArithmetic

/-! Coordinate keys for ordered lookup, separate from the public tape encoding.
The generic contract supplies equality reflection on the orbit, not efficiency
or admissibility of an arbitrary key implementation. Concrete keys must be
reviewed for hidden scalar lookup. No comparison or construction cost is proved.
-/
namespace Research.PointKeys

open OrbitRefinement

structure PointKey (P : CyclicProblem) where
  key : P.Point → Nat
  reflects_orbit : ∀ a b,
    key (orbit P a) = key (orbit P b) ↔ orbit P a = orbit P b

/-- Ordinary tagged coordinate packing, defined even off the curve. There is
no orbit enumeration, inverse table, or secret-scalar argument in this code. -/
def rawKey : SmallCurve.RawPoint → Nat
  | none => 0
  | some (x, y) => 1 + 5 * x.val + y.val

theorem rawKey_lt (p : SmallCurve.RawPoint) : rawKey p < 26 := by
  cases p with
  | none => decide
  | some p =>
    obtain ⟨x, y⟩ := p
    simp only [rawKey]
    have hx := x.isLt
    have hy := y.isLt
    omega

theorem rawKey_injective (p q : SmallCurve.RawPoint)
    (h : rawKey p = rawKey q) : p = q := by
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q => simp only [rawKey] at h; omega
  | some p =>
    cases q with
    | none => simp only [rawKey] at h; omega
    | some q =>
      obtain ⟨x, y⟩ := p
      obtain ⟨u, v⟩ := q
      have hx := x.isLt
      have hy := y.isLt
      have hu := u.isLt
      have hv := v.isLt
      simp only [rawKey] at h
      have heqx : x = u := Fin.ext (by omega)
      have heqy : y = v := Fin.ext (by omega)
      simp [heqx, heqy]

def coordinateKey (p : SmallCurve.Point) : Nat := rawKey p.val

theorem coordinateKey_lt (p : SmallCurve.Point) : coordinateKey p < 26 :=
  rawKey_lt p.val

theorem coordinateKey_eq_iff (p q : SmallCurve.Point) :
    coordinateKey p = coordinateKey q ↔ p = q := by
  constructor
  · intro h
    exact Subtype.ext (rawKey_injective p.val q.val h)
  · intro h
    exact congrArg coordinateKey h

/-- This refinement uses only the coordinate arithmetic in rawKey. -/
def smallCurve : PointKey SmallCurve.problem where
  key := coordinateKey
  reflects_orbit := fun a b =>
    coordinateKey_eq_iff (orbit SmallCurve.problem a) (orbit SmallCurve.problem b)

theorem smallCurve_key_reflects (a b : Nat) :
    smallCurve.key (orbit SmallCurve.problem a) =
      smallCurve.key (orbit SmallCurve.problem b) ↔
    a % 7 = b % 7 := by
  rw [smallCurve.reflects_orbit, orbit_eq_iff_mod]
  rfl

/-- Packed keys occupy at most five bits. This is a value bound, not a memory
layout, serialization implementation, or bit-operation count. -/
theorem coordinateKey_fits (p : SmallCurve.Point) : coordinateKey p < 2 ^ 5 := by
  have h := coordinateKey_lt p
  omega

end Research.PointKeys
