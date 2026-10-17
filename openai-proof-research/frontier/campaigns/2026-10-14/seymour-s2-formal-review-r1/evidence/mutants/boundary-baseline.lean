/- Copyright 2026 Myeongjin Kang. Licensed under MIT.
Supporting finite-set and integer lemmas for the S2 proof. Not the graph theorem.
-/
import Mathlib

open scoped BigOperators
namespace SeymourSupport

/-- The exact boundary identity yields the weak deficit. The identity and
indicator bounds are explicit inputs, not graph facts proved here. -/
theorem boundary_weak (dD dH a q b : ℤ)
    (hId : dD = dH + q + b - a) (hD : dD ≤ -1)
    (ha : a ≤ 1) (hq : 0 ≤ q) (hb : 0 ≤ b) : dH ≤ 0 := by
  omega

/-- Avoiding the successor ensures q ≥ a, giving strictness. -/
theorem boundary_strict (dD dH a q b : ℤ)
    (hId : dD = dH + q + b - a) (hD : dD ≤ -1)
    (haq : a ≤ q) (hb : 0 ≤ b) : dH ≤ -1 := by
  omega

end SeymourSupport
