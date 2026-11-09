import CrownVAlg

/-!
# Crown variety: the coordinate-killing endomorphism

`CrownV.coordKill` is the ring endomorphism of `PolyRing n K` killing the
coordinate variables `X (v, true)` and `X (v, false)` for `v ∈ T`, fixing all
other variables, and fixing every coefficient.  Its action on `X` and `C` and
the resulting annihilation of `CrownV.xx` and `CrownV.yy` over `T` are proved
below.  This module does NOT claim kernel equality or ideal primality; those
are subsequent obligations handled elsewhere.
-/

namespace CrownV

variable {n : Nat} {K : Type*} [CommRing K] (T : Finset (V n))

/-- The ring endomorphism of `PolyRing n K` fixing every coefficient `C c`,
sending `X (v, b)` to `0` when `v ∈ T` and to `X (v, b)` otherwise.
Built from the variable-evaluation constructor `MvPolynomial.eval₂Hom`
(not the coefficient mapping `MvPolynomial.map`). -/
noncomputable def coordKill : PolyRing n K →+* PolyRing n K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* PolyRing n K)
    (fun q : V n × Bool => if q.1 ∈ T then (0 : PolyRing n K) else MvPolynomial.X q)

theorem coordKill_C (c : K) :
    coordKill T (MvPolynomial.C c) = MvPolynomial.C c := by
  unfold coordKill
  rw [MvPolynomial.eval₂Hom_C]

theorem coordKill_X (q : V n × Bool) :
    coordKill T (MvPolynomial.X q : PolyRing n K)
      = if q.1 ∈ T then (0 : PolyRing n K) else MvPolynomial.X q := by
  unfold coordKill
  rw [MvPolynomial.eval₂Hom_X']

theorem coordKill_X_of_notMem {q : V n × Bool} (hq : q.1 ∉ T) :
    coordKill T (MvPolynomial.X q : PolyRing n K) = MvPolynomial.X q := by
  rw [coordKill_X, ite_eq_right hq]

theorem coordKill_xx (v : V n) :
    coordKill T (xx v : PolyRing n K)
      = if v ∈ T then (0 : PolyRing n K) else xx v := by
  rw [show (xx v : PolyRing n K) = (MvPolynomial.X (v, true) : PolyRing n K) from rfl,
    coordKill_X]

theorem coordKill_yy (v : V n) :
    coordKill T (yy v : PolyRing n K)
      = if v ∈ T then (0 : PolyRing n K) else yy v := by
  rw [show (yy v : PolyRing n K) = (MvPolynomial.X (v, false) : PolyRing n K) from rfl,
    coordKill_X]

theorem coordKill_xx_eq_zero {v : V n} (hv : v ∈ T) :
    coordKill T (xx v : PolyRing n K) = (0 : PolyRing n K) := by
  rw [coordKill_xx, ite_eq_left hv]

theorem coordKill_yy_eq_zero {v : V n} (hv : v ∈ T) :
    coordKill T (yy v : PolyRing n K) = (0 : PolyRing n K) := by
  rw [coordKill_yy, ite_eq_left hv]

end CrownV
