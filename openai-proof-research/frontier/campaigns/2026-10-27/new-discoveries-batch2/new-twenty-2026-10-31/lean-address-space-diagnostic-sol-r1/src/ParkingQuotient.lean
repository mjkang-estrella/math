module
public import ParkingBase
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public noncomputable section
namespace Parking
variable {K : Type*} [CommRing K]
def DeformedIdeal {n : ℕ} (theta : Fin n → Poly n K) : Ideal (Poly n K) :=
  Ideal.span (Set.range (fun i => theta i - MvPolynomial.X i))

abbrev AlgebraicParking {n : ℕ} (theta : Fin n → Poly n K) :=
  Poly n K ⧸ DeformedIdeal theta


#print axioms DeformedIdeal
#print axioms AlgebraicParking
end Parking
