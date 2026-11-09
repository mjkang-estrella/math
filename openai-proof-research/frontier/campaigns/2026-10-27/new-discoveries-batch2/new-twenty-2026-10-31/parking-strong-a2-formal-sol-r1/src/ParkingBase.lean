module
public import Mathlib.Algebra.MvPolynomial.Eval

/-! General coordinate-ring portion of the source statement.
Coefficient-parametric model; complex specialization not imported here.
No reflection-group classification, local multiplicity or parking action is asserted here.
These missing bindings prevent this module from being a literal Strong endpoint. -/
public noncomputable section
namespace Parking
abbrev Coord (n : ℕ) (K : Type*) := Fin n → K
abbrev Poly (n : ℕ) (K : Type*) [CommRing K] := MvPolynomial (Fin n) K
variable {K : Type*} [CommRing K]

def Homogeneous {n : ℕ} (d : ℕ) (p : Poly n K) : Prop :=
  ∀ a ∈ p.support, a.sum (fun _ m => m) = d

def CommonZero {n : ℕ} (theta : Fin n → Poly n K) : Set (Coord n K) :=
  {v | ∀ i, MvPolynomial.eval v (theta i) = 0}

def FixedLocus {n : ℕ} (theta : Fin n → Poly n K) : Set (Coord n K) :=
  {v | ∀ i, MvPolynomial.eval v (theta i) = v i}

/-- The zero-locus condition is over the whole affine space (specialize K to ℂ for the source). -/
def ZeroLocusHsop {n : ℕ} (d : ℕ) (theta : Fin n → Poly n K) : Prop :=
  (∀ i, Homogeneous d (theta i)) ∧ CommonZero theta = {0}

/-- Exact point-count clause, separated from the still unpaid local-length clause. -/
def DistinctPointCount {n : ℕ} (theta : Fin n → Poly n K) (N : ℕ) : Prop :=
  Nonempty ({v // v ∈ FixedLocus theta} ≃ Fin N)

/-- Pure logical elimination of a universal conjunction. The two supplied predicates
are not definitions of either parking space, and this is not a literal endpoint. -/
theorem refute_conjunction {ι : Sort*} (A B C : ι → Prop)
    (i : ι) (hi : ¬ A i) : ¬ (∀ j, A j ∧ B j ∧ C j) := by
  intro h
  exact hi (h i).1

#print axioms Homogeneous
#print axioms CommonZero
#print axioms FixedLocus
#print axioms ZeroLocusHsop
#print axioms DistinctPointCount
#print axioms refute_conjunction
end Parking
