import CrownVAlg

/-!
# CrownV rank-one parametrization map (r19)

An actual rank-one parametrizing ring homomorphism from the existing binomial
edge polynomial ring `CrownV.PolyRing n K = MvPolynomial (V n × Bool) K` to the
free polynomial codomain `CrownV.RankOneCodomain n K = MvPolynomial (Bool ⊕ V n) K`,
which carries two independent factor variables (indexed by `Bool`) and one
independent factor variable per crown vertex `v : V n`.

The homomorphism `CrownV.rankOneHom` fixes every coefficient (`MvPolynomial.C`)
and sends each variable `X (v, b)` to the product `factVar b * vertVar v` of its
Bool factor and its vertex factor.  Consequences proved here: the action on
constants and variables, and the annihilation `rankOneHom (minor u v) = 0` of
every existing binomial minor `CrownV.minor u v = xx u * yy v - xx v * yy u`
for ALL pairs `u v : V n`.  Consequently the all-pair minor ideal
`CrownV.allPairMinorIdeal` (the span of `{minor u v | u v : V n}`, precisely
defined below) is contained in `RingHom.ker rankOneHom`.

This module claims an inclusion only.  It does NOT claim equality of the
all-pair minor ideal with the kernel, does NOT claim primality, and does NOT
identify `rankOneHom` with evaluation on any actual variety `Pc(T)`; the
definitions `Pc`, `minor` and `PolyRing` are used, never redefined.
-/

namespace CrownV

section RankOneMap

variable {n : ℕ} {K : Type*} [CommRing K]

/-- The free rank-one codomain: two independent factor variables indexed by
`Bool` and one independent factor variable per `v : V n`. -/
abbrev RankOneCodomain (n : ℕ) (K : Type*) [CommRing K] :=
  MvPolynomial (Bool ⊕ V n) K

/-- The factor variable attached to the `Bool` label `b`. -/
noncomputable def factVar (b : Bool) : RankOneCodomain n K := MvPolynomial.X (Sum.inl b)

/-- The factor variable attached to the vertex `v`. -/
noncomputable def vertVar (v : V n) : RankOneCodomain n K := MvPolynomial.X (Sum.inr v)

/-- The rank-one variable assignment: the variable `(v, b)` of `PolyRing n K`
maps to the product of the Bool factor `b` and the vertex factor `v`. -/
noncomputable def rankOneFun (q : V n × Bool) : RankOneCodomain n K :=
  factVar q.2 * vertVar q.1

/-- The actual rank-one parametrizing ring homomorphism from the existing
`PolyRing n K`: every coefficient `MvPolynomial.C c` is fixed and every variable
`X (v, b)` is sent to `factVar b * vertVar v`.  Built from the variable
evaluation constructor `MvPolynomial.eval₂Hom` with the coefficient ring hom
`MvPolynomial.C` (not `MvPolynomial.map`, which changes coefficients). -/
noncomputable def rankOneHom : PolyRing n K →+* RankOneCodomain n K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* RankOneCodomain n K) rankOneFun

/-- Constants are fixed: `rankOneHom (C c) = C c`. -/
theorem rankOneHom_C (c : K) :
    rankOneHom (MvPolynomial.C c : PolyRing n K)
      = (MvPolynomial.C c : RankOneCodomain n K) := by
  unfold rankOneHom
  rw [MvPolynomial.eval₂Hom_C]

/-- Variable action: `rankOneHom (X (v, b)) = factVar b * vertVar v`. -/
theorem rankOneHom_X (v : V n) (b : Bool) :
    rankOneHom (MvPolynomial.X (v, b) : PolyRing n K)
      = factVar (n := n) b * vertVar (n := n) v := by
  unfold rankOneHom
  rw [MvPolynomial.eval₂Hom_X']
  rfl

/-- Action on `xx v = X (v, true)`. -/
theorem rankOneHom_xx (v : V n) :
    rankOneHom (xx v : PolyRing n K) = factVar true * vertVar v :=
  rankOneHom_X v true

/-- Action on `yy v = X (v, false)`. -/
theorem rankOneHom_yy (v : V n) :
    rankOneHom (yy v : PolyRing n K) = factVar false * vertVar v :=
  rankOneHom_X v false

/-- Mixed product action. -/
theorem rankOneHom_xy (a b : V n) :
    rankOneHom (xx a * yy b : PolyRing n K)
      = (factVar true * vertVar a) * (factVar false * vertVar b) := by
  rw [map_mul, rankOneHom_xx, rankOneHom_yy]

/-- The actual minor annihilation: every binomial edge minor
`minor u v = xx u * yy v - xx v * yy u` maps to `0` under `rankOneHom`,
for ALL pairs `u v : V n` (not only crown edges). -/
theorem rankOneHom_minor (u v : V n) :
    rankOneHom (minor u v) = (0 : RankOneCodomain n K) := by
  have h1 : rankOneHom (xx u * yy v : PolyRing n K)
      = (factVar true * vertVar u) * (factVar false * vertVar v) :=
    rankOneHom_xy u v
  have h2 : rankOneHom (xx v * yy u : PolyRing n K)
      = (factVar true * vertVar v) * (factVar false * vertVar u) :=
    rankOneHom_xy v u
  show rankOneHom (xx u * yy v - xx v * yy u) = (0 : RankOneCodomain n K)
  rw [map_sub, h1, h2]
  ring

/-- The all-pair minor set: every `minor u v` over ALL pairs `u v : V n`. -/
def allPairMinorSet (n : ℕ) : Set (PolyRing n K) := {g | ∃ u v : V n, g = minor u v}

/-- The all-pair minor ideal: the span of `allPairMinorSet n` in `PolyRing n K`. -/
noncomputable def allPairMinorIdeal (n : ℕ) (K : Type*) [CommRing K] :
    Ideal (PolyRing n K) := Ideal.span (allPairMinorSet (n := n) (K := K))

theorem minor_mem_allPairMinorIdeal (u v : V n) :
    (minor u v : PolyRing n K) ∈ allPairMinorIdeal (n := n) (K := K) :=
  Submodule.mem_span_of_mem ⟨u, v, rfl⟩

/-- The kernel inclusion: the all-pair minor ideal is contained in the kernel of
the rank-one homomorphism.  This is an inclusion only; no reverse equality and
no primality are claimed here. -/
theorem allPairMinorIdeal_le_ker (n : ℕ) (K : Type*) [CommRing K] :
    allPairMinorIdeal (n := n) (K := K) ≤ RingHom.ker
      (rankOneHom (n := n) (K := K)) := by
  refine Ideal.span_le.2 ?_
  rintro g ⟨u, v, rfl⟩
  exact RingHom.mem_ker.2 (rankOneHom_minor u v)

end RankOneMap

end CrownV
