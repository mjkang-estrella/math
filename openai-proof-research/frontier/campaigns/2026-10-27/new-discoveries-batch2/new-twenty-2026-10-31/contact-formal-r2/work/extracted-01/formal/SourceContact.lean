import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.Eval

namespace ContactPilot

/-- Literal local zero-set comparison in the bidisk. `q` must be the
reflection of the reduced stable denominator, up to a nonzero local unit.
Certification of that connection is a separate mandatory theorem. -/
def HasZeroSetContact (q : ℂ → ℂ → ℂ) (τ₁ τ₂ : ℂ) (K : ℕ) : Prop :=
  ‖τ₁‖ = 1 ∧ ‖τ₂‖ = 1 ∧ q τ₁ τ₂ = 0 ∧
  ∃ δ ρ c C : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < c ∧ 0 < C ∧
    ∀ z : ℂ, ‖z‖ = 1 → 0 < ‖z - τ₁‖ → ‖z - τ₁‖ < δ →
      (∀ v : ℂ, ‖v‖ < 1 → ‖v - τ₂‖ < ρ → q z v = 0 →
        c * ‖z - τ₁‖ ^ K ≤ 1 - ‖v‖) ∧
      (∃ v : ℂ, ‖v‖ < 1 ∧ ‖v - τ₂‖ < ρ ∧ q z v = 0 ∧
        1 - ‖v‖ ≤ C * ‖z - τ₁‖ ^ K)

/-- Upper-half-plane version for the reduced denominator of beta(f(-1/x,w)).
The two clauses express the lower bound for every local zero and an upper
bound attained by some local zero, avoiding an empty-set infimum. -/
def HasHalfPlaneContact (r : ℂ → ℂ → ℂ) (K : ℕ) : Prop :=
  r 0 0 = 0 ∧
  ∃ δ ρ c C : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, 0 < |x| → |x| < δ →
      (∀ w : ℂ, ‖w‖ < ρ → w.im < 0 → r x w = 0 →
        c * |x| ^ K ≤ |w.im|) ∧
      (∃ w : ℂ, ‖w‖ < ρ ∧ w.im < 0 ∧ r x w = 0 ∧
        |w.im| ≤ C * |x| ^ K)

end ContactPilot

namespace ContactPilot
noncomputable section
abbrev Poly₂ := MvPolynomial (Fin 2) ℂ

def eval₂ (p : Poly₂) (z w : ℂ) : ℂ :=
  MvPolynomial.eval (fun j => if j = 0 then z else w) p

def beta (v : ℂ) : ℂ := (1 + Complex.I*v)/(1 - Complex.I*v)
def betaInv (v : ℂ) : ℂ := Complex.I*(1-v)/(1+v)

/-- `isZ = false` means color w. -/
def resolventMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (isZ : Fin n → Bool)
    (z w : ℂ) : Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact (Matrix.of (fun i j => if G.Adj i j then (1:ℂ) else 0)) -
    Matrix.diagonal (fun i => if isZ i then z else w)

def graphFunction {n : ℕ} (G : SimpleGraph (Fin n)) (isZ : Fin n → Bool)
    (i : Fin n) (z w : ℂ) : ℂ := (resolventMatrix G isZ z w)⁻¹ i i

/-- Reflection in the declared bidegree; the certificate also checks the
bidegree bounds, so truncated exponents cannot silently redefine reflection. -/
def reflect (p : Poly₂) (m k : ℕ) : ℂ → ℂ → ℂ := fun z w =>
  p.support.sum (fun d => star (p.coeff d) * z^(m-d 0) * w^(k-d 1))

structure ReducedCertificate (f : ℂ → ℂ → ℂ) where
  numerator : Poly₂
  denominator : Poly₂
  denominator_ne : denominator ≠ 0
  reduced : ∀ d : Poly₂, d ∣ numerator → d ∣ denominator → IsUnit d
  stable : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → eval₂ denominator z w ≠ 0
  represents : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
    beta (f (betaInv z) (betaInv w)) = eval₂ numerator z w / eval₂ denominator z w
  degreeZ : ℕ
  degreeW : ℕ
  bounds : ∀ d ∈ denominator.support, d 0 ≤ degreeZ ∧ d 1 ≤ degreeW
  phase : ℂ
  phase_norm : ‖phase‖ = 1
  reflection : ∀ z w : ℂ, eval₂ numerator z w = phase * reflect denominator degreeZ degreeW z w

/-- Walk formulation includes precisely the reachable nonempty nearest-w case;
no artificial distance is assigned to an empty set of reachable w vertices. -/
def NearestWDistance {n : ℕ} (G : SimpleGraph (Fin n)) (isZ : Fin n → Bool)
    (i : Fin n) (d : ℕ) : Prop :=
  (∃ j : Fin n, isZ j = false ∧ ∃ p : G.Walk i j, p.length = d) ∧
  ∀ j : Fin n, isZ j = false → ∀ p : G.Walk i j, d ≤ p.length

/-- Universal source assertion on every finite simple colored graph and every
root, whenever nearest-w distance and local contact are defined. No branch
matching, equal-branch assumption, or candidate polynomial occurs here. -/
def SourceConjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (isZ : Fin n → Bool) (i : Fin n)
    (cert : ReducedCertificate (graphFunction G isZ i)) (d K : ℕ),
    NearestWDistance G isZ i d → 0 < K → Even K →
    HasZeroSetContact (eval₂ cert.numerator) (-1) 1 K → K = 2*d
end
end ContactPilot
