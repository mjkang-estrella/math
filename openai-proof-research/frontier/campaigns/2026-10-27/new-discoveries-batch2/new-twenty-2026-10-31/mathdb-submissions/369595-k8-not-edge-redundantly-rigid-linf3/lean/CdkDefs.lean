import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Definitions of Cruickshank, Dewar and Kitson, *Algebraic connectivity in normed spaces*

arXiv:2508.00134v1, §2.2 (support functionals, smoothness, rigid motions),
§2.3 (frameworks, trivial infinitesimal flexes, rigidity matrix, infinitesimal
rigidity) and §5 (edge-redundant rigidity, Conjecture 5.4).

The definitions are stated for an arbitrary real normed space `E` with a family
of vectors `b : Fin d → E` playing the role of the standard basis
`b₁, …, b_d` of `ℝ^d` (the columns of the rigidity matrix are indexed by
`V × [d]`, and a kernel vector `u ∈ ℝ^{V × [d]}` is identified with the
displacement `v ↦ ∑ᵢ u (v, i) • bᵢ`).  The space `ℓ∞^d` is `Fin d → ℝ` with
Mathlib's sup norm `‖x‖ = maxᵢ |xᵢ|`, and `bᵢ = Pi.single i 1`.
-/

namespace CDK

open Matrix

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dual norm of a linear functional, `‖φ‖* = sup_{‖x‖ = 1} |φ x|` (§2.2). -/
noncomputable def dualNorm (φ : E →ₗ[ℝ] ℝ) : ℝ :=
  sSup ((fun x => |φ x|) '' Metric.sphere (0 : E) 1)

/-- `φ` is a support functional for `x₀`: `φ x₀ = 1` and `‖φ‖* = 1` (§2.2). -/
def IsSupportFunctional (x₀ : E) (φ : E →ₗ[ℝ] ℝ) : Prop :=
  φ x₀ = 1 ∧ dualNorm φ = 1

/-- The norm is smooth at `x₀` if `x₀` has exactly one support functional (§2.2). -/
def IsSmoothAt (x₀ : E) : Prop :=
  ∃! φ : E →ₗ[ℝ] ℝ, IsSupportFunctional x₀ φ

open Classical in
/-- The unique support functional `φ_{x₀}` at a smooth point (any support
functional if there are several, `0` if there is none; only used at smooth
points). -/
noncomputable def supportFunctional (x₀ : E) : E →ₗ[ℝ] ℝ :=
  if h : ∃ φ, IsSupportFunctional x₀ φ then h.choose else 0

/-- A rigid motion of `E` (§2.2): continuous paths `αₓ : (-1, 1) → E` with
`αₓ(0) = x`, differentiable at `0`, and `‖αₓ(t) - α_y(t)‖ = ‖x - y‖` for all
`t ∈ (-1, 1)`.  Values outside `(-1, 1)` are irrelevant. -/
structure RigidMotion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  α : E → ℝ → E
  continuousOn : ∀ x, ContinuousOn (α x) (Set.Ioo (-1) 1)
  zero : ∀ x, α x 0 = x
  differentiableAt : ∀ x, DifferentiableAt ℝ (α x) 0
  isometric : ∀ x y, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖α x t - α y t‖ = ‖x - y‖

/-- `η` is an infinitesimal rigid motion: `η x = αₓ'(0)` for a rigid motion `α`. -/
def IsInfRigidMotion (η : E → E) : Prop :=
  ∃ m : RigidMotion E, ∀ x, η x = deriv (m.α x) 0

variable {V : Type*}

/-- The normalised vector `(p v - p w) / ‖p v - p w‖`. -/
noncomputable def normalised (p : V → E) (v w : V) : E :=
  ‖p v - p w‖⁻¹ • (p v - p w)

/-- `(G, p)` is a framework in `E` (§2.3): for each edge `vw`, `p v ≠ p w` and the
norm is smooth at the normalised vector. -/
def IsFramework (G : SimpleGraph V) (p : V → E) : Prop :=
  ∀ v w, G.Adj v w → p v ≠ p w ∧ IsSmoothAt (normalised p v w)

/-- Well-positioned placements: the set `W(G, E)` of `p` for which `(G, p)` is a
framework. -/
def W (G : SimpleGraph V) : Set (V → E) := {p | IsFramework G p}

/-- `u` is a trivial infinitesimal flex of `(G, p)`: `u v = η (p v)` for an
infinitesimal rigid motion `η` (§2.3). -/
def IsTrivialFlex (p : V → E) (u : V → E) : Prop :=
  ∃ η, IsInfRigidMotion η ∧ ∀ v, u v = η (p v)

open Classical in
/-- The rigidity matrix `R(G, p)` (§2.3): rows indexed by edges, columns by
`V × [d]`; the `(e, (v, i))` entry is `φ_{v,w}(bᵢ)` if `e = vw`, else `0`, where
`φ_{v,w}` is the support functional at the normalised vector of `p v - p w`. -/
noncomputable def rigidityMatrix {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) :
    Matrix G.edgeSet (V × Fin d) ℝ :=
  fun e vi =>
    if h : vi.1 ∈ (e : Sym2 V) then supportFunctional (normalised p vi.1 (Sym2.Mem.other h)) (b vi.2)
    else 0

/-- The displacement field of a vector `u ∈ ℝ^{V × [d]}`. -/
def displacement {d : ℕ} (b : Fin d → E) (u : V × Fin d → ℝ) : V → E :=
  fun v => ∑ i, u (v, i) • b i

variable [Fintype V]

/-- Infinitesimal rigidity (§2.3): `(G, p)` is a framework and the kernel of the
rigidity matrix consists of trivial infinitesimal flexes only. -/
def IsInfRigid {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) : Prop :=
  IsFramework G p ∧
    ∀ u : V × Fin d → ℝ, rigidityMatrix b G p *ᵥ u = 0 → IsTrivialFlex p (displacement b u)

/-- An edge-redundantly rigid framework (§5): infinitesimally rigid, and the
framework obtained by deleting any single edge is infinitesimally rigid. -/
def IsEdgeRedundantlyRigidFramework {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) :
    Prop :=
  IsInfRigid b G p ∧ ∀ e ∈ G.edgeSet, IsInfRigid b (G.deleteEdges {e}) p

/-- `G` is edge-redundantly rigid in `E` (§5): some framework `(G, p)` in `E` is
edge-redundantly rigid. -/
def EdgeRedundantlyRigidIn {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) : Prop :=
  ∃ p : V → E, IsEdgeRedundantlyRigidFramework b G p

end General

/-- The standard basis of `ℝ^d`. -/
noncomputable def stdBasis (d : ℕ) : Fin d → (Fin d → ℝ) := fun i => Pi.single i 1

/-- `G` is edge-redundantly rigid in `ℓ∞^d = (ℝ^d, ‖·‖∞)`. -/
def EdgeRedundantlyRigid {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  EdgeRedundantlyRigidIn (E := Fin d → ℝ) (stdBasis d) G

/-- The complete graph `Kₙ`. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) := ⊤

/-- Conjecture 5.4 of Cruickshank–Dewar–Kitson: for every `d ≥ 2` and every
`n ≥ 2d + 2`, the complete graph `Kₙ` is edge-redundantly rigid in `ℓ∞^d`. -/
def Conjecture : Prop :=
  ∀ d n : ℕ, 2 ≤ d → 2 * d + 2 ≤ n → EdgeRedundantlyRigid (completeGraph n) d

end CDK
