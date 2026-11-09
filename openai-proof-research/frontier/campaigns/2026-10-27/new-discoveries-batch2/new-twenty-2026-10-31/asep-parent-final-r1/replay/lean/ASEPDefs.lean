import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The asymmetric subtour elimination polytope and the neighborhood-tour conjecture

Source: E. Vercesi, J. Barta, L. M. Gambardella, S. Gualandi, M. Mastrolilli,
*On the integrality gap of small asymmetric traveling salesman problems: a polyhedral and
computational approach*, arXiv:2506.10671 (v1, 12 Jun 2025), formulas (2)–(4), (6), Definition 3
and Conjecture 1 ("For each x vertex, N(x) contains at least one tour"); MathDB 368807.

A point of `P_ASEP^n ⊂ ℝ^{n(n-1)}` is written, as in the source (Section 3), as an `n × n` matrix with
zero diagonal.  Vertices are extreme points; two vertices are adjacent when the segment joining
them is a face (an extreme subset) of the polytope; a tour is (the incidence vector of) a directed
Hamiltonian cycle, i.e. of the successor map of an `n`-cycle.
-/

namespace ASEP

open Finset

/-- Out-flux of `x` across the node set `S`: `∑_{i ∈ S, j ∉ S} x_ij`. -/
def flux {n : ℕ} (x : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, ∑ j ∈ Sᶜ, x i j

/-- `P_ASEP^n` in matrix form: zero diagonal, `x ≥ 0`, in- and out-degree constraints (2), (3) and the
subtour elimination constraints (4) for all `S` with `2 ≤ |S| ≤ n - 2`. -/
def polytope (n : ℕ) : Set (Fin n → Fin n → ℝ) :=
  {x | (∀ i, x i i = 0) ∧ (∀ i j, 0 ≤ x i j) ∧ (∀ j, ∑ i, x i j = 1) ∧ (∀ i, ∑ j, x i j = 1) ∧
    ∀ S : Finset (Fin n), 2 ≤ S.card → S.card ≤ n - 2 → 1 ≤ flux x S}

/-- The incidence matrix of the arcs `i → σ i`. -/
def tourMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → ℝ :=
  fun i j => if σ i = j then 1 else 0

/-- `t` is a tour: the arc set of a directed Hamiltonian cycle, i.e. of an `n`-cycle `σ`. -/
def IsTour (n : ℕ) (t : Fin n → Fin n → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ σ.support = Finset.univ ∧ t = tourMatrix σ

/-- Vertices of `P_ASEP^n`. -/
def IsVertex (n : ℕ) (x : Fin n → Fin n → ℝ) : Prop := x ∈ Set.extremePoints ℝ (polytope n)

/-- Adjacency in the vertex graph (Definition 3): distinct vertices whose segment is a face. -/
def Adjacent (n : ℕ) (x y : Fin n → Fin n → ℝ) : Prop :=
  IsVertex n x ∧ IsVertex n y ∧ x ≠ y ∧ IsExtreme ℝ (polytope n) (segment ℝ x y)

/-- Conjecture 1 of the source, for every `n ≥ 4` (the source studies `n ≥ 4`). -/
def NeighborhoodTourConjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ x, IsVertex n x → ∃ t, IsTour n t ∧ Adjacent n x t

lemma flux_add {n : ℕ} (x y : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    flux (x + y) S = flux x S + flux y S := by
  simp only [flux, Pi.add_apply, Finset.sum_add_distrib]

lemma flux_smul {n : ℕ} (a : ℝ) (x : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    flux (a • x) S = a * flux x S := by
  simp only [flux, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma flux_sub {n : ℕ} (x y : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    flux (x - y) S = flux x S - flux y S := by
  simp only [flux, Pi.sub_apply, Finset.sum_sub_distrib]

end ASEP
