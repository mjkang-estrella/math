import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega

namespace Shrinking
open Finset
abbrev Block (n : ℕ) := Finset (Fin n)
abbrev Partition (n : ℕ) := Finset (Block n)

def IsPartition {n : ℕ} (P : Partition n) : Prop :=
  (∀ a ∈ P, a.Nonempty) ∧ (∀ a ∈ P, ∀ b ∈ P, a ≠ b → Disjoint a b) ∧
  P.biUnion id = univ

-- The edge weight between quotient vertices is exactly (16b) of the source.
def edge {n : ℕ} (x : Fin n → Fin n → ℚ) (a b : Block n) : ℚ :=
  if a = b then 0 else ∑ u ∈ a, ∑ v ∈ b, x u v

-- Degree equations (7a) determine vertex weights uniquely.
def weight {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) (a : Block n) : ℚ :=
  (∑ b ∈ P, edge x a b) / 2

def Assignment {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) : Prop :=
  IsPartition P ∧ (∀ u v, x u v = x v u) ∧ (∀ u, x u u = 0) ∧
  (∀ u v, 0 ≤ x u v) ∧
  (∀ a ∈ P, 0 ≤ weight x P a ∧ weight x P a ≤ 1) ∧
  (∀ a ∈ P, ∀ b ∈ P, edge x a b ≤ weight x P a)

def merge {n : ℕ} (P : Partition n) (a b : Block n) : Partition n :=
  insert (a ∪ b) ((P.erase a).erase b)

def S1 {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) (a b : Block n) : Prop :=
  0 < weight x P a ∧ edge x a b = weight x P a ∧
  weight x P a = weight x P b ∧
  ∃ c ∈ P, c ≠ a ∧ c ≠ b ∧ weight x P a ≤ weight x P c

def S2 {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) (a b : Block n) : Prop :=
  max (weight x P a) (weight x P b) < edge x a b

instance {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) (a b : Block n) :
    Decidable (S1 x P a b) := by unfold S1; infer_instance
instance {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) (a b : Block n) :
    Decidable (S2 x P a b) := by unfold S2; infer_instance

-- All eligible pairs, with no prescribed tie-breaking order.
def next {n : ℕ} (x : Fin n → Fin n → ℚ) (P : Partition n) : Finset (Partition n) :=
  ((P.offDiag.filter fun ab => S1 x P ab.1 ab.2 ∨ S2 x P ab.1 ab.2).image
    fun ab => merge P ab.1 ab.2)

inductive Reach {n : ℕ} (x : Fin n → Fin n → ℚ) : Partition n → Partition n → Prop
  | refl (P) : Reach x P P
  | step {P Q R} : Q ∈ next x P → Reach x Q R → Reach x P R

def Isomorphic {n : ℕ} (x : Fin n → Fin n → ℚ) (P Q : Partition n) : Prop :=
  ∃ f : {a // a ∈ P} ≃ {b // b ∈ Q},
    (∀ a, weight x P a = weight x Q (f a)) ∧
    (∀ a b, edge x a b = edge x (f a) (f b))

-- This is the S1S2 member of Conjecture 6.2. Refuting one strategy refutes
-- the assertion quantified over the five strategies.
def SourceS1S2Conjecture : Prop :=
  ∀ n (x : Fin n → Fin n → ℚ) (P Q R : Partition n),
    Assignment x P → Reach x P Q → Reach x P R →
    next x Q = ∅ → next x R = ∅ → Isomorphic x Q R

def matrix : Fin 6 → Fin 6 → ℚ := fun i j =>
  (![![0,1,2,0,0,1], ![1,0,2,0,1,0], ![2,2,0,0,0,0],
     ![0,0,0,0,1,1], ![0,1,0,1,0,2], ![1,0,0,1,2,0]] i j : ℚ) / 2

def P0 : Partition 6 := {{0},{1},{2},{3},{4},{5}}
def P1 : Partition 6 := {{0,2},{1},{3},{4},{5}}
def A : Partition 6 := {{0,1,2},{3},{4},{5}}
def P2 : Partition 6 := {{0,2},{1},{3},{4,5}}
def B : Partition 6 := {{0,1,2},{3},{4,5}}

-- Concrete statements only use kernel reduction, never a native evaluator.
theorem initial_assignment : Assignment matrix P0 := by decide

theorem step01 : P1 ∈ next matrix P0 := by decide
theorem step1A : A ∈ next matrix P1 := by decide
theorem step12 : P2 ∈ next matrix P1 := by decide
theorem step2B : B ∈ next matrix P2 := by decide
theorem terminalA : next matrix A = ∅ := by decide
theorem terminalB : next matrix B = ∅ := by decide

theorem reachA : Reach matrix P0 A := .step step01 (.step step1A (.refl _))
theorem reachB : Reach matrix P0 B := .step step01 (.step step12 (.step step2B (.refl _)))

theorem not_isomorphic : ¬ Isomorphic matrix A B := by
  rintro ⟨f, _, _⟩
  have h := Fintype.card_congr f
  have ha : Fintype.card {a // a ∈ A} = 4 := by decide
  have hb : Fintype.card {b // b ∈ B} = 3 := by decide
  omega

theorem source_refutation : ¬ SourceS1S2Conjecture := by
  intro h
  exact not_isomorphic (h 6 matrix P0 A B initial_assignment reachA reachB terminalA terminalB)

#print axioms source_refutation
end Shrinking
