import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

namespace Smyth1512

open Finset

/-! ## Literal definitions (Smyth §1) -/

/-- `U m n`: compositions of `n` with `m` non-negative parts, i.e. `λ : [m] → ℕ` with `|λ| = n`. -/
def U (m n : ℕ) : Set (Fin m → ℕ) := {f | ∑ i, f i = n}

/-- Non-increasing rearrangement of a composition (its associated partition), as a list. -/
def rearr {m : ℕ} (f : Fin m → ℕ) : List ℕ :=
  (List.ofFn f).insertionSort (fun x y => y ≤ x)

/-- Partial sum of the first `j` entries (entries beyond the length count as `0`). -/
def psum (l : List ℕ) (j : ℕ) : ℕ := (l.take j).sum

/-- Dominance of partitions given as lists: `l₁ ⊵ l₂` iff `|l₁| = |l₂|` and every prefix sum
of `l₂` is at most the corresponding prefix sum of `l₁` (Smyth: `λ ⊴ μ` iff `|λ| = |μ|` and
`∑_{i≤j} λ(i) ≤ ∑_{i≤j} μ(i)` for all `j`). -/
def DomL (l₁ l₂ : List ℕ) : Prop := l₁.sum = l₂.sum ∧ ∀ j : ℕ, psum l₂ j ≤ psum l₁ j

/-- Smyth's dominance on compositions: `f ⊵ g` iff `f_p ⊵ g_p` for the non-increasing
rearrangements. -/
def Dom {m : ℕ} (f g : Fin m → ℕ) : Prop := DomL (rearr f) (rearr g)

/-- Concatenation `λμ` of `λ ∈ U^A` and `μ ∈ U^B`. -/
def concat {A B : ℕ} (f : Fin A → ℕ) (g : Fin B → ℕ) : Fin (A + B) → ℕ := Fin.append f g

/-- Smyth, Conjecture 1.5 (literal): for all `A ≥ B ≥ 0`, `a ≥ b ≥ 0` there is an injection
`γ : U^A_b × U^B_a ↪ U^A_a × U^B_b` with `λ₁μ₁ ⊵ λ₂μ₂` whenever `(λ₂,μ₂) = γ(λ₁,μ₁)`. -/
def Conjecture15 : Prop :=
  ∀ A a B b : ℕ, B ≤ A → b ≤ a →
    ∃ γ : (U A b × U B a) → (U A a × U B b), Function.Injective γ ∧
      ∀ x : U A b × U B a, Dom (concat x.1.1 x.2.1) (concat (γ x).1.1 (γ x).2.1)

/-! ## Certificate data -/

def gens : List (List ℕ) :=
  [[13,12,8,4,2],[13,13,7,3,3],[12,12,8,6,1],[14,12,6,4,3],
   [13,11,7,7,1],[14,11,6,6,2],[15,11,5,5,3],[16,10,5,4,4]]

/-- Boolean dominance test, exact for lists of length 5 (prefixes of length `0..5`). -/
def domB (g l : List ℕ) : Bool :=
  (g.sum == l.sum) && (List.range 6).all (fun j => decide (psum l j ≤ psum g j))

def inDB (l : List ℕ) : Bool := gens.any (fun g => domB g l)

def sortL (l : List ℕ) : List ℕ := l.insertionSort (fun x y => y ≤ x)

/-- Structural enumeration of compositions of `n` into `m` non-negative parts. -/
def comps (m n : ℕ) : List (List ℕ) :=
  Nat.rec (motive := fun _ => ℕ → List (List ℕ))
    (fun n => if n = 0 then [[]] else [])
    (fun _ rec n => (List.range (n + 1)).flatMap
      (fun i => (rec (n - i)).map (List.cons i))) m n

def XL : List (List ℕ × List ℕ) := (comps 3 19) ×ˢ (comps 2 20)
def YL : List (List ℕ × List ℕ) := (comps 3 20) ×ˢ (comps 2 19)
def SL : List (List ℕ × List ℕ) := XL.filter (fun p => inDB (sortL (p.1 ++ p.2)))
def TL : List (List ℕ × List ℕ) := YL.filter (fun p => inDB (sortL (p.1 ++ p.2)))



end Smyth1512
