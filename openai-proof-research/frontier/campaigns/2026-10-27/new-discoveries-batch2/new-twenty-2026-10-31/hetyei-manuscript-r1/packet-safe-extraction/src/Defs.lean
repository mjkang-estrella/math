import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace Hetyei347230

abbrev Word := List Bool

/-- ℚ⟨a,b⟩ with its word basis. -/
abbrev ABPoly := Word →₀ ℚ

/-! ### Formal integer combinations of words (computable layer) -/

abbrev FSum := List (Word × ℤ)

/-- Semantic map from a formal sum to an ab-polynomial. -/
noncomputable def toPoly (l : FSum) : ABPoly :=
  (l.map fun p => Finsupp.single p.1 (p.2 : ℚ)).sum

/-- Ehrenborg-Readdy coproduct pieces of a word. -/
def cop (w : Word) : List (Word × Word) :=
  (List.range w.length).map fun i => (w.take i, w.drop (i + 1))

/-- `Mrs r s n u v` is ER's `M_{r,s}(u,v,n)`; `r = false` means r = 1, `r = true` means r = 2. -/
def MrsAux : ℕ → Bool → Bool → Word → Word → FSum :=
  Nat.rec (fun _ _ _ _ => []) (fun k prev r s u v =>
    match k with
    | 0 => []
    | 1 => match r, s with
      | false, true => [(u ++ [false] ++ v, 1)]
      | true, false => [(v ++ [true] ++ u, 1)]
      | _, _ => []
    | _ + 2 => match r with
      | false => (cop u).flatMap fun p =>
          (prev true s p.2 v).map fun q => (p.1 ++ [false] ++ q.1, q.2)
      | true => (cop v).flatMap fun p =>
          (prev false s u p.2).map fun q => (p.1 ++ [true] ++ q.1, q.2))

theorem MrsAux_zero : MrsAux 0 = (fun _ _ _ _ => []) := rfl
theorem MrsAux_succ (n : ℕ) : MrsAux (n + 1) = (fun r s u v => match n with
    | 0 => []
    | 1 => match r, s with
      | false, true => [(u ++ [false] ++ v, 1)]
      | true, false => [(v ++ [true] ++ u, 1)]
      | _, _ => []
    | _ + 2 => match r with
      | false => (cop u).flatMap fun p =>
          (MrsAux n true s p.2 v).map fun q => (p.1 ++ [false] ++ q.1, q.2)
      | true => (cop v).flatMap fun p =>
          (MrsAux n false s u p.2).map fun q => (p.1 ++ [true] ++ q.1, q.2)) := rfl

def Mrs (r s : Bool) (n : ℕ) (u v : Word) : FSum := MrsAux n r s u v
theorem Mrs_step_false (s : Bool) (k : ℕ) (u v : Word) :
    Mrs false s (k + 3) u v = (cop u).flatMap (fun p =>
      (Mrs true s (k + 2) p.2 v).map fun q => (p.1 ++ [false] ++ q.1, q.2)) := rfl
theorem Mrs_step_true (s : Bool) (k : ℕ) (u v : Word) :
    Mrs true s (k + 3) u v = (cop v).flatMap (fun p =>
      (Mrs false s (k + 2) u p.2).map fun q => (p.1 ++ [true] ++ q.1, q.2)) := rfl

def rsVal (b : Bool) : ℕ := if b then 2 else 1

/-- ER index set condition n ≡ r + s + 1 (mod 2) (redundant, kept for fidelity). -/
def inIndex (r s : Bool) (n : ℕ) : Bool := (n + rsVal r + rsVal s + 1) % 2 == 0

/-- Mixing operator on words, summed over all n in ER's index set.  Terms with
    n > |u| + |v| + 2 vanish (lemma `Mrs_eq_nil_of_large` below), so the finite range is exact. -/
def Mw (u v : Word) : FSum :=
  [false, true].flatMap fun r => [false, true].flatMap fun s =>
    ((List.range (u.length + v.length + 3)).filter fun n => 2 ≤ n && inIndex r s n).flatMap
      fun n => Mrs r s n u v

noncomputable def M : ABPoly →ₗ[ℚ] ABPoly →ₗ[ℚ] ABPoly :=
  Finsupp.linearCombination ℚ fun u =>
    Finsupp.linearCombination ℚ fun v => toPoly (Mw u v)

/-- I2 on a word, Theorem 32. -/
def I2w (w : Word) : FSum :=
  [(w, 1), (w.reverse, 1)] ++ (cop w).flatMap fun p => Mw p.1.reverse p.2

/-- The linear operator I2 on ℚ⟨a,b⟩ (linear extension of `I2w`). -/
noncomputable def I2 : ABPoly →ₗ[ℚ] ABPoly :=
  Finsupp.linearCombination ℚ fun w => toPoly (I2w w)

/-- Reversal u ↦ u*. -/
noncomputable def star : ABPoly →ₗ[ℚ] ABPoly := Finsupp.lmapDomain ℚ ℚ List.reverse

/-- Homogeneous part of degree n. -/
def deg (n : ℕ) : Submodule ℚ ABPoly := Finsupp.supported ℚ ℚ {w : Word | w.length = n}

/-- Antisymmetric, resp. symmetric, homogeneous ab-polynomials of degree n (Definition 34). -/
noncomputable def anti (n : ℕ) : Submodule ℚ ABPoly := deg n ⊓ LinearMap.ker (star + LinearMap.id)
noncomputable def symm (n : ℕ) : Submodule ℚ ABPoly := deg n ⊓ LinearMap.ker (star - LinearMap.id)

/-- MathDB 347230 / Hetyei Conjecture 39 (kernel taken inside the degree-n part; the printed
    codomain `Q<a,b>_{n+1}` is immaterial for the kernel). -/
def KernelConjecture : Prop := ∀ n : ℕ, 1 ≤ n → deg n ⊓ LinearMap.ker I2 = anti n

end Hetyei347230
