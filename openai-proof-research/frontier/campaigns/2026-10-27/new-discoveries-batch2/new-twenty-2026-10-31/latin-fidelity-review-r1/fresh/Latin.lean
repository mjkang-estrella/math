import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace MathDB347712
abbrev P (n : ℕ) := Equiv.Perm (Fin n)
abbrev Strategy (n : ℕ) := P n → Fin n
variable {n : ℕ}
def agreement (a : Fin n → Fin n → Fin n) (p : P n) (r : Fin n) : ℕ :=
 (Finset.univ.filter fun i => p i = a r i).card
def magneticity (s : Strategy n) (h i k : Fin n) : ℕ :=
 (Finset.univ.filter fun p : P n => s p = h ∧ p i = k).card
def intensity (s : Strategy n) (h k : Fin n) : ℕ :=
 Finset.univ.sup fun i => magneticity s h i k
def field (s : Strategy n) : ℕ := ∑ h : Fin n, ∑ k : Fin n, intensity s h k
def Latin (a : Fin n → Fin n → Fin n) : Prop :=
 (∀ r, Function.Bijective (a r)) ∧ (∀ i, Function.Bijective fun r => a r i)
def IsLatinStrategy (s : Strategy n) : Prop := ∃ a, Latin a ∧
 ∀ p j, agreement a p j ≤ agreement a p (s p)
def IsOptimal (s : Strategy n) : Prop := ∀ t : Strategy n, field t ≤ field s
def SourceClaim : Prop := ∀ n : ℕ, 0 < n → ∀ s : Strategy n,
 IsOptimal s ↔ IsLatinStrategy s
def cyclic (r i : Fin 5) : Fin 5 := r + i
def better (r i : Fin 5) : Fin 5 :=
 ![![4,0,3,2,1], ![3,2,4,1,0], ![1,4,2,0,3], ![2,1,0,3,4], ![0,3,1,4,2]] r i
def choose (a : Fin 5 → Fin 5 → Fin 5) (p : P 5) : Fin 5 :=
 if ∀ j, agreement a p 0 ≥ agreement a p j then 0 else
 if ∀ j, agreement a p 1 ≥ agreement a p j then 1 else
 if ∀ j, agreement a p 2 ≥ agreement a p j then 2 else
 if ∀ j, agreement a p 3 ≥ agreement a p j then 3 else 4
theorem cyclic_latin : Latin cyclic := by
 unfold Latin Function.Bijective Function.Injective Function.Surjective
 decide
theorem cyclic_selects_maximum : ∀ p j, agreement cyclic p j ≤ agreement cyclic p (choose cyclic p) := by decide
theorem cyclic_field : field (choose cyclic) = 290 := by decide
theorem better_field : field (choose better) = 302 := by decide
theorem cyclic_is_latin : IsLatinStrategy (choose cyclic) :=
 ⟨cyclic, cyclic_latin, cyclic_selects_maximum⟩
theorem cyclic_not_optimal : ¬ IsOptimal (choose cyclic) := by
 intro h
 have hh := h (choose better)
 rw [cyclic_field, better_field] at hh
 omega
theorem source_refutation : ¬ SourceClaim := by
 intro h
 exact cyclic_not_optimal ((h 5 (by decide) (choose cyclic)).2 cyclic_is_latin)
#print axioms source_refutation
end MathDB347712

open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  if (env.getModuleIdxFor? n).isNone then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"AUDIT {n}: {axs}"
   if ci.isUnsafe then throwError "unsafe declaration {n}"
   if ci matches .axiomInfo _ then throwError "custom axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden axiom {ax} in {n}"
 logInfo m!"AUDIT_TOTAL {count}"
