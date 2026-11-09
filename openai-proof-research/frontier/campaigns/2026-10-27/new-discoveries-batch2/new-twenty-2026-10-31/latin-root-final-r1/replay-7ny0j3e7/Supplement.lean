import Latin
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open MathDB347712
open scoped BigOperators
namespace LatinFidelity
-- This predicate adds the usual nonempty-fibre convention explicitly.
def NonemptyFibres {n : ℕ} (s : Strategy n) : Prop := ∀ h, ∃ p, s p = h
def RestrictedOptimal {n : ℕ} (s : Strategy n) : Prop :=
 ∀ t : Strategy n, NonemptyFibres t → field t ≤ field s
def RestrictedClaim : Prop := ∀ n : ℕ, 0 < n → ∀ s : Strategy n,
 NonemptyFibres s → (RestrictedOptimal s ↔ IsLatinStrategy s)
theorem cyclic_nonempty : NonemptyFibres (choose cyclic) := by
 unfold NonemptyFibres
 decide
theorem better_nonempty : NonemptyFibres (choose better) := by
 unfold NonemptyFibres
 decide
theorem better_latin : Latin better := by
 unfold Latin Function.Bijective Function.Injective Function.Surjective
 decide
theorem better_maximum : ∀ p j, agreement better p j ≤ agreement better p (choose better p) := by decide
theorem better_is_latin : IsLatinStrategy (choose better) :=
 ⟨better, better_latin, better_maximum⟩
theorem cyclic_sizes : ∀ h : Fin 5,
 (Finset.univ.filter fun p : P 5 => choose cyclic p = h).card = ![46,26,21,16,11] h := by decide
theorem better_sizes : ∀ h : Fin 5,
 (Finset.univ.filter fun p : P 5 => choose better p = h).card = ![33,27,25,20,15] h := by decide
theorem restricted_not_optimal : ¬ RestrictedOptimal (choose cyclic) := by
 intro h
 have hh := h (choose better) better_nonempty
 rw [cyclic_field, better_field] at hh
 omega
theorem restricted_refutation : ¬ RestrictedClaim := by
 intro h
 exact restricted_not_optimal ((h 5 (by decide) (choose cyclic) cyclic_nonempty).2 cyclic_is_latin)
theorem ordinary_partition_counterexample : ∃ s t : Strategy 5,
 NonemptyFibres s ∧ NonemptyFibres t ∧ IsLatinStrategy s ∧ IsLatinStrategy t ∧ field s < field t := by
 refine ⟨choose cyclic, choose better, cyclic_nonempty, better_nonempty, cyclic_is_latin, better_is_latin, ?_⟩
 rw [cyclic_field, better_field]
 decide
theorem permutation_count : Fintype.card (P 5) = 120 := by decide
theorem cyclic_target_counts : ∀ k : Fin 5,
 (∑ h : Fin 5, intensity (choose cyclic) h k) = 58 := by decide
theorem better_target_counts : ∀ k : Fin 5,
 (∑ h : Fin 5, intensity (choose better) h k) = ![62,62,62,61,55] k := by decide
end LatinFidelity
open Lean in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n, ci) in env.constants.toList do
  if (env.getModuleIdxFor? n).isNone then
   count := count + 1
   let axs ← Lean.collectAxioms n
   logInfo m!"SUPPLEMENT {n} TYPE {ci.type} AXIOMS {axs}"
   if ci.isUnsafe then throwError "unsafe {n}"
   if ci matches .axiomInfo _ then throwError "axiom {n}"
   for ax in axs do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
     throwError "forbidden {ax}"
 logInfo m!"SUPPLEMENT_TOTAL {count}"
