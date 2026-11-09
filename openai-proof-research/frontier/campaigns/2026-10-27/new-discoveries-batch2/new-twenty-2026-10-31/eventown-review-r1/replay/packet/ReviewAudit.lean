import Eventown
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
 let env ← getEnv
 let mut count : Nat := 0
 for (n,c) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let m := env.header.moduleNames[idx.toNat]!
  if m.toString == "Eventown" then
   count := count + 1
   let ax ← Lean.collectAxioms n
   let ty ← liftTermElabM <| Lean.Meta.ppExpr c.type
   logInfo m!"DECL|{n}|MODULE|{m}|UNSAFE|{c.isUnsafe}|PARTIAL|{c.isPartial}|BODY(value? true)|{(c.value? true).isSome}|AXIOMS|{ax.toList}\nTYPE|{ty}"
   if c.isUnsafe || c.isPartial then throwError "bad safety {n}"
   match c with
   | .axiomInfo _ => throwError "local axiom {n}"
   | _ => pure ()
   if !(c.value? true).isSome then throwError "missing body {n}"
   for a in ax do
    if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a then throwError "bad axiom {a}"
 logInfo m!"COUNT|{count}"
namespace IndependentReview
-- Independently restated predicates, without the candidate's shorthand.
def SourceStatement : Prop :=
 ∀ n : ℕ, 2 ≤ n → ∀ F : Finset (Equiv.Perm (Fin n)),
 ((∀ σ ∈ F, ∀ π ∈ F, σ ≠ π →
   ∃ i : Fin n, ∃ k : ℕ, 0 < k ∧ Even k ∧ ((σ * π⁻¹)^k) i = i ∧
     ∀ j : ℕ, 0 < j → j < k → ((σ * π⁻¹)^j) i ≠ i) ∧
  ∀ H : Finset (Equiv.Perm (Fin n)),
   (∀ σ ∈ H, ∀ π ∈ H, σ ≠ π →
    ∃ i : Fin n, ∃ k : ℕ, 0 < k ∧ Even k ∧ ((σ * π⁻¹)^k) i = i ∧
      ∀ j : ℕ, 0 < j → j < k → ((σ * π⁻¹)^j) i ≠ i) → H.card ≤ F.card) ↔
 (∃ P : Sylow 2 (Equiv.Perm (Fin n)), ∃ a b : Equiv.Perm (Fin n),
  ∀ x, x ∈ F ↔ ∃ h : P, x = a * (h : Equiv.Perm (Fin n)) * b)
theorem source_refuted : ¬ SourceStatement := Eventown372630.literal_source_refutation
-- Positive negative-controls: false witness properties have kernel-checked negations.
theorem bad_card : Eventown372630.witness.card ≠ 9 := by decide
theorem bad_closure : Eventown372630.w1 * Eventown372630.w5 ∉ Eventown372630.witness := by decide
theorem identity_has_no_bounded_even_cycle : ¬ Eventown372630.BoundedEvenCycle (1 : Equiv.Perm (Fin 5)) := by
  unfold Eventown372630.BoundedEvenCycle
  decide
end IndependentReview
#print axioms IndependentReview.source_refuted
