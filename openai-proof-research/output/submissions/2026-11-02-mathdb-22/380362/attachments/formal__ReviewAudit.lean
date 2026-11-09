import Loop
import Lean
open Lean Elab Command
open Loop380362
-- Stronger control: remove the candidate's identity-preservation requirement.
theorem unpointed_inequivalence : ¬ ∃ e : Q ≃ Q,
    ∀ x y z, e (assocGroup x y z) = assocLoop (e x) (e y) (e z) := by
  rintro ⟨e, ha⟩
  have hz := ha (e.symm zero) (e.symm zero) (e.symm zero)
  have he : e zero = zero := by
    simpa only [assocGroup, e.apply_symm_apply, show assocLoop zero zero zero = zero from by decide] using hz
  have h := ha (e.symm u) (e.symm v) (e.symm w)
  change e zero = _ at h
  rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h
  exact assoc_nonzero h.symm
example : assocGroup u v w = zero := by decide
example : assocLoop u v w = (false, false, false, true) := by decide
example : distance ≠ 96 := by decide
example : ¬ IsAssociator loop assocGroup := by unfold IsAssociator; decide
run_cmd do
  let env ← getEnv
  let mut total : Nat := 0
  for (n,c) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if env.header.moduleNames[i.toNat]! == `Loop then
        total := total + 1
        if c.isUnsafe then throwError "Unsafe declaration: {n}"
        match c with
        | .axiomInfo _ => throwError "Local axiom: {n}"
        | _ => pure ()
        let ax ← Lean.collectAxioms n
        for a in ax do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
            throwError "Forbidden axiom {a} in {n}"
        logInfo m!"AUDIT {n} unsafe={c.isUnsafe} axioms={ax.toList}"
  if total != 28 then throwError "Unexpected declaration count: {total}"
  logInfo m!"ALL LOCAL DECLARATIONS: {total}"
#print axioms unpointed_inequivalence
#print Loop380362.SourceClaim
#print axioms Loop380362.source_refutation
