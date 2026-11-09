# MathDB 365943 r5p: partial Coverage8 bridges and proved composition

This lane does not complete the assignment. Coverage8 and the unconditional
endpoint remain absent. No solution credit or self-acceptance is claimed.

The proved additions construct catalogue graphs and check all catalogue codes
at orders 1 through 8, extend deletion labels to a permutation on the full
vertex set, encode the transported neighbourhood with the required bound, and
prove the inherited extendGraph arithmetic has exactly the transported
adjacency. The general binary and row-major encoding proofs work at arbitrary
orders. The remaining Coverage8 obligations are mask eligibility and catalogue
induction, specified in GAPS.md.

The exact composition theorem `Nut8.finite_of_parts` is proved against the
root-fixed interface. The unchanged r4a endpoint is copied, and
`Nut8.target_of_parts` composes both explicit assumptions into Target.
FinalEndpoint.lean contains the exact requested assembly source but is excluded
until Coverage8.lean exists; its theorem is not claimed as checked.

All selected inputs are SHA-256 bound in inputs-before.json and copied under
inputs with hash identity. Every r4b inherited Lean source and the fixed
NutInterface.lean are unchanged; r4a's shared modules agree byte for byte, and
its added modules are copied unchanged. r4a-compatibility.json lists both groups.
The supplied r4b packet, interface and r4a packet hashes match the assignment.
Final input rechecks and declaration counts are recorded separately after replay.

The source-only packet and portable replay driver perform a fresh sanitized
strict build, leanchecker for each built module, all-local declaration audit,
and negative controls. AuditAll logs module, full type, full body with opaque
values enabled, flags and transitive axioms, including generated declarations.
Only propext, Classical.choice and Quot.sound are permitted. See results.json
and fresh-extracted/logs/replay.json for the actual replay outcome.

One resource-rule deviation occurred in development: two capped Lean calls
briefly overlapped. It is documented in GAPS.md; the extracted replay runs
sequentially. No git, shared ledger writes, child agents or external actions
were used. No background process is intended to remain at handback.
