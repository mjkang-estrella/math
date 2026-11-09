# Extracted replay receipt

Fresh extraction: verification/ from the safe 17-file source-only archive.
Six strict serial builds and six per-module leanchecker invocations passed.
All three negative controls failed as required. No live lane process remains.

LOCAL declarations: 59; unsafe/partial/added-axiom/
unsafe_rec/implemented_by/extern flags all zero.
The endpoint import closure has 252976 declarations,
including private/generated declarations. Audit used import all for the full module
closure and kernel ConstantInfo values with allowOpaque := true.
The audited endpoint set equals its module inventory exactly.

Conditional endpoint axioms: propext, Classical.choice, Quot.sound.
Upstream metadata is separate in verification/replay-report.json; the entire compiler/
tactic import closure contains unsafe implementations, partial functions, externs, and
axioms such as sorryAx and Lean.trustCompiler. These are NOT transitive axioms of the
conditional endpoint or any LOCAL mathematical declaration. No blanket whitelist PASS
for every unrelated upstream declaration is claimed.

Peak replay process-group RSS: 3281044 KiB.
Longest replay process wall time: 73.689 seconds.
Unique compiler/checker logs: verification/logs/.
Full per-declaration metadata, axioms, and direct dependencies:
verification/audit.jsonl (including allowOpaque proof bodies).

Exact remaining Props and the conditional literal endpoint: src/GridFinal.lean.
This validates a PARTIAL handback; it does not discharge the conjecture.
