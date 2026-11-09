All failed compilation attempts are retained as attempt*, words*, attractor*,
endpoint* logs and guard receipts. attempt01 imported all Mathlib and was
killed at sampled groupRSS 3,289,370,624 bytes, exceeding 2800MiB. It was
replaced by narrow imports without changing caps. Subsequent failures were
ordinary Lean errors: lemma application syntax, missing Nat.Find import,
elaboration of implicit Nat.find predicates, length conversion, missing
decidability instances, arithmetic normal forms, and strict linter warnings.
An Endpoint attempt ran before its failed Attractor dependency was available
and correctly failed with unknown module. None was passed off as verified.

The first all-origin audit found compiler-generated prefixWord._unsafe_rec,
unsafe=false but DefinitionSafety.partial. The audit verifier rejected it.
The equation-style recursion was replaced with explicit Nat.rec; the final
all-origin audit must have no partial or unsafe owned declarations. The old
audit01.log preserves the rejected inventory. No authored partial recursion
was used, and no generated partial declaration is silently exempted.

Inherited source/retrieval failures remain frozen in frozen/6/failures.md and
frozen/scout-metadata/FAILURES.md and failures.jsonl. Those include initial
scout dual-freeze sequencing deviation, guessed identifier404, failed HiGHS
exit134, and failed mixed four-boundary rule. The independent review's later
Dolce retrieval supersedes the scout's unread-Dolce limitation only to the
precise extent stated in review.md. Registry and historical-access holds
remain. No failed numerical search is used as a Lean premise or novelty proof.
