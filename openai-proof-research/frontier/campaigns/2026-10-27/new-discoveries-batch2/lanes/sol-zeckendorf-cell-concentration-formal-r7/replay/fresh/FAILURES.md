# Preserved failures and limits

All attempt-NNN-source.lean, logs and JSON resource receipts are retained. Early errors involved a deprecated sqrt import, differing decidable-membership instances in an indicator sum, rational/natural casts in parameter inequalities, rational-to-real sums needing Rat.BigOperators, and normalization of a real divided expression. Each was corrected in the final source; no sorry/admit, unsafe/native_decide or partial workaround was used.

inventory-run.log and audit-run.log were exploratory pre-final runs against a previously compiled Concentration.olean after a later compilation failed. They do not certify the final source. The later inventory-final-run.log, audit-final-run.log and independently extracted replay certify the final source. No stale object enters the source-only archive.

A bounded local search for Mathlib/Order/Interval/Finset/Int.lean returned file-not-found; no external retrieval resulted. The generic finite Chebyshev and interval/mixture upper bounds were not implemented. This is a substantive remaining scientific gap, not a compilation failure hidden by the passing component audit. Full endpoint remains HOLD.
