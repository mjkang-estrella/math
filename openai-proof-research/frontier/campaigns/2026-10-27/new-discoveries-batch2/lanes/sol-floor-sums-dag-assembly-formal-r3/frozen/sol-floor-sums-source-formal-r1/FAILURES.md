# Preserved failures and limits

- Initial bounded file inventory was too broad and its displayed output truncated. No scientific conclusion used that truncated inventory.
- First guarded source freeze looked for wong-current.txt among original scientificbindings names and raised IndexError. The partial PDF copy was subsequently rebound in freeze.json; the complete four primary files were frozen from the immutable r2 source packet before reading them. The helper exited 1, sampled RSS 10,330,112 bytes, wall 0.0401 seconds.
- attempt01 imported all Mathlib.Tactic and was killed by the 2800 MiB process-group RSS guard: observed 3,003,314,176 bytes at a sampled boundary, exit -9. This is a detected cap crossing (sampling overshoot), not a cap increase. Broad imports were replaced with narrow ones. No resource limits were raised.
- attempt02 requested a nonexistent Mathlib.Tactic.Omega object. The core Lean.Elab.Tactic.Omega import fixed it.
- attempt03–07 expose cast-placement, missing imports, unused-variable warnings, and a `1*m` rewrite mismatch. The integer-division-vs-natural-division issue was corrected explicitly, not hidden with a bridge assumption. All logs/guard receipts remain.
- probe01 ran before a successful Reduction object existed; probe02 intentionally queried unavailable names while discovering available library interfaces. Probe.lean is a diagnostic file, not part of run.sh or the audited modules; its failed output is preserved.
- source01 had an unused K parameter under warningAsError. It was removed. expansion01 needed explicit nonmembership proofs for the sixteen-set sum expansion; expansion02 succeeds.
- Full certificate elaboration was not implemented. This is the material remaining failure to meet the requested unconditional endpoint. No Python computational PASS has been promoted to Lean PASS.

Lean invocations use serial -j1 -M2700, warningAsError=true, autoImplicit=false, CPU210/wall230, group RSS2800MiB, and no extra address-space cap. Non-Lean helpers use the required 512MiB AS/group-RSS CPU210/wall230 guard. No denied network route or browser was used or retried; this lane performs no live retrieval. Current registry clearance and inaccessible historical intervals remain parked and HOLD.
