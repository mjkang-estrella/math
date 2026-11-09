# Reproduction

Extract `kirchhoff-source-only.zip` into a new empty directory. The archive contains no oleans. Set `LEAN_BIN` to the Lean 4.34.1 executable (commit 5045d0056413266e57c625dcd7c365b10e377c52), and `LEAN_PACKAGES` to the read-only mathlib package cache pinned to d13f23b723b8a846827a245b89c10fc7d3f11612. Run `python3 -I replay.py` from the extraction directory.

The driver refuses any existing olean, verifies source hashes, sanitizes the child environment, and sequentially builds Basic, Certificates, Graph and RealBridge with `lean -j1 -DwarningAsError=true`. It runs leanchecker on each proof module, then the all-local-declaration audit, then three expected-failure negative controls. Audit.lean is command-only audit tooling; all declarations in every proof module, including generated declarations, are selected by module identity, not namespace or a handwritten theorem list.

Every Lean and leanchecker invocation goes through scripts/run.py: at most two CPU affinities, 120 seconds of CPU per process, 140 seconds wall time, MALLOC_ARENA_MAX=2, and a 6 GiB sampled private-RSS process-group watchdog. Outputs, temporary directory, logs and receipts stay in the extracted directory. A killed control does not count as a successful rejection. Full process output is retained in logs, with structured return codes, time, peak sampled private RSS and termination reasons in receipts.

The real endpoints are `KirchhoffReal.refuteMP` and `KirchhoffReal.refuteSpec`. `formal/Certificates.lean` contains explicit 11 by 11 rational Laplacians, inverse certificates, intermediate products and kernel-decide checks. The real bridge proves that mapped matrices satisfy the same equations and that pair sums and trace indices map correctly.

Negative controls reject the old asymmetric -2Xij paraphrase's numerical value, reject the group inverse as the Moore–Penrose inverse, and reject a unit perturbation at entry (0,0). No forbidden axiom or unsafe proof mechanism is introduced even in the controls.

This work does not rerun or expand the prior-art gate. Its read-only source inputs are copied with identical SHA-256 hashes and bound before and after the work. Root acceptance and independent fidelity review remain required; a successful replay is not self-acceptance or novelty clearance.
