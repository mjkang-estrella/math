# Fresh replay receipt

A source-only archive, source.zip, was created with the relative paths shown by zipinfo. Every entry was inspected: no absolute paths, parent components, build files or dependency packages. It was extracted into the new empty lane-local replay/fresh directory.

`bash replay/fresh/scripts/replay.sh` exited 0. All 16 capped steps exited 0: seven strict Lean builds, seven explicit-module leanchecker runs, Python regression and report generation. The fresh generated results.json is byte-identical to the working results.json. Logs are in replay/fresh/logs, with the combined transcript in logs/fresh-replay.out and logs/fresh-replay.err.

Archive SHA-256: b9752d0b267e8d201ac2ac7cad4916cc4658108562430eb4164946aed51fd2e7.

The audit has 106 local and 5,260 upstream declarations. Local unsafe, partial, implemented_by, extern and _unsafe_rec totals are zero. Upstream metadata totals are reported separately in results.json; only the three allowed logical axioms occur. Both endpoints are conditional. This receipt does not accept the conjecture or claim credit.

Earlier development logs, including failed elaborations and the initial leanchecker PATH failure, are retained. The fresh replay uses the corrected PATH shim, which supplies the memory and thread options even for Lean subprocesses launched by leanchecker. No worker process remains at handback.
