# Preserved failures and limits

1. Initial inventory/read commands emitted more output than the display budget;
   later reads were bounded. All referenced scientific files were frozen before
   their contents were inspected. An attempted read of packet/Assembly.lean
   failed because the endpoint is in Endpoint.lean; no file was invented.
2. PDF marker attempt 1: Node rejected --no-expose-wasm (exit 9).
   Attempt 2 used supported --max-old-space-size=64 --max-semi-space-size=4
   --jitless, but V8 failed at SegmentedTable::InitializeTable (exit 133).
   Both ran through the mandated helper guard, unchanged 512 MiB AS/group RSS,
   CPU210/wall230. Logs are preserved. No marker success, no PDF authoring,
   no rendering, no visual QA: PDF NOTAUTHORED / QA_NOTPERFORMED.
3. The inherited verify_audit.py is a historical component verifier and reports
   NOT_PROVED; it is retained unchanged. full_audit.py is the documented complete
   post-replay verifier. Legacy run.sh is not the strict replay entry point.
4. Predecessor FAILURES.md files are frozen, not overwritten. Inaccessible
   historical intervals and denied routes remain parked. No network retries,
   browser bypass, proxy or TLS changes occurred.
5. The first replay attempt used the byte-identical local helper copy through
   replay.sh's new default. The instruction requires the exact predecessor
   guard path. The attempt was stopped, preserved as replay-attempt01-local-guard
   and restarted cleanly with HELPER_GUARD set to that exact path. Only the
   latter complete strict serial run is used for the final receipt.
6. A combined packaging/documentation patch failed because its README context
   did not match. No partial patch was applied; the corrected patch succeeded.

Resource measurements are sampled process-group RSS, not a guarantee excluding
unsampled transient peaks. No cap was raised. The Lean exception alone removes
the helper's AS restriction for the authorized fixed binary using the inherited
dedicated guard; its RSS/CPU/wall and -j1 -M2700 limits remain unchanged.
