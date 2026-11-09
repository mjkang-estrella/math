# Preserved failures and corrections

All attempted Lean inputs, stdout/stderr logs, exit status and resource receipts are retained as attempt-NNN-source.lean/.log/.json. failures.json indexes every unsuccessful compiler attempt (including killed/aborted runs). No failure is represented as proof success.

Initial errors involved a missing power argument, rational/real cast alignment, a denominator comparison, explicit filter-limit binder types and goal order, a strict-event reflexivity goal, and elementary exponential constant simplification. These were corrected with kernel-checked proofs.

Several embedded/global and then module-indexed metaprogram audit attempts exceeded the unchanged memory cap. Import trimming reduced proof-module memory but did not fix embedded interpretation. A separately compiled embedded tool also failed. The final safe standalone Lean auditor imports only Environment, Path and FoldConsts, loads the proof environment with loadExts=false, and explicitly traverses theorem/opaque bodies using allowOpaque=true. Its 34-second full-body run passed at roughly2.50GiB. An initial standalone findSysroot call failed because lean was absent from PATH; the final tool uses the authorized absolute sysroot.

The inherited instrumentation used value? without allowOpaque=true, which skips theorem/opaque bodies in this Lean version. Its reported dependency count was therefore insufficient for this task. The new full-body audit covers17562 dependencies; no inherited proof module was modified.

Operational bounded listings included a missing not-yet-created target directory, an initially overly broad/truncated administrative file listing, and a nonexistent speculative mathlib source path. No science source contents were read before freezing the assigned science inputs. Exploratory library declaration lookup preceded supplemental library-source copies; package revisions were pinned throughout. No network requests, HTTP failures, bypass, retry, or retrieval occurred.

Packaging initially failed because ancestor and batch administrative AGENTS.md snapshots shared a flat filename. The original recorded batch hash and the independent inherited administrative snapshot agreed; the batch snapshot was restored to a distinct flat filename with unchanged recorded hash. Scientific snapshots were unaffected.
