# Failures, deviations and limits

The first inventory command (`pwd; rg --files ...`) ran outside the required guard and searched too broadly, producing truncated output. It was read-only, but is a command-discipline deviation. Native `ls`, `cat`, `sed` and `rg` reads subsequently used bounded named inputs; several overly broad read outputs were truncated and targeted rereads followed. No failed command has been omitted from the session record. No helper, retrieval, script edit or hash command was executed outside the specified helper guard; apply_patch edits are explicitly permitted.

All guarded invocations used OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1 and python -B, with the prescribed unmodified guard's AS/groupRSS512MiB, CPU210 and wall230 limits. No cap was raised. Guarded checker runs and retrievals succeeded; no access denial was retried. Candidate failures remain in frozen/FAILURES.md and frozen/failed-metadata.txt.

An interim review update correctly said that Example16.2 alone did not give an established global bridge. Further actual-body reading found the decisive Lemma16.1. The final review supersedes the interim unresolved-bridge assessment and includes a complete general deduction and exact quartic. No exclusion is based on the interim shortcut objections.

Journal VoR body not obtained. Crossref and OpenAlex were successful metadata/location lookups; neither is a body substitute. ScienceDirect, GitHub API/raw/codeload/diff/patch, browser, proxies and TLS bypasses were not attempted. No repeated HEAD loops. Old capped registry/history gaps and current denied registry routes remain unresolved and were not reopened. Source and priority coverage is bounded.

No children, shared/git/public edits, Lean, manuscript or acceptance work. Administrative snapshots are not live replay bindings. The manifest excludes manifest.json and verification-receipt.json explicitly; the final verifier is a separate guarded invocation after final content/manifest writes.
