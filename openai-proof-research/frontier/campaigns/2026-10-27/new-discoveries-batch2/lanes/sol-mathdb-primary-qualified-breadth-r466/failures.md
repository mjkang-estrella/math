# Failures and access limits

- freeze.py failed before scientific content: r465 manifest is an object but r304 manifest is a list. Original script and freeze.log preserved.
- freeze-v2.py failed before scientific content: r304 manifest entries omit byte sizes; SHA-256 remained mandatory. Original script and freeze-v2.log preserved. freeze-v3.py checks any supplied size and mandatory hashes, records actual sizes, then succeeded.
- https://arxiv.org/pdf/1401.4502 returned HTTP 404 on 2026-10-31 UTC; no alternate route requested. Record 327084 remains HOLD_SOURCE.
- Current MathDB and public registry clearance unavailable under inherited access restrictions; zero MathDB requests. No known denied route was retried. No direct ScienceDirect, Google, GitHub or browser access was made. Web search returned some publisher and MathDB snippets incidentally; no such page was opened, and no snippet is proof evidence.
- Closest successor coverage remains incomplete for rows without a selected primary successor; no novelty clearance or hard classification inferred.
- No resource-cap failure, Lean, manuscript or large computation. Integrity checks do not audit mathematical dependencies.
