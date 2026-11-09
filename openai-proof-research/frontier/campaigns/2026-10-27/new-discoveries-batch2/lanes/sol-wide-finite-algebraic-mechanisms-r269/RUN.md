# Capped reproduction

Run from /home/mj-kang/Documents/Dev/math. Every Python/helper/retrieval/hash/edit operation uses this guard and these environment settings. No cap changes:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-finite-algebraic-mechanisms-r269/check.py
```

The fixed guard enforces 512MiB address space and sampled process-group RSS, 210CPU seconds and230wall seconds. Exact arithmetic uses Python integers/Fraction only. The check stops at the first rank-one obstruction; no numerical evidence is used. check.py rewrites exact-checks.json deterministically. A replay should compare its original hash; if artifacts are intentionally changed, rebuild the manifest before verification.

For distinct post-write verification use the identical prefix, replacing the last path `check.py` by `verify.py`. It validates the manifest, original/copy bindings and source/text hashes, then independently checks the modular minors, graph distances and path-count witness. It writes only verification-receipt.json, excluded from the manifest. `finalize.py` builds the manifest and provenance before this distinct step; it performs no retrieval.

Retrieval helper `work.py fetch URL NAME` saves a bounded response and access receipt before any scientific extraction. `work.py text NAME.pdf` hashes the saved source before/after pdftotext and records the derived hash. Failed/denied/challenged routes must not be retried by a replay; cached bytes suffice. Never use an unguarded Python invocation for these scripts.
