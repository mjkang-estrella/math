# Exact runnable checks

From the math workspace, set task-local variables:

```bash
review_lane=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-semigroup-support-review-empty-lines-r297
review_guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$review_guard" python "$review_lane/check.py"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$review_guard" python "$review_lane/finalize.py"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$review_guard" python "$review_lane/verify.py"
```

The last verification is a separate guarded invocation, after the final manifest is written. Manifest excludes itself and verification-receipt.json. check.py is offline, exact rational/integer arithmetic and independent Boolean DP. It imports no author code. Its construct(k,m,typ) gives explicit aligned failed triples on the two empty supports, typ0 for4a=3b and typ1 for4a=3d. All parameters must satisfy discovery.md hypotheses. Running check.py executes the checks and writes checks.json; it does not fetch sources.

freeze.py and scout.py are provenance procedures already completed, not routine replay dependencies. Do not refreeze historical inputs or reretrieve sources to validate this snapshot. Final verify rechecks original and copied bytes on all flat bindings and checks all source PDF/text hashes against preinspection access records. If any original subsequently changes, it reports failure rather than silently rebinding it.

Recorded scientific check runtime: final run26.65s, peak sampled group RSS17,317,888 bytes, exit0 under fixed512MiB/CPU210s/wall230s caps. No limits raised. Other failures are preserved in failures.json. No Python/helper/hash/retrieval was run outside the prescribed guard.
