# Capped runnable checks

Every command below must use this exact prefix, retaining the fixed guard and environment:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python
```

Append the absolute assigned-lane script path followed by one mode. Each mode is a separate guarded run; do not combine them into one uncapped shell batch. All scripts write only inside their own assigned lane. To preserve this finalized packet, copy it within an authorized verification destination before invoking modes that rewrite outputs; no extracted strict replay is claimed here.

* `depth.py dag`: reconstructs every known-DAG node/mask and root overlap analysis.
* `depth.py union`: enumerates every root branch subset and all minimal80-union plans; requires dag output.
* `depth.py grammar`: all1225 intervals to closure.
* `depth.py contexts`: all100 short prefix/suffix contexts to closure; complete flag is false until all100 finish. A per-word45000-state exception aborts, and never certifies a count. The delivered run completed all100.
* `depth.py code`: all3279 code-input reflection checks and1521 reused-separator tests.
* `depth.py sync`: synchronization and prefix/suffix split checks.
* `depth.py extend`: all1392 possible length18 square-free ternary fourth-code candidates, preserving failures.
* `verify.py science`: independent complete known-DAG edge/reachability/mask verification plus all finite conditions used by the universal reflection lemma. It uses a separate square-deletion implementation and does not import depth.py.
* `work.py finalize`: binds current immutable scientific references and writes provenance/progress/chronology. It does not refetch.
* `verify.py manifest`: write final manifest, excluding itself and final receipt.
* `verify.py final`: separate guarded final verification of manifest, immutable originals, all new original/copy PDFs, live query bytes and independent re-extraction hashes. Only after all checks pass does it write final-verification.json.

The last two modes must be SEPARATE guard invocations after every intended write. Do not invoke fetch/papers when replaying: immutable existing sources suffice, and denied routes must remain parked. The standard guard enforces512MiB AS and sampled group RSS,210CPU/230wall; no parameter raises are supported here.
