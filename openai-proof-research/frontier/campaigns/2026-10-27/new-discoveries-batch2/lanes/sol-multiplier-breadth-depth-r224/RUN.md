# Exact runnable checks

Run from the repository root. Every Python/helper/retrieval/hash operation uses the stipulated guard and environment. Caps are fixed AS/groupRSS512MiB, CPU210s, wall230s; no cap raises.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-multiplier-breadth-depth-r224/verify.py
```

verify.py is a separate process after final payload writes. It verifies every payload hash, frozen original/copy bindings, and every Jensen sign by integer square-root enclosures only. The manifest excludes itself and verification-receipt.json. The receipt does not certify the ordinary analytic proof or novelty.

To regenerate finite certificates, replace verify.py with check_exact.py in that command. This invalidates the manifest until a guarded finalize.py run followed by a new guarded verify.py run. Floating mpmath evaluations only choose candidate test points; certified signs use integer arithmetic at600 bits. Replaying the frozen payload needs no network.

bootstrap.py, research.py, scout.py, bodies.py, inspect.py, alias.py, compact.py and citers.py preserve the research procedures. Retrieval names are write-once; do not replay downloads or parked/denied routes to verify this packet. finalize.py refreshes source receipts, chronology, provenance and manifest, but is not the verifier.
