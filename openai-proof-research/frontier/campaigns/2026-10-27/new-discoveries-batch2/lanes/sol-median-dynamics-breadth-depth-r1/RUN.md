# Exact runnable checks

From this lane directory, all commands must use the unchanged assigned guard and environment:

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python certificate.py
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python forward_check.py
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py
```

The final verifier checks the manifest and all bound scientific originals/copies before and after a fresh exact forward replay, then writes only the excluded verification receipt. `finalize.py` regenerates provenance and manifest if authorized lane files have changed. Manifest excludes itself and receipt; no file is modified after final manifest generation except that receipt. The guard fixes512MiB AS/groupRSS,210s CPU,230s wall. Exact certificate and forward verifier use only the Python standard library. Exploratory SciPy modes are optional and not part of the proof; their retained failures must not be treated as full sweeps.
