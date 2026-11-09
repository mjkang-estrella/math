# Exact runnable checks

From this lane, use the fixed guard for EACH command. Do not execute the frozen author scripts in place: some write next to themselves. Our checkers import no author modules and write only lane result JSON.

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python audit.py
python "$guard" python next_supports.py
python "$guard" python support_check.py
python "$guard" python support2_check.py
python "$guard" python verify.py
```

All executed under fixed512MiB AS and process-group RSS,210 CPU seconds,230 wall seconds, with no raised caps. Observed guarded runs: audit2.93s/~34.8MB; next ratio0.32s/~13.3MB; support A4.13s/~15.0MB; support B4.33s/~14.3MB; scouting3.93s/~45.2MB. Each exited0 without a cap reason. Resource figures are guard observations, not mathematical evidence.

freeze.py is initial construction only and must NOT be rerun to refresh bindings. scout.py is retrieval and initial report freezing only; do not rerun it to rebaseline originals. finalize.py builds the manifest; verify.py is a distinct final read-only integrity check apart from writing its own excluded receipt. Manifest excludes only itself and verification-receipt.json. These outputs are not embedded in their own hashes.
