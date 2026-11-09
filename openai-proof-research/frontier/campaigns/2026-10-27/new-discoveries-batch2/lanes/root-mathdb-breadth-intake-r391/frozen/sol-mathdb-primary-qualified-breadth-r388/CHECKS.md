# Capped replay

From the repository root, run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-mathdb-primary-qualified-breadth-r388/verify.py
```

Fixed inherited guard: 512MiB address-space/groupRSS, CPU210s, wall230s. No raised limits. Every Python helper in this task used this exact guard prefix, including subprocess-based PDF text extraction. Native text inspection used bounded shell reads. No scientific finite sweeps were run.

`bind.py` performed the initial pre-content binding. `extract.py` extracted only reserved records after binding. `fetch.py` and `fetch_additional.py` retain HTTP responses before reading; they are provenance scripts, not necessary for offline replay and should not be rerun to replace sealed evidence. `read_sources.py` and `read_additional.py` extracted only after checking retained byte hashes. `finish.py` encodes the individual dispositions. `seal.py` builds the lane payload manifest. `verify.py` independently checks integrity against actual originals; it does not call any upstream verifier or mutate an upstream receipt.

The final verification receipt is excluded from the payload to avoid self-reference. Every other file, including scripts, binding receipt, selected-record extraction, evidence and failures, is covered.
