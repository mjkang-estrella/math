Every command runs from this lane with:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python checks.py

Replace checks.py by verify.py for the separate final check. AS/groupRSS512MiB CPU210s wall230s fixed, group sampling about40ms; no cap raised. The guard script is referenced, not modified or duplicated. checks.py uses only the standard library. Guarded source collection scripts remain runnable but network reruns are not required for verification and previously denied routes must never be retried. finalize.py generates manifest after writes; verify.py runs separately and writes receipt excluded from manifest. No source is mutated by checks.
