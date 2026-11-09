# Reproduction

Run checks.py and verify_final.py ONLY through:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python SCRIPT_ABSOLUTE_PATH

Guard limits: AS512MiB, process-group RSS512MiB, CPU210s, wall230s. Do not increase them. The verifier is separate from final writing and manifest creation. It excludes only manifest.json and verification-receipt.json from the final file manifest. Its receipt includes UTC, manifest hash and precise failures. Never bind live ledger/NEXT as scientific originals. No network is needed for replay; sources and extracts are already present. No numerical replay proves an arbitrary-order assertion or establishes novelty.
