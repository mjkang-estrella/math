# Reproduction

From this lane, run each command through the required absolute helper:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python diagnostics.py

diagnostics.py uses SymPy for exact algebra, no random seed or floating tolerance. Resource envelope remains AS512MiB / sampled process-group RSS512MiB / CPU210s / wall230s with one BLAS/OMP thread, no cap raises. Observed diagnostics peak sampled RSS54,460,416bytes and wall0.882s. The final verification is a distinct guarded process:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py

Do not rerun exploratory search commands into existing paths: see FAILURES.md. Manifest recreation is deliver.py; verification occurs afterward in a separate process. Administrative originals may change due to root/concurrent work and are snapshot-only; verifier checks their copies only. Scientific originals and copies are both rechecked.
