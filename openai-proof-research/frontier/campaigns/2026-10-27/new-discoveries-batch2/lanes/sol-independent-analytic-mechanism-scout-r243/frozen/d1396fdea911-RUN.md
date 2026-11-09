Run only via the assigned fixed guard, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1:

    python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python checks/check.py

from this lane. Same guard for checks/verify.py after writes. Limits:512MiB AS and sampled group RSS, CPU210s, wall230s; no increases. Sampling does not certify absence of arbitrarily short RSS spikes.
