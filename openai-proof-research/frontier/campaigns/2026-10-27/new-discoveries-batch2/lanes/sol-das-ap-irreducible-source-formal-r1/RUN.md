# Reproduce

Extract source-only.tar.gz into a fresh directory inside this lane, then run `bash run.sh` there. No own olean is supplied. The runner checks the compiler hash and all nine package heads, builds Definitions then Witness serially, runs exhaustive Audit, and checks every declaration and source hash.

Lean runner is the frozen completed cube-lane convention: pinned lean-4.34.1, -j1 -M2700, groupRSS2800MiB, CPU210, wall230, no additional AS cap. Each Lean subprocess has its own strict guard. No limits are raised. No lake update, git command or network operation is needed.

All Python utility work runs as:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 <helper.py>
```

That helper guard fixes AS/groupRSS512MiB, CPU210, wall230. Lean is invoked separately through lean_guard.py, as expressly authorized, so it does not inherit the helper's AS limit. Native bounded reads are permitted. verify_pins.py checks the compiler SHA, lake manifest SHA and nine package HEAD files without git operations. Replay receipts are generated, not packaged as proof premises. final_verify.py is run separately after the final manifest write.
