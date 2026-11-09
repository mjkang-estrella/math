Run from `openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2`. Every command
goes through the guard with the fixed caps (AS/RSS 512 MiB, CPU 210 s, wall 230 s; never raise them):

```bash
G=lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
L=lanes/claude-projection-packing-full-r1
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python3 $G python3 -I -B $L/tools/verify.py            # final verification (writes only verification-receipt.json)
python3 $G python3 -I -B $L/tools/exp5_geofrac_w.py     # exact rational check of Theorem A' on source V (deterministic)
python3 $G python3 -I -B $L/tools/exp2_climb2d.py 25 5 170 1.03       # 2-dim distance climb (seed N budget lammin)
python3 $G python3 -I -B $L/tools/exp3_fp_adversarial.py 53 2 5 min 170 c 1.01   # loss coefficient search
python3 $G python3 -I -B $L/tools/exp4_rules.py 63 2 5 min lp 170     # selection rule lp|geo|self
```

The exp1–exp4 scripts are float, lp_solve-based, and wall-clock budgeted, so their outputs are not
bit-reproducible. They are support evidence only. Their recorded outputs are in runs/. exp5 is exact
and deterministic. No network access is used by any script. manifest.json (built by tools/manifest.py)
explicitly excludes itself and verification-receipt.json.
