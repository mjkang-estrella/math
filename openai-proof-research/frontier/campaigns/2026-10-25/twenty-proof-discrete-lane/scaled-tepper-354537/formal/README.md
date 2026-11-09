# Lean certificate

Module: `Tepper.lean`; namespace: `ScaledTepper`; source question: MathDB #354537.

Run from any directory:

```sh
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-discrete-lane/scaled-tepper-354537/formal/rebuild.py
```

Optional `--lean-bin` and `--mathlib-packages` arguments select an existing local installation; `pins.json` remains mandatory. The driver checks every dependency revision and forbids tracked modifications. It never downloads or writes dependencies. Compiled artifacts and logs are regenerated in `build/`. The source directory is excluded from `LEAN_PATH` during the audit, preventing a stale adjacent object from satisfying the checks import.

The script checks every local definition and theorem with both `#check` and `#print axioms`. Allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. No additional axioms or admissions are accepted.
