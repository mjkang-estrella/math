# sigma-fusion-366458

Paper source: [paper.tex](paper.tex). Complete written proof: [proof.md](proof.md). Complete Lean certificate: [formal/SigmaFusion.lean](formal/SigmaFusion.lean). Source and novelty review: [../discovery.md](../discovery.md).

All 25 local definitions/theorems compile and pass the axiom audit with Lean 4.34.1 and the pinned mathlib dependencies. Rebuild with:

```sh
python formal/rebuild.py
```

Run from this package directory; the script also works from any directory when its path is supplied. Dependencies must already be compiled. Explicit `--lean-bin` and `--mathlib-packages` options support other locations. See [formal/build/audit.json](formal/build/audit.json) and [formal/build/Checks.log](formal/build/Checks.log). No PDF has been generated.
