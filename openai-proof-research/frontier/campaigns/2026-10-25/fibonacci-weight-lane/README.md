# Fibonacci recurrence weight preservation — MathDB 371201

Full Lean proof of Pudelko's Conjecture 17 (arXiv:2510.24882v2), formalizing the existing orbit-counting argument posted by **Shivam Patel**. No novelty claim.

- `formal/FibonacciWeight.lean`: actual recurrence, actual reduction and orbit quotient, minimal period, fiber/orbit bridges, and complete weight identity.
- `formal/Checks.lean`: type and axiom checks for every named declaration.
- `formal/build/audit.json`: pinned clean rebuild receipt.
- `paper/main.tex`: paper source with the full argument and attribution.
- `discovery.md`: exact scope and source correspondence.
- `notes/review.md`: implementation self-review.
- `sources/`: immutable copies of the assigned MathDB source and arXiv v2, with hashes.

Rebuild from the workspace root:

```sh
python openai-proof-research/frontier/campaigns/2026-10-25/fibonacci-weight-lane/formal/rebuild.py
```

The script uses the preinstalled Lean 4.34.1 compiler and already-built pinned mathlib dependencies; it does not run Lake or modify dependency/source caches. Full dependency and tool paths can be overridden by its command-line options. The final theorem is `FibonacciWeight.fibonacci_weight_preservation`. Both source signs are covered by its arbitrary integer coefficient.
