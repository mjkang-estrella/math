# MathDB 374728: complete reverse-mex counterexample

S={3,6,10} satisfies the source's condition(a) nonvacuously but fails reverse mex at heap5. This verifies Shivam Patel's existing posted base example, not a new discovery or the posted infinite scaling extension.

`formal/ReverseMex.lean` proves all45 local declarations with pinned Lean4.34.1. The source move-set/image bridge, mex minimality, exact recurrence for every heap, uniqueness, eventual period, source piecewise reduction, all positive-distance minima, full P-position classification (including prefix0), universal condition(a), and reverse-mex failure are certified. `build/audit.json` is PASS with standard logical axioms only.

`main.tex` is the complete written paper, `PROOF.md` explains the formal/source bridges, `source.json` inventories primary/post provenance and hashes, and `sources/` contains the full exact primary manuscript and current MathDB API response. `outcome.json` gives the release manifest. Parent handles PDF production and independent review; no PDF was authored here.

Replay from repository root:

```
python3 openai-proof-research/frontier/campaigns/2026-10-25/thirty-proof-campaign/verify_outcome.py openai-proof-research/frontier/campaigns/2026-10-25/extension-nim-counter
```
