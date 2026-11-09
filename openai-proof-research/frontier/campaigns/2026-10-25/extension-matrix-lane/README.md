# Two additional matrix outcomes

Both are complete counterexamples to distinct quantified MathDB source conjectures, outside the previous twenty IDs. Both reproduce mathematical counterexamples already posted by Shivam Patel; neither claims discovery or first formalization.

| MathDB | Package | Result | Pinned axiom audit |
|---|---|---|---|
| 372496 | `weak-majorization/` | Actual sorted eigenvalue weak majorization fails at exponent five, via trace -82 > -122 for explicit complex Hermitian 2-by-2 matrices | PASS, 18 declarations |
| 380287 | `coefficient-minor/` | Strict PD integer 3-by-3 triple has actual coefficient minor with a positive real root | PASS, 30 declarations |

Each package has `formal/<module>.lean`, `outcome.json`, `main.tex`, `PROOF.md`, `source.json`, and the pinned verifier's `build/audit.json`, including source SHA256 and axiom inventory. All local declarations compile warning-free. The complete source snapshots live in this lane's `sources/`; the relevant snapshot names and exact hashes are inventoried in each `source.json`. Preserve those snapshots when packaging the outcomes separately. No PDFs were authored; parent will compile and inspect the two `main.tex` files centrally.

The local compiler helper `compile.py` is for iterative checking only. The authoritative replay is the existing campaign `verify_outcome.py`, whose pinned dependencies and compiler checks have passed for each package.

Independent review is still required before counting. No git or shared campaign-index modifications were made by this lane.
