# Arithmetic-ratio lane: two complete source statements

**Complete:** MathDB **375256** and **375257**, respectively Conjectures 3 and 9
of S. I. Dimitrov, *Lower bounds on expressions depending on the functions
φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1.

The proofs cover **every integer n ≥ 2 and k ≥ 1**, including the actual
arithmetic-function bridge. They are formal verifications of prior posted
arguments by **Shivam Patel (20 August 2026)**, not novelty claims. No equality
classification is claimed. There are two source-question outcomes, not 37
outcomes corresponding to the local Lean declarations. No campaign ledger
or other shared file has been changed.

## Files

- `formal/ArithmeticRatios.lean`: arithmetic bridge, Euler-product equivalence,
  homogeneity, and exact final theorems `mathdb_375256` and `mathdb_375257`.
- `formal/RealRatios.lean`: parent-provided, unchanged real polynomial certificates.
- `formal/Checks.lean`: statements and axiom reports for all 37 local declarations.
- `main.tex` and `output/pdf/main.pdf`: complete three-page proof note.
- `review.md`: implementation self-review, including the source metadata error.
- `provenance.json`: source locations, snapshot hashes, attribution, and limitations.
- `verification.json`, `build.log`, `audit.log`: successful formal validation.
- `sources/`: exact MathDB snapshots, original arXiv TeX archive/extraction and HTML,
  plus the two erroneous older-reference targets for auditability.

## Reproduce

From this directory:

```sh
bash check.sh
python3 audit.py
bash build_paper.sh
```

`check.sh` uses Lean **4.34.1** and the existing pinned packages under
`../../2026-10-14/formal/.lake/packages`; warnings are errors. The mathlib revision
is `d13f23b723b8a846827a245b89c10fc7d3f11612` (see `pins.json`).

`audit.py` also concatenates the two Lean source texts and replays them through
`lean --stdin`, importing only Mathlib and excluding local compiled modules
from `LEAN_PATH`. It checks every local declaration's axiom report against
`{propext, Classical.choice, Quot.sound}`. It does not use `sorry`, new axioms,
`native_decide`, or an oracle asserting either conjecture.

`build_paper.sh` uses the locally available Tectonic binary and this lane's own
cache. The latest PDF has three pages, no TeX errors, unresolved references, or
overfull boxes; all three page images were inspected. The original sources
retain their authors' rights; their inclusion here does not grant a publication
or redistribution license.

## Exact semantic coverage

`Nat.totient` is mathlib's count of coprime residues. `sigma` is mathlib's
`ArithmeticFunction.sigma 1`, proved equal to the sum of all positive divisors.
`psi` is the primary paper's integral prime-factor product. For n ≠ 0,
`psi_euler_product` also proves ψ(n) = n ∏(1+1/p). `psi_one` handles the empty
product. The product-defined value at n = 0 is irrelevant: all final statements
require n ≥ 2.

The bridge proves 0 < φ(n)^k ≤ (n−1)^k < (n+1)^k ≤ ψ(n)^k ≤ σ(n)^k.
The real bounds are then applied to x/y, a/b, z/y. Both homogeneity identities
and both source right-hand-side rewrites are proved in Lean. No arithmetic
comparison is left as a hypothesis of the final theorems.

**Provenance correction:** The 375256 snapshot claims that arXiv:2401.09497 and
arXiv:1712.08666 are older sources of this conjecture. Their actual v1 source
archives are unrelated papers (weakly consecutive sequences; Euler-number
periodicity). Do not propagate the snapshot's asserted 2017 first-stated year
or its “three papers” claim. The exact 2026 primary statements are verified.
