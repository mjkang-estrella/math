# T298P independent scoped Lean review, recovery round 2

**PASS for scoped support; no required findings.** Read `review.md` for exact coverage, optional findings, counterexample assignments and analytic debts. This packet does not formalize the analytic theorem or claim acceptance/count credit.

Verify read-only using the independently supplied review MANIFEST SHA256:

```bash
python -B verify.py --anchor EXTERNAL_REVIEW_SHA256 --repo /path/to/openai-proof-research
```

The anchor must come from outside this packet. The verifier checks identities and recorded evidence; it does not run Lean. It also needs the original author packet and bound repository files. `binding.json` contains their exact identities. `verdict.json` is the machine-readable scoped verdict.

For fresh offline source compilation, from this review directory, with **new output directories outside the sealed packet**:

```bash
python -B copied-author/rebuild.py --output /var/tmp/NEW_T298P_AUTHOR_REPLAY --lean /path/to/lean-4.34.1-linux/bin/lean --cache /path/to/formal/.lake/packages
python -B audit.py --output /var/tmp/NEW_T298P_REVIEW_REPLAY --lean /path/to/lean-4.34.1-linux/bin/lean --cache /path/to/formal/.lake/packages
```

`fresh-build/` records an independent execution of the author runner. `independent-build/` records the independent runner's fresh copied support/control/test builds, all 18 theorem types/axioms, and five expected mutation rejections. Its five negative `.lean` files deliberately fail; they are test inputs, not proved results. `Independent.lean` contains ten successful reviewer examples. `development-attempt-1/` preserves a rejected reviewer fixture diagnostic, explained in the review.

Lean/compiler runtime and pinned pre-existing dependency oleans remain trusted; mathlib was not rebuilt. Executable SHA256 and dependency revisions are recorded in both receipts. No network or cache installation was used. Code is MIT under `LICENSE-CODE.txt`; review prose follows the project author's CC BY 4.0 convention. No frozen source or shared index was changed, and nothing was staged or committed.
