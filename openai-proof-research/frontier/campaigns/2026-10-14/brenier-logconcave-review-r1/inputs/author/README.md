# fresh-analytic-discovery-r12

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0; code MIT.

Target (frozen in `original-scope.md`): extend the sharp `W_2^{1/3}`
stability of Brenier maps (openai/math entry 374, uniform convex source) to
every log-concave source with compact convex support, with an explicit
constant that does not depend on a lower density bound.

Outcome: `candidate.md` gives a proposed complete proof (status
`PROOF-CANDIDATE`, awaiting parent review; not counted, no self-PASS).

Files:

- `original-scope.md` — frozen target and exclusions.
- `literature-screen.md` — dated literature and operation screen.
- `source-contracts.md` — pinned files, blobs, reading extent, use of each label.
- `candidate.md` — statement, proof, validation, limits.
- `progress.md` — checkpoints.
- `experiments/` — two pure-Python sanity checks and their outputs (evidence only).
- `inputs/pinned/brenier/` — pinned source copies; `inputs/context/` — snapshots
  of the ledger, briefs, launch record and `upstream.json`.
- `verify.py` — read-only, fail-closed integrity verifier;
  `verify-receipt.json` — its recorded run.
- `inputs-manifest.json`, `outputs-manifest.json`, `seal.json`,
  `seal.sha256` (detached seal hash).

Verify with `PYTHONDONTWRITEBYTECODE=1 python3 -B verify.py` from this
directory (add `--with-experiments` to rerun the numerical checks).
