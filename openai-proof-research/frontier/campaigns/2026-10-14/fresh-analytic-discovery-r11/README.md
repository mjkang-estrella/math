# Fresh analytic discovery r11: sextic Salem Bernoulli convolution

Author: Myeongjin Kang (no affiliation). Prose CC BY 4.0, code MIT; see
RIGHTS.md. Status: **UNRESOLVED**, not counted, no self-PASS.

Target (frozen in `original-scope.md`): singularity of nu_{1/beta_6}, where
beta_6 = 1.40126836794 is the sextic Salem root of x^6 - x^4 - x^3 - x^2 + 1.
Source family 153 (Bernoulli convolutions, pinned openai/math fd4aeeb).

Result: a proved finite seed criterion for Salem numbers of every degree
(Theorem S, Corollary S'), its sharpness up to constants (Proposition O1), and
action doubling for product multipliers (Proposition O2). The target reduces
to one seed problem, which remains open. Degree six is critical for the pinned
multiplier mechanism.

| file | role |
|---|---|
| original-scope.md | frozen scope (read-only, SHA-256 in status.json) |
| candidate.md | statements, proofs, obstacle, novelty limits |
| literature-screen.md | primary-literature comparison |
| source-contracts.md | pinned files, blob SHA-1s, labels relied on |
| git-identities.json | upstream pin and observed local Git state |
| progress.md, status.json | checkpoints and final status |
| scripts/ | evidence-only numerics (double precision) |
| evidence/ | raw outputs of the scripts |
| verify.py | read-only verifier (writes nothing) |
| inputs-manifest.json, outputs-manifest.json | size and SHA-256 manifests |
| verify-receipt.json | recorded verifier run |
| seal.json | binds both manifests and the receipt; its SHA-256 is reported externally and in seal.sha256 |

Run: `python3 -B verify.py` (add `--with-search` to rerun the seeded search,
about 25 seconds). Python 3 standard library only.
