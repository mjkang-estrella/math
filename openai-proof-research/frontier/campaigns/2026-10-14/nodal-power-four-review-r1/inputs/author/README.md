# fresh-analytic-discovery-r13

Author: Myeongjin Kang (no affiliation). Prose CC BY 4.0; code MIT (see RIGHTS.md).

Target (frozen in `original-scope.md`): Theorem T4, a fixed power-law
violation of Yau's smooth nodal upper bound in dimension four, on
S^3 x S^1. Status: PROOF-CANDIDATE, not self-passed, not counted.

* `candidate.md`: statement, architecture, full proofs of the new
  three-dimensional envelope amplification (Lemmas 3.1, 5.1, 6.1, 7.1,
  7.2, Proposition 8.1), the base-S^3 transfer table, the proof of T4,
  and checkable risk points.
* `literature-screen.md`: family screening, operation-level comparison
  with the pinned sources, and the dated external screen.
* `source-contracts.md`, `git-identities.json`: pinned sources, labels,
  lines, and Git blob identities (31 files).
* `progress.md`: work log. `status.json`: machine-readable status.
* `inputs/pinned/`: private third-party copies. `inputs/context/`:
  read-only snapshots of project files.
* `inputs-manifest.json`, `outputs-manifest.json`, `seal.json`,
  `seal.sha256`, `verify.py`, `verify-receipt.json`: integrity only.

Verify (read-only): `python3 -B verify.py`. Passing means the files are
intact. It does not establish the mathematics or its novelty.
