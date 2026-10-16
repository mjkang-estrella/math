# Fresh structural discovery round 16: B8C

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

**Status: `FULL_PROOF_CANDIDATE_B8C_AWAITING_INDEPENDENT_REVIEW`.**
There is no self-PASS, acceptance, count increase, manuscript, Lean
package, commit or staging.

Target (frozen in `original-scope.md`): for the complex rank-one
projectors X ⊂ R^8 (trace-one Hermitian 3x3 matrices, Frobenius metric),
diam X = √2 and the Borsuk number b(X) = 9.

Outcome: B8C is proved in `candidate.md`. Both parts are proved, and
the result is a confirmation, not a refutation. X attains Borsuk's
bound d + 1 = 9 with equality.

- Lower bound: a Hermitian odd extension combined with Borsuk–Ulam on S^8.
- Upper bound: the closed Voronoi cells of a small Weyl–Heisenberg-
  covariant perturbation of the Hesse SIC. Its covering overlap is
  strictly above the Bessel threshold 1/2, so no cell contains an
  orthogonal pair.

Source family 156 (openai/math fd4aeeb2…, Borsuk failure in dimension 9).
No source theorem is a proof input.

## Files

| path | role |
|---|---|
| original-scope.md | frozen target |
| candidate.md | full proof candidate |
| source-contracts.md | sources, reading extents, blob ids, dependencies |
| primary-comparison.md | comparison with the source and literature |
| progress.md | checkpoints C0–C6 |
| status.json | machine-readable status |
| tools/diagnose_b8c.py, diagnostics/ | floating-point diagnostic and its output (evidence only) |
| tools/authenticate_lr_r2.py | LR-r2 authenticator used before reliance |
| inputs/ | context snapshots, pinned sources, primary, records |
| unchanged-source-receipts.json | before/after hashes of the files read |
| verify.py | read-only identity verifier (needs an external seal hash) |
| manifest.json, seal.json | exact membership and detached seal |

Verify with `python3 verify.py --seal-sha256 <hash supplied outside this directory>`.
