# r71: approximate PPT route, unresolved full target

The unchanged T101G69 target remains unresolved. This packet is supporting author work with **no nomination and no count change**. The original freeze is preserved byte-identically in scope.md. No files in r69/r70 or shared campaign indexes were changed.

- [ppt-repair-obstructions.md](ppt-repair-obstructions.md) computes the partial-transpose spectrum of the paid simplex family and proves a two-dimensional lower bound against quadratic-trace positive-addition repair. Neither is a target counterexample.
- [separable-interface.md](separable-interface.md) proves the conditional constant-400 lifting from a short real separable quartic with exact marginal. It credits r69 polar compression and proves that the missing repair is equivalent up to constants to the full target.
- [attempts-and-primary-comparison.md](attempts-and-primary-comparison.md) explains which exact low-rank PPT hypotheses were actually read and where each attempted repair stops.
- [reading-limits.md](reading-limits.md) and source-receipts.json separate bounded source reading, retained private source bytes, paid comparisons and original deductions.

check_exact.py uses standard-library exact rational arithmetic. It verifies finite index/spectrum examples and the two-dimensional residual polynomials; the universal claims are supported by the written proofs, not by finite tests. verify.py is read-only and requires an externally supplied MANIFEST.json SHA256. It checks flat public membership, regular single-link files, byte identities, exact diagnostic output, and optionally retained private source identities. The local MANIFEST.sha256 is a convenience copy, not its own trust anchor.

Usage, with the digest independently supplied in the final handoff:

```sh
python -B verify.py --expected-manifest-sha256 EXTERNAL_DIGEST --check-private
```

The temporary-fixture negative controls test rejection of corrupted/missing payloads, unexpected directories, symlinks, hardlinks, a changed manifest, and a wrong external digest. They are integrity checks and are not an independent mathematical review. There are no uploads, source-truth audits, subagent reviews, staging or commits in this branch.
