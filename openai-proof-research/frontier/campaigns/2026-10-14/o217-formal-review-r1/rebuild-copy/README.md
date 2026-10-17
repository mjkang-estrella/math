# O217 scoped Lean support

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. This is an implementation packet submitted for independent audit, not an independent proof verdict or campaign acceptance.

The packet proves **28 Lean theorems across 43 public support declarations**. It constructs the finite Ising vertex flip, derives the Hamiltonian identity and equality of the actual exponential partition sums and log partitions, proves smoothness of the coordinate log partition and oddness of its deleted cubic derivative. The oddness also holds for observables of that actual log partition, including the square observable and scaled tests. Further support proves the exact square-Taylor identity, its fourth-order scalar bound from lower-order remainders, the noncircular quadratic bootstrap with explicit constant, its centered-variance correction, and both finite-size edge-count cancellations.

This is **not a formalization of the full O217 probability theorem**. Product laws, moment cancellation, bounded cumulants/mixed derivatives, Taylor's theorem supplying the scalar hypotheses, Lindeberg comparison, deleted-coordinate restoration, the finite hybrid maximum, and the source Gaussian law/weak-limit transfer remain in the adopted human proof. In particular the bootstrap inequality is a premise of the scalar bootstrap theorem; its probabilistic derivation is not claimed formalized. `coverage.json` maps every declaration and lists all omissions. Exact types and all `#print axioms` reports are in `validation/sealed-build/types-axioms.stdout`.

`Edge n` is the subtype of `Fin n × Fin n` consisting of `(i,j)` with `i<j`. Adding one to each vertex label identifies this with the manuscript's `1≤i<j≤n`; there are no diagonal edges, repeated ordered copies, or factor-of-two convention changes. Boolean spins map to ±1. The Hamiltonian sum omits q, and `partitionSum q` inserts q into its exponential, matching q=β/√n. The counting spin prior and zero field are explicit.

`logFam_contDiff` proves smoothness to every finite order of the actual one-coordinate family. The general derivative sign lemma also respects mathlib's total derivative convention (zero at nondifferentiability), so the arbitrary-observable oddness theorem needs no regularity hypothesis. Quantitative derivatives or C6 composition estimates are not obtained from that sign identity.

The unchanged human target permits independent nonidentical centered variance-one couplings with uniformly bounded fourth moments and unrestricted third moments. Its finite-size comparisons hold for fixed β>0; its own-centered/own-standardized all-integer limit and exact variance prefactor at fixed β>1 inherit the stipulated pinned Gaussian source. No fifth/sixth moments, symmetry, all-moment transfer, or critical-window extension are inserted here. This packet creates no second contribution for the technical variance bridge or the inherited Gaussian consequence.

## Reproduction

Authenticate using the SHA-256 supplied separately by the parent or release receipt:

```sh
python3 -B verify.py --anchor EXTERNALLY_SUPPLIED_SHA256
```

The read-only verifier checks exact file and directory inventory, hashes, build/source/coverage consistency and recorded scope. It requires an externally supplied anchor and rejects altered, extra, missing or symlinked payloads. It does not compile Lean or certify the human theorem. `validation/integrity-controls.json` records actual controls of this verifier on an isolated pre-seal fixture, including a wrong anchor. Do not authenticate a package with an anchor obtained from that same untrusted package.

To rebuild, first make a working copy, because build logs change the sealed inventory:

```sh
python3 -B rebuild.py --lean /path/to/lean-4.34.1/bin/lean \
  --cache /path/to/pinned/.lake/packages --output .replays/independent
```

Defaults use the installed Lean under `dlp-research/.tools/lean-4.34.1-linux/bin/lean` and the sibling `formal/.lake/packages`. The runner requires Lean 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52` and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, checking every locked dependency revision and tracked cleanliness. It reads cached dependency objects without modifying them, copies only the four own Lean source/audit files into a fresh temporary directory, and builds its own objects there. Previously compiled O217 objects are never reused. No network is used.

The clean build has no compiler warnings and accepts only the standard transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. It compiles eight proved semantic-control theorems, rejects five deliberately false Lean proof goals (wrong gauge sign, dropped square term, invalid bootstrap constant, negative-constant domain, dropped centering term), and executes four subprocess-wrapper controls. In particular, an exit-zero child printing `SOME FAIL` is rejected. False goals fail with `⊢ False`, not broken imports or syntax. These controls detect concrete mistakes; they are not an independent proof review or exhaustive test suite.

The interrupted predecessor implementation and subsequent repair are disclosed in `reading-and-provenance.md` and the retained transition inventory. Third-party source bodies remain in the private author packet; no new redistribution of those bodies occurs here. All author and review packets were kept immutable.
