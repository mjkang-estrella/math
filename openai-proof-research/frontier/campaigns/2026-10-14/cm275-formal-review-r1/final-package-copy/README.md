# CM275 scoped Lean support

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT.

This packet supplies **30 Lean theorems, 36 public support declarations** for finite sampling, algebraic symmetry projection and conditional scalar verification margins. It is an implementation submitted for independent review. It does not formalize the full CM275 continuum membership or QMA-completeness theorem, give an independent gate verdict, or change the campaign count.

The unchanged human theorem concerns every distinct rational unit-nuclear configuration, every positive unary electron count, the full spinful antisymmetric Coulomb form on all of space, and the stated inverse-input-length gap. It permits arbitrarily small nuclear separations, exponentially distant nuclei and unbound/nonattained infima. Source hardness is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No supplied basis, binding, selected spin sector or efficient state preparation is assumed in that theorem. The scoped support does not prove these analytic or complexity assertions.

`coverage.json` maps every public declaration to its exact role and limitations; `CM275.lean` and `validation/sealed-build/types-axioms.stdout` are the authoritative formal statements. The support proves normalized finite additive-character Parseval from actual character orthogonality, unit-modulus coefficient-phase invariance, discrete translation, ZMod character injection and centered-band nonaliasing. It constructs character-twisted averaging from an actual representation, proves its eigen range, fixed vectors, idempotence and commuting-map property, and instantiates the permutation sign character. This is an **algebraic projector**, with no formal claim of orthogonality or self-adjointness. Conditional scalar results combine four error budgets and preserve the failed validity-test weight in soundness.

The implementation uses mathlib's existing finite-character orthogonality and invariant-average theorems explicitly; it is not a new proof of those library results. The human proof's analytic estimates and physical realizations remain outside Lean. The implementer previously authored the CM275 contribution review, but not the candidate or independent full proof review. A separate reviewer is required for this artifact.

## Reproduction

First authenticate this exact packet using the manifest SHA256 supplied separately by the parent/release receipt:

```sh
python -B verify.py --anchor EXTERNALLY_SUPPLIED_SHA256
```

The verifier is read-only and checks exact payload/directory membership and hashes. It rejects extra/missing/changed files, symlinks and wrong anchors. It checks recorded build/coverage/source consistency; it does not rerun Lean or certify the full theorem. `validation/integrity-controls.json` records positive and negative controls. Do not use a digest read from the same untrusted manifest as an external anchor.

For a fresh source build, use a **working copy** of this packet (the build writes logs, so the result is no longer the exact sealed inventory). Invoke:

```sh
python -B rebuild.py --lean /path/to/lean-4.34.1/bin/lean \
  --cache /path/to/pinned/.lake/packages --output .replays/independent
```

The default compiler is `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`. The default read-only cache is the sibling `formal/.lake/packages`. Portable copies must supply these options. The compiler must report commit `5045d0056413266e57c625dcd7c365b10e377c52`; the mathlib checkout must be `d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine dependency identities are in `lake-manifest.json`. Dependencies and their precompiled objects must already be installed; this command makes no network request. The lock and toolchain preserve the established project provenance, while the package is named `cm275_scoped_support` in `lakefile.toml`.

`rebuild.py` checks all dependency Git revisions and absence of tracked changes, copies only the four own Lean source/audit files to a new temporary directory, and compiles its own modules there. It never uses a previously built CM275 object. It runs exact declaration type and axiom checks, 14 proved semantic-control theorems, nine deliberately false mathematical proof goals, and four actual subprocess-wrapper controls. The wrapper rejects `SOME FAIL` printed by a zero-exit child and a zero-exit stderr error, as well as a nonzero exit; it accepts a clean child. The runner requires the exact nine mutant filenames and derives counts from executed rows; missing-one and empty-directory controls reject before compilation. The nine mutants are expected compile failures, not production proofs. Their logs show mathematical false-goal rejection rather than parser or missing-import errors. No `sorry`, conclusion axiom, `native_decide` or unsafe command is permitted in the support/control sources. The only observed transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.

The completed clean build is retained under `validation/sealed-build/`; no compiled dependency or own `.olean` is redistributed. Early elaboration errors were repaired before this clean build. See `reading-and-provenance.md` for actual reading bounds and helper origins. The source/dependency identities authenticate bytes, not mathematical correctness. Neither an external peer-review claim nor worldwide priority is asserted.
