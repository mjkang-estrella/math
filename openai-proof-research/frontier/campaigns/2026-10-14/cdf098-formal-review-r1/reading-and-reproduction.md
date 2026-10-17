# Reading, provenance, reproduction and limits

The reviewer authored cdf098-manuscript-r1, not CDFLocal or the implementation runners. The implementer previously authored cdf098-contribution-r1. Neither relationship is concealed. This is an independent implementation audit, not an independent new proof or contribution review. The prior manuscript's description was not used as a substitute for declaration inspection.

AGENTS and original-scope.md were read in full again for this assignment. The complete candidate and prior proof/contribution reports had been read in the immediately preceding manuscript implementation, at the unchanged anchors; their mathematical verdicts are context, not Lean certification. All 343 lines of exact final CDFLocal.lean, coverage.json, source-contracts.json, README and the complete support type/axiom report were read immediately before this audit and remain unchanged at the supplied hashes. During this audit the proofs and their hypotheses were independently reassessed declaration by declaration. Controls.lean, Checks.lean, ControlChecks.lean, rebuild.py, checked_run.py, mutations.py, semantic_checks.py and verify.py were read completely before or during their use. Every fresh mutant failure output and the full fresh control type/axiom output were read. Fresh support type/axiom bytes were checked identical to the fully read authenticated report. No truncated output is counted as full reading.

No new primary-literature search or reading was necessary for these internal formal interfaces. Earlier manuscript/source reading is recorded in the sealed manuscript map and is not silently claimed anew. The stipulated upstream nonembedding proof, unrelated source companions and mathlib theorem implementations were not audited here. Coverage is mathematical interface semantics and reproducible kernel checking, not a source-theorem truth check or novelty assessment.

All writes were confined to cdf098-formal-review-r1. The 75 authenticated formal payloads were copied into private/formal without copying external .replays or transient builds. The baseline copy is retained byte-for-byte. New local .replays/auditor-build and .replays/auditor-mutations are this review's execution evidence and included in the outer review inventory. The integrity-negative temporary copy was removed after restoring and rechecking it. No .olean remains in the review.

Reproduce in a WORKING COPY of this review directory, preserving the sealed original. The pinned Lean compiler and read-only dependency cache must be available. Use new output labels to avoid overwriting retained evidence:

```sh
python3 -B private/formal/rebuild.py --cache /absolute/path/to/formal/.lake/packages --output .replays/another-build
python3 -B private/formal/mutations.py --cache /absolute/path/to/formal/.lake/packages --output .replays/another-mutation-run
python3 -B audit_controls.py
```

Compiler defaults to /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean; --lean can select an equivalent pinned installation. The copied runner's default cache path is not suitable for this nested review copy, so --cache is required as shown. Replaying mutates the working copy and invalidates its old review seal. No dependency package compilation or network fetch is needed.

Read-only identity check, using the external seal hash delivered by the reviewer:

```sh
python3 -I verify.py --seal-sha256 EXTERNAL_REVIEW_SEAL_SHA256
```

This authenticates the outer exact inventory, copied original formal baseline, externally frozen formal and source/review identities, fresh build/source/type/axiom links and negative-control receipts. It executes no mathematical program or external verifier. The audit hook denies writes, subprocesses and network access. Identity is not a fresh proof run. The required compiler/runtime/dependency-cache trust is stated in review.md and checks/cache-trust.json.

Rights: Myeongjin Kang, no affiliation. Original review prose CC BY 4.0. Original review code MIT. Copied original implementation files retain their recorded CC BY/MIT licenses and provenance. The contained candidate/review snapshots are private evidence, not a public redistribution or new license for third-party material. No publication or campaign-count change.

The read-only review verifier adapts the author's original integrity helper from cdf098-manuscript-r1/support/verify.py; it adds this audit's fresh declaration, axiom, mutation and control linkages. No implementation source was repaired or edited.
