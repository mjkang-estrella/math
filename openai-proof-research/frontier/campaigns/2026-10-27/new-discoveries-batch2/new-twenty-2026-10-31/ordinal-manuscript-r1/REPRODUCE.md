# Reproducing the MathDB 366371 dossier (DRAFT)

**Status.** Zero accepted credit. The campaign root alone accepts, and the campaign count of 7/20 beyond 39 is unchanged. MathDB 366834 (the caterpillar candidate from the same author lane) is on root HOLD and is not part of this dossier.

## Claim

There is a six-point ordinal space (X, δ) whose identity enumeration has the majorization property of Keller–Petrov Definition 7.1 (for every chain length k, with repeats and permutations) but which does not embed in ℝ¹. This refutes Conjecture 7.4 of K. Keller and E. Petrov, *Ordinal spaces*, Acta Math. Hungar. 160 (2020) 119–152 (arXiv:2412.17391v1).

Lean endpoints (module `OrdinalLine`):
- `OrdinalSpaces366371.not_majorizationConjecture : ¬ MajorizationConjecture`
- `OrdinalSpaces366371.witness : IsOrdinalSpace δW ∧ Function.Bijective (id : Fin 6 → Fin 6) ∧ HasMajorization δW id ∧ ¬ EmbeddableInLine δW`

## External dependencies

**Required.**
- Python 3, standard library only.
- Linux `/proc`, rlimits and CPU affinity.
- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The `lean` and `leanchecker` sha256 hashes are in `pins.json`.
- Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 with its pinned dependencies and their prebuilt `.lake/build/lib/lean` oleans. `pins.json` records the full `lake-manifest.json` and every package HEAD, read from `.git/HEAD` files without running git.

**Optional.** A user systemd manager (`systemd-run --user --scope`) for the extra MemoryMax=6G cgroup cap. Set `REPLAY_NO_SYSTEMD=1` to skip it.

Nothing is downloaded, repaired or rebuilt upstream.

## Fresh extraction and replay

```sh
python3 -I safe_extract.py source-only-proof.zip /absolute/path/to/NEW-directory
cd /absolute/path/to/NEW-directory
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

The two paths are this machine's; point them at any installation with the pinned bytes.

**`safe_extract.py`** creates only a new destination and never overwrites or deletes. It rejects absolute paths, `..` components, backslashes, symlinks, non-regular members and duplicate names.

**`replay.py`**:
1. verifies the binary hashes, every entry of `source-manifest.json`, and that `proof/OrdinalLine.lean` has the pinned literal hash `da892a4d…cec7703f`;
2. refuses to run if any `.olean`, `replay-receipts/` or `controls/` already exists (use another fresh extraction to repeat);
3. builds `proof/OrdinalLine.lean` with `lean -j1 -DwarningAsError=true` (the log must be empty) and runs `leanchecker OrdinalLine`;
4. runs the reviewer audit `proof/ReviewAudit.lean` over all 95 constants stored in the module data of `OrdinalLine` (23 definitions, 69 theorems, and the structure `IsOrdinalSpace` with its constructor and recursor), cross-checked against an origin scan of the whole environment. For each constant: origin, kind, full type (`pp.all`), body presence via `value? true` (required for every definition and theorem), no axiom/opaque/quot kinds, not unsafe/partial/implemented_by/extern, no `sorry` in any value, and transitive axioms ⊆ {propext, Classical.choice, Quot.sound};
5. runs `proof/ReviewSanity.lean`: prints the definitions, re-states both endpoints, checks non-vacuity (concrete `Prec` and `Sim` instances, one needing a transposition; a majorization conclusion; `EmbeddableInLine` satisfiable on two points) and prints `#print axioms` for both endpoints;
6. runs the negative controls below;
7. runs `diagnostic.py` (corroboration only).

The driver creates only `replay-receipts/`, `controls/` and `proof/OrdinalLine.{olean,ilean}` in the extraction and deletes nothing.

**Caps per call.** At most 2 CPUs; 120 s CPU; 140 s wall; 64 GiB address space; `MALLOC_ARENA_MAX=2`; a 6 GiB guard on sampled private RSS (RssAnon + RssShmem of the process group, every 50 ms), with total VmRSS reported; and, when available, a transient systemd scope with MemoryMax=6G, MemorySwapMax=0, CPUQuota=200%. Lean runs with a minimal environment (HOME, `PATH=$LEAN_BIN:/usr/bin:/bin`, `LANG`, `LEAN_PATH`, `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=2`).

**Outputs.** `replay-receipts/*.receipt.json` (command, environment, exit, wall time, private and total peaks) and `replay-receipts/result.json`.

**Resource caveat.** Mathlib oleans are mmapped read-only; total VmRSS counts those clean shared pages, so the kill criterion is private RSS. 50 ms sampling may miss transient peaks; a cgroup MemoryMax does not bound page cache already charged elsewhere.

## Negative controls

Each control asserts only what it tests.

| Control | Expected | What it shows |
|---|---|---|
| `control-core-verbatim` | exit 0, empty log | Positive twin: the contradiction lemma `core`, extracted verbatim, re-checks (validates the harness). |
| `negative-dropped-comparison` | exit 1, `linarith failed` | Without the fifth comparison D(3,5) < D(0,2), `linarith` finds no contradiction: that comparison is load-bearing in the certificate. |
| `control-prefix-verbatim` | exit 0, empty log | Positive twin: the module prefix up to and including `finite_check` re-checks standalone. |
| `negative-perturbed-table` | exit 1, `is false`, single error at the `decide +kernel` line of `finite_check` | Exchanging the values of {0,3} and {0,4} makes the kernel finite check evaluate to false: the check is not vacuous. (`diagnostic.py` independently finds 12 violating reduced pairs for this table.) |
| `negative-wrong-endpoint` | exit 1, type mismatch | `not_majorizationConjecture` does not inhabit `MajorizationConjecture`. |
| `negative-sorry` | exit 1, `sorry` | `sorry` is rejected under `warningAsError`. |
| `negative-forbidden-axiom` | exit 1, `forbidden axiom cheat` | The audit's axiom filter flags an added axiom. |
| `negative-malformed-olean` | non-zero, invalid header | `leanchecker` rejects a malformed `.olean` (tests only header rejection). |

## Diagnostic

`diagnostic.py` (standard library) parses the table from the Lean file and checks: the table is a symmetric bijection of the 15 pairs onto 1..15; axioms (i)–(vii) over all 6⁶ sextuples; Definition 7.1 literally for k = 1..4 with repeats and all permutations, under both readings of "but not (7.4)" (441, 3136, 15876, 63504 chain pairs; 0 violations); the 63 × 63 reduced finite check for t = 1..15; that threshold-count dominance equals sorted-value dominance on every reduced pair; the forced order and the five comparisons with gap coefficients [1, 2, 2, 2, 1] on both sides; and that the perturbed control table fails. It is not a premise of the Lean theorem.

## Contents and provenance

- `proof/OrdinalLine.lean`: byte-identical to `expanded-corpus-r61/formal/OrdinalLine.lean` (sha256 da892a4df78aa6e737bc6a65bf9f39be0114661d60d0dafb25e4624cfec7703f). Its strict build reproduces the olean sha256 cddbfa4e59da9e31a02c6a32ca0285118ffac456059129408e0399418c84ba12 reported by the author lane and the independent review.
- `proof/ReviewAudit.lean`, `proof/ReviewSanity.lean`: clearly labelled reviewer supplements written in this lane; nothing in the author module was edited.
- `sources/366371.jsonl`: the exact raw MathDB line. `sources/2412.17391*`: the arXiv HTML, text rendering and abstract page with fetch receipts; provenance and hashes in `sources/RECEIPTS.json`.
- `PROOF.md`: the ordinary proof, correspondence table and limitations.
- `source-manifest.json` hashes every member of the source package except itself; `dossier-manifest.json` hashes every member of the full dossier except itself; `archive-hashes.json` binds both ZIPs.

The **full dossier** (`full-dossier.zip`) adds the paper (`paper.pdf`, its source `write_paper.py`, build record), QA renders and receipt, this lane's fresh-extraction replay receipts, frozen-input bindings, verbatim copies of 366371-only author and review evidence, and labelled 366371-only extracts of the joint review and root adjudication. It excludes all 366834 material, oleans and upstream caches.

## Limits

- Trusted: the Lean kernel and compiler, the prebuilt Mathlib oleans (no upstream rebuild), `leanchecker` from the same installation. Statement fidelity rests on human reading of arXiv v1.
- The published 2020 journal text was not read; its Conjecture 7.4 is assumed identical to arXiv v1.
- Bounded literature search; no priority claim.
- The n = 5 and n = 6 scans of the author lane are diagnostics only; no minimality claim.
