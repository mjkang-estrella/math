# Reproducing the MathDB 355956 dossier (DRAFT)

**Status.** Zero accepted credit. The campaign root alone accepts, and the campaign count of 5/20 beyond 39 is unchanged. MathDB 355701, the candidate that shares the author packet, is on root HOLD and is not part of this dossier.

## Claim

For q = 5^8 and d = 3, the only admissible r is 1. In every field with 5^8 elements, F_5 is a clique of GP(5^8, 3) but not a maximal clique. The extending vertex is x = 2θ + 4θ^2 + θ^3, where f(θ) = 0 for f = X^8 + X^7 + 2X^6 + 2.

This refutes Yip's conjecture: J. Algebraic Combin. 56 (2022), arXiv:2101.09652, Conjecture 1.4, which is also Algebr. Comb. 6(4) (2023), arXiv:2209.00864, Conjecture 1.1.

Lean endpoints:
- `MathDB355956.yip_conjecture_false : ¬ YipConjecture`
- `MathDB355956.yip_conjecture_SG_false : ¬ YipConjectureSG`

## External dependencies

**Required.**
- Python 3, standard library only.
- Linux `/proc`, rlimits and CPU affinity.
- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The `lean` and `leanchecker` sha256 hashes are listed in `pins.json`.
- Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, with its pinned dependencies and their prebuilt `.lake/build/lib/lean` oleans. `pins.json` records the full `lake-manifest.json` and the HEAD of every package, read from the `.git/HEAD` files without running git.

**Optional.**
- A user systemd manager (`systemd-run --user --scope`) for the extra MemoryMax=6G cgroup cap. Set `REPLAY_NO_SYSTEMD=1` to skip it.

**Not done.** Nothing is downloaded, repaired or rebuilt upstream.

## Fresh extraction and replay

```sh
python3 -I safe_extract.py source-only-proof.zip /absolute/path/to/NEW-directory
cd /absolute/path/to/NEW-directory
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

The two paths are examples from this machine. Point them at any installation with the pinned bytes.

**`safe_extract.py`.** It creates only a new destination and never overwrites or deletes anything. It rejects:
- absolute paths, `..` components and backslashes;
- symlinks and non-regular members;
- duplicate names.

**What `replay.py` does.**
1. It verifies the binary hashes and every entry of `source-manifest.json`.
2. It refuses to run if any `.olean`, `replay-receipts/` or `controls/` already exists. To repeat the replay, use another fresh extraction.
3. It builds `proof/Yip355956.lean` with `lean -j1 -DwarningAsError=true` and runs `leanchecker Yip355956`.
4. It runs the reviewer audit `proof/ReviewAudit.lean`, which covers all 40 constants stored in the module data of `Yip355956`, including auxiliary and generated ones. For each constant the audit checks:
   - its origin (re-checked);
   - its full type, printed with `pp.all`;
   - body presence via `value? true`;
   - that it is safe, non-partial, and not an axiom;
   - that its transitive axioms are a subset of {propext, Classical.choice, Quot.sound}.
5. It runs `proof/ReviewSanity.lean`, which re-states the endpoints and checks non-vacuity.
6. It runs the negative controls (listed below).
7. It runs `diagnostic.py`.

**Environment and caps.** Lean runs with HOME preserved and a minimal environment (`PATH=$LEAN_BIN:/usr/bin:/bin`, `LANG`, `LEAN_PATH`, `LEAN_NUM_THREADS=1`, `MALLOC_ARENA_MAX=2`). Each call gets:
- at most 2 CPUs;
- 120 s of CPU and 140 s of wall time;
- 64 GiB of address space;
- a 6 GiB guard on sampled private RSS (RssAnon + RssShmem of the process group, sampled every 50 ms);
- when available, a transient systemd scope with MemoryMax=6G, MemorySwapMax=0 and CPUQuota=200%.

**Outputs.** Every command, environment, exit code, elapsed time and peak (private and total) is written to `replay-receipts/*.receipt.json`. The summary is `replay-receipts/result.json`.

**Resource caveat (please read).** `import Mathlib` mmaps about 6–7 GB of read-only `.olean` files. Total VmRSS counts those clean, file-backed, shared pages, so it exceeds 6 GiB even though the process's private memory stays below 1 GiB. For that reason the kill criterion is private RSS, and total VmRSS is reported alongside it. Sampling at 50 ms does not guarantee catching transient peaks. A cgroup MemoryMax does not bound pages that are already cached and charged to another cgroup.

## Negative controls

Each control asserts only what it tests.

| Control | Expected result | What it shows |
|---|---|---|
| `control-certificate-verbatim` | exit 0 | Positive twin: the certificate of `cube_0`, extracted verbatim from the module, re-checks. |
| `negative-wrong-certificate` | exit 1, `ring failed` | The same certificate claimed for x − 1 instead of x − 0 is rejected by `linear_combination`. |
| `negative-wrong-endpoint` | exit 1, type mismatch | `yip_conjecture_false` does not inhabit `YipConjecture`. |
| `negative-sorry` | exit 1 | `sorry` is rejected under `warningAsError`. |
| `negative-forbidden-axiom` | exit 1, `forbidden axiom cheat` | The audit's axiom filter flags an added axiom. |
| `negative-malformed-olean` | non-zero exit, invalid header | `leanchecker` rejects a malformed `.olean`. This control tests only the header rejection. |

## Diagnostic

`diagnostic.py` uses only the standard library and is not a premise of the Lean theorem. It parses the Frobenius chain and the cube and inverse certificates from the Lean file and rechecks them with independent F_5[X]/(f) arithmetic. It also checks:
- the admissible r;
- the irreducibility of f, via the Frobenius orbit and gcd(f, P_4 − X) = 1;
- that x − a is a cube, via (x − a)^((q−1)/3) = 1;
- that F_5 ⊕ xF_5 is a 25-clique;
- that θ is primitive;
- that F_25 and F_625 are not cliques.

Finally, it counts all extension vertices with a discrete-log table, giving 960, none of which lies in F_625.

## Contents and provenance

**Proof files.**
- `proof/Yip355956.lean` is byte-identical to the author file (sha256 0ccf6655…ee9d7be).
- `proof/ReviewAudit.lean` and `proof/ReviewSanity.lean` are clearly labelled reviewer supplements. Nothing in the author module was edited.

**Sources.**
- `sources/355956.jsonl` is the exact raw MathDB line.
- The other files in `sources/` are byte-identical copies of the primary TeX and e-prints read. Their provenance is in `sources/RECEIPTS.json`.

**Manifests.**
- `source-manifest.json` hashes every member of the source package except itself.
- `dossier-manifest.json` hashes every member of the full dossier except itself.
- `archive-hashes.json` binds both ZIP files.

**Full dossier.** `full-dossier.zip` adds:
- the paper (`paper.pdf`, with its source `write_paper.py`) and the QA renders with their receipt;
- this lane's fresh-extraction replay receipts;
- the frozen-input bindings;
- verbatim copies of 355956-only evidence;
- labelled extracts of the joint review and adjudication files.

The full dossier excludes:
- 355701 material;
- the 117 MB incomplete proof dump of the technical review (referenced by hash only);
- oleans and upstream caches.

## Paper

`paper.pdf` is built with ReportLab 4.4.9 from `write_paper.py`:

```sh
python3 write_paper.py
```

The fonts are Liberation Serif and Mono, with Noto Sans Math as a fallback; their paths and hashes are in `paper-build.json`. No LaTeX engine was used, and no `.tex` transcription is supplied.

The pages were rendered with `pdftoppm -r 100 -png paper.pdf qa/page`, and every page was inspected individually; see `qa/receipt.json`.

The paper separates three kinds of content:
- Lean-certified content;
- results with ordinary proofs only (Propositions 3 and 4, and the irreducibility of f);
- computational diagnostics.

## Limits

**Trust.**
- The Lean kernel, the compiler and the prebuilt Mathlib oleans are trusted; there is no upstream rebuild.
- `leanchecker` comes from the same installation as `lean`.
- Statement fidelity rests on human reading.

**Novelty.** The literature search was bounded, and no worldwide priority is claimed. The following were not read:
- Yip's thesis;
- three citers of [1] listed by OpenAlex;
- the MathDB/Palomar comment and solution state (HTTP 403).

The source review's limits apply unchanged.

**Remaining steps.** The root's final replay, the paper review and acceptance are pending.
