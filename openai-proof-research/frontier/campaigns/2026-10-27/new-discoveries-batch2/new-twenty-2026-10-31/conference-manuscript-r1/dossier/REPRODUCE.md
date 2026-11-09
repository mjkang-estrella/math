# Reproducing the MathDB 324342 dossier

Run every command from the root of the extracted dossier: the directory that contains `PROOF.md`, `paper/`, `lean/` and `tools/`. Run commands one at a time. The lane wrapped each call in these caps:

- 2 CPUs;
- 120 s of CPU time and 140 s of wall time;
- 2 GiB address space;
- `MALLOC_ARENA_MAX=2`.

Always invoke Python as `python3 -I -B`.

## 1. Ordinary check, no Lean (Python stdlib only)

    python3 -I -B tools/check_witness.py lean/324342-replay-fit-source.zip out-witness.json

The script reads `ConferenceMDS324342.lean` from inside the ZIP, in memory and without extracting it. It checks:

- **Conference properties:** W has entries in {0, ±1}, zero diagonal, Wᵀ = −W, 19 nonzeros in every row and column, and W Wᵀ = 19 I.
- **Construction:** W equals H − I for the Goethals–Seidel array, and the periodic autocorrelation sums are 0.
- **Rank:** rank 10 mod 19, by fresh Gaussian elimination.
- **Certificates:** WWᵀ ≡ 0 (mod 19), A₀B₀ = B₀A₀ = I, and every row is D times rows 0–9.
- **Codeword:** c = xW mod 19 has weight 9, with support {5, 8, 9, 10, 12, 14, 15, 16, 17}.
- **Singleton bound:** the Singleton value is 11.
- **Arasu–Gulliver congruences:** they have no solutions mod 19.

It exits with 0 only if every check passes. The lane's output is `data/witness-check.json`.

## 2. The paper

    python3 -I -B paper/build_paper.py paper.pdf <REPORTLAB_DIR>

The build needs the following:

- **reportlab 5.1.0.** It is pure Python. The lane used a hash-identical copy of the earlier lanes' reportlab 5.1.0 tree (`receipts/rldeps.sha256` in the full dossier).
- **Pillow.** The system Pillow 12.3.0 for Python 3.15 was used.
- **Fonts.** Liberation Serif/Mono, Noto Sans Math and Symbola, all under `/usr/share/fonts`.

Before typesetting, the builder checks that the printed matrix W, the inverse B₀, the vector x, the vector xW, the codeword c and its support equal the data in the Lean packet. It aborts otherwise.

The output is deterministic (`invariant=1`). Building from the extracted source ZIP reproduces `conference-324342-draft.pdf` byte for byte; see `receipts/source-zip-verification.json` in the full dossier.

## 3. Lean replay (not run by this lane)

The packet is `lean/324342-replay-fit-source.zip`, sha256 `c6977a39d3f5aa81122c6ad9c2d374bcadc281dccf577208fbda31eac2e1a00f`. The files in `lean/packet/` are its four members, byte-identical.

The pins are in `lean/pins.json`:

- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52;
- Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, plus the listed package revisions.

Set `LEAN_PATH` to a fresh build directory followed by the `.lake/build/lib/lean` directories of the pinned packages. Then, in a fresh, safely extracted copy of the ZIP:

    for m in ConferenceMDS324342 Controls Audit MetadataAudit; do
      lean -j1 -M3500 -DwarningAsError=true -o "$BUILD/$m.olean" "$m.lean" || exit 1
      leanchecker "$m" || exit 1
    done

Expected results:

- every call exits with 0;
- `Audit` prints `AUDIT declarations=90 disallowed=0`;
- `MetadataAudit` prints `METADATA declarations=116 forbidden=0`;
- `#print axioms ConferenceMDS.conjecture5_false` gives `[propext, Classical.choice, Quot.sound]`.

The root's replay driver is `receipts/root-replay/rootcheck-replay.sh`, and its logs are in `receipts/root-replay/logs/`. Peak RSS was 2.93 GB and the longest call took 48.8 s.

Prebuilt Mathlib objects are trusted. The leanchecker runs recheck only the local modules.

## 4. MathDB literal

`mathdb/324342.raw.jsonl` is line 3870 of `mathdb-normalized-chunk-0002.jsonl` (chunk sha256 `d944c503…ea0a`). It hashes to:

- sha256 `73a0bb42…1342` without the newline;
- sha256 `12a701a2…c55f` with the newline.

`mathdb/mathdb-binding.json` records both hashes in full.

## 5. Sources

`sources/` holds the arXiv v1 and v2 PDFs and their texts, the ISIT 2013 author copy, the author-posted IEEE TIT copy (`tit2013-author-posted-ieee-copy.pdf`, sha256 `a7b49ca6…c9f9`), and the rendering notes and images of journal pp. 6712, 6715 and 6722. Its subfolders are:

- `secondary/`: the cached secondary texts;
- `receipts/`: the fetch receipts and Crossref records that verify the three DOIs cited.

All copies are byte-identical to the frozen inputs; `receipts/copy-receipt.json` in the full dossier lists source paths and hashes.
