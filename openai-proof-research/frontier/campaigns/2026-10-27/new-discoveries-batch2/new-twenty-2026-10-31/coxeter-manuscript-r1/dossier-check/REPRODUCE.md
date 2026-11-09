# Reproduction and trust boundary

Draft only; candidate credit 0, campaign context 1/20. Root paper review/final replay/acceptance are separate.

1. Verify dossier-manifest.json with `python3 verify_dossier.py` from a fresh dossier extraction. The manifest hashes every packaged file except itself; it does not authenticate an untrusted distribution. Compare the ZIP hash against archive-receipt.json delivered beside the archive.
2. Extract frozen/330264-r3-FULL-LEAN.zip into a new empty directory **inside the authorized lane**. This exact original packet has SHA256 `2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab`. It contains no oleans. Do not modify its Lean or scripts.
3. In that new directory run `env -i PATH=/usr/bin:/bin HOME=/home/mj-kang LANG=C.UTF-8 python3 replay.py`. The original packet manifest is checked, then 10 modules compile in dependency order, with 2-CPU affinity, Lean -j2 -M3500 -DwarningAsError=true and 300-second per-module limits. The final declaration is MathDB330264.conjecture_false. All 24 printed axiom audits must use a subset of propext, Classical.choice, Quot.sound.
4. Read replay-receipt.json and module .lean.log / .lean.receipt.json, not just the exit status. The dossier's proof/ is our fresh extraction and contains these receipts; compiled oleans are deliberately omitted from the ZIP. To repeat in proof/ directly, re-extract the frozen packet over it first: replay overwrites replay-receipt.json, which the original manifest binds, so a second invocation without restoration will fail correctly.

Installed dependencies (absolute paths are embedded in original check.py):
- Lean4.34.1: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
- Lean commit 5045d0056413266e57c625dcd7c365b10e377c52; binary SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550.
- Packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
- proof/dependency-hashes.json pins the anchored source-import closure, including 3,097 external source/olean pairs. dependency-verification.json and dependency-verification-after.json check those bytes. Original local paths in that historical manifest point to the original candidate; the new verifier instead checks local files under proof/ against the same source hashes.

This is a full local proof replay using prebuilt, read-only-by-convention external cache dependencies. It is not a full dependency rebuild or a proof that cache oleans were faithfully built from matching sources. Implicit Init/runtime/plugin sidecars are trusted installed toolchain components, not a fully enumerated runtime closure. No external cache is written by the scripts. Portability requires the same dependencies or explicit path adaptation of replay scripts in a separate authorized copy; the delivered originals remain unchanged.

`independent-corroboration.py` adapts the fidelity reviewer's independent arithmetic script only by replacing its `fresh/` extraction path with `proof/`. It verifies all transition entries and backward vectors, six exact characteristic polynomials, matrix inverses/intertwiners, and an independent forward recurrence. It requires Python3 and SymPy; this corroboration is not the trusted Lean proof.

## Manuscript compilation

paper.tex is the LaTeX source for paper.pdf. The local build uses downloaded Tectonic0.17.0 (GitHub release, tools/tectonic.tar.gz and compiler provenance recorded locally) and its fetched TeX bundle. Run `XDG_CACHE_HOME="$PWD/tools/cache" tools/tectonic --keep-logs paper.tex` here. Compilation is separate from proof replay. The dossier does not vendor the TeX engine/cache; ordinary current LaTeX with amsmath/amssymb/amsthm/geometry/hyperref/booktabs/listings also suffices. Rendering command: `pdftoppm -scale-to 1100 -png paper.pdf render/page`. Every final page is inspected; see pdf-qa.json.

Evidence packaging includes selected direct review files, source bodies/receipts, and the single frozen original proof packet. It excludes prior fresh-extraction directories, old archives, generated oleans, dependency caches and the TeX tool cache. Files that point to earlier campaign evidence are historical references, not claims to vendor that entire history. Reviews are unchanged evidence, not review of this new manuscript.
