# Reproduce

Pinned Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin (4.34.1).
Pinned read-only packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The delivered source archive is chanlevine-round7c-source.zip. Its SHA-256 is in results.json. It contains only Lean sources, scripts, documentation and frozen manifests, with relative safe paths.

From the lane, scripts/package.py verifies all 36 frozen hashes, writes the archive, validates paths and extracts into a new empty fresh-extraction directory. It intentionally refuses to replace an existing extraction. The delivered extraction contains no inherited compiled artifacts before its first replay.

Run `python3 -I fresh-extraction/scripts/replay.py --resume`. Without --resume it rebuilds all modules. Receipts are keyed to the complete source manifest. All 43 modules compile in dependency order with -j1 -M3500 -DwarningAsError=true and run through leanchecker. Every child is resource-capped and every log name is unique. The driver itself launches no concurrent heavy children.

CountR7CAudit constructs the full reachable type/value dependency closure from every declaration owned by the independently enumerated local import closure of CountR7CControls, including generated declarations. It checks closure membership of all dependencies, audits unsafe/partial/_unsafe_rec/extern/implemented_by metadata, and rejects unexpected axioms or local executable flags. LOCAL and UPSTREAM records are distinct. The driver independently reconstructs the local module closure from source imports and validates audit totals.

Seven deliberately invalid controls must fail compilation. Exact isolated Python checks include the inherited diagnostic suites and check_r7c.py. Finally, run `python3 -I scripts/finalize.py` to verify archive/extraction/source equality, frozen hashes and audit data and produce results.json.

The target theorem is unconditional. This packet does not assert that the full MathDB endpoint or the sibling trace identity has been proved.
