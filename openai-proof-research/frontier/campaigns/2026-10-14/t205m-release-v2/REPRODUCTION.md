# Reproduction

From this release preparation directory:

```sh
python3 -B verify_preparation.py
python3 -B release_checks.py
```

The second writes only disposable /var/tmp copies and prints its receipt. Neither command builds a final archive or confers mathematical acceptance.

After a parent-adopted final gate, assembly is:

```sh
python3 -B assemble.py --gate /path/FINAL-GATE.json --gate-sha256 EXTERNAL_GATE_HASH --output /path/NEW.zip
python3 -B verify_bundle.py /path/NEW.zip --manifest-sha256 EXTERNAL_MANIFEST_HASH --gate-sha256 EXTERNAL_GATE_HASH
```

Verify an extracted directory with the same hashes as well. Exact membership, directory membership, hashes, duplicate JSON keys, path traversal, symlinks, hardlinks and nonregular files are checked. Hashes establish identities, not theorem validity.

In the selected `t205m-manuscript-v1/public/`, read README.md and build.py, then build using Tectonic 0.17.0 with its already cached bundle and a fresh outside output directory. The expected PDF SHA256 is 4144bf0f3f06b5a7e8a13e2937f03f9bc405101cf40a219e3a097fcc3a234765. The public finite-code commands and their precise m≤8 / degree≤10 limits are documented there; these do not prove the all-order lemmas.

For scoped Lean reproduction, read selected `t205m-formal-v1/rebuild.py`, then run it with `--output /var/tmp/NEW-BUILD --lean /path/lean --cache /path/pinned-packages`. The nine dependency revisions are in lake-manifest.json. It compiles fresh local objects, audits types/axioms and requires a new output directory outside the packet. Cache bootstrap is separate; no dependency cache is distributed. The independent review source/log is selected for statement and necessity controls; its original execution driver is deliberately omitted because it writes its own review directory and assumes full private research layouts. No portable reviewer execution is claimed.

The actual final gate is now adopted; pass its externally supplied hash, never merely a self-declared status. The selected public finite verifier is `frontier/campaigns/2026-10-14/t205m-manuscript-v1/public/code/verify-finite-proof.py`; run `python3 -B` without `--write`. Build with `python3 -B frontier/campaigns/2026-10-14/t205m-manuscript-v1/public/build.py --output /var/tmp/NEW-PDF --tectonic /path/tectonic`. Use new outside output directories. Neither command needs private sources. Reviewer independent_finite.py resolves the selected sibling manuscript certificate; lemma_controls.py is standalone. Their result files are historical independent evidence; release validation replays the author's public finite verifier.

Run `python3 -B bundle_checks.py ZIP --manifest-sha256 EXTERNAL_MANIFEST_HASH --gate-sha256 EXTERNAL_GATE_HASH` for disposable archive/extraction mutation controls. The prior parent formal portability receipt is included; unchanged formal payload is not rebuilt again here.
