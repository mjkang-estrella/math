# Public reproduction

Run release checks from the release helper directory:

```sh
python3 -B verify_preparation.py
python3 -B release_checks.py
python3 -B assemble.py --gate FINAL-GATE.json --gate-sha256 EXTERNAL_GATE_HASH --output /var/tmp/NEW-T117Q.zip
python3 -B verify_bundle.py /var/tmp/NEW-T117Q.zip --manifest-sha256 EXTERNAL_BUNDLE_MANIFEST_HASH --gate-sha256 EXTERNAL_GATE_HASH
```

The assembler refuses an existing archive. Obtain hashes externally from the release handoff, not from a replacement gate. Verify the clean extraction with the same verifier arguments, using its directory in place of the ZIP. Exact file/directory membership, hashes, anchor manifest bindings, duplicate JSON keys, unsafe paths, links and nonregular files are checked. `bundle_checks.py` accepts the same archive/hash arguments and exercises disposable mutation copies under /var/tmp. These are identity tests only.

In the clean extraction, change to `frontier/campaigns/2026-10-14/t117q-manuscript-v3/` and run:

```sh
python3 -B build.py --output /var/tmp/NEW-T117Q-PDF --tectonic /path/to/tectonic
```

Use Tectonic0.17.0 with cached dependencies and a new output directory. Default compiler path is /tmp/frontier-typeset/tectonic. The builder sets SOURCE_DATE_EPOCH=1792281600, copies main.tex outside the extraction, and records console/build receipts. Expected16-page PDF SHA256:80b522c80cf975b2b913294874a18f5886a0939763086889ea0a2d532f63c49a. All four options in the PDF Reproduction paragraph are ASCII `--`; no en-dash substitution is needed. The printed `/var/tmp/NEW-PDF-BUILD` path must be fresh, or use another fresh path as the manuscript permits. This release checks extracted tokens and replays the public builder with a fresh output path; r3 separately records literal printed-command execution.

For formal reproduction read selected t117q-formal-v1/rebuild.py, then supply `--output /var/tmp/NEW-LEAN`, `--lean /path/to/lean`, and `--cache /path/to/pinned/packages`. Lean4.34.1 and nine dependency revisions are required; cached objects are trusted. The earlier selected15-file portability run and parent adoption are included. Since those files are unchanged, this release does not repeat it. Full T117Q is not formalized.

Optional finite comparisons: `python3 -B frontier/campaigns/2026-10-14/t117q-contribution-r2/independent_checks.py` and `python3 -B frontier/campaigns/2026-10-14/t117q-parent-literature-r1/grid_control.py` from the extraction root. Both print bounded diagnostics to stdout. They do not prove T117Q or establish priority.
