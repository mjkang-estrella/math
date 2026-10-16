# Reproduction

Use hashes from the separately supplied parent receipt. Before executing bundle
code, check the verifier and `bundle_common.py` bytes against that receipt.
Hash consistency does not establish mathematical truth or priority.

To verify the assembled ZIP, or an untouched clean extraction, run:

```sh
python3 -B verify_bundle.py PATH --manifest-sha256 TRUSTED_MANIFEST_HASH --gate-sha256 TRUSTED_GATE_HASH
```

The verifier requires exact membership, safe unique paths, matching sizes and
hashes, the bound final review artifacts and all required gate verdicts. It does
not execute files from an unverified archive.

Within the extracted manuscript directory
`frontier/campaigns/2026-10-14/kn-minus-edge-manuscript-r2`, run:

```sh
python3 -B support/verify_package.py --public
```

No ZIP or private handoff manifests are required there. The full handoff and
`--with-inputs` modes belong to the research repository, not the public subset.
The formal author's `verify.py --payload-only` checks its included payload
without absent research inputs. Other frozen review scripts may name original
repository paths; those commands are preserved as history and are not promised
as portable standalone verification.

For a fresh build of the support, 9 author controls, 16 reviewer controls, and
exact type/axiom queries, provide an existing Lean 4.34.1 compiler and a matching
read-only dependency cache. The pinned compiler commit and every package Git
revision are checked. The dependency build objects are trusted setup; mathlib
itself is not recompiled. No network downloads occur.

```sh
python3 -B rebuild_formal.py --root EXTRACTED_ROOT --lean /path/to/lean --cache /path/to/.lake/packages --check-setup
python3 -B rebuild_formal.py --root EXTRACTED_ROOT --lean /path/to/lean --cache /path/to/.lake/packages
```

The second command creates fresh project objects only in a disposable temporary
directory, compares type/axiom reports with the independent review outputs, and
runs the original integer arithmetic controls. It never imports the project's
included historical `.olean` files or modifies frozen sources. Capture its JSON
stdout outside the extraction if retaining a new receipt; progress goes to stderr.

Mathematical finite checks and TeX rebuild instructions are in the manuscript
README. Run such regenerating commands on disposable copies, since they write
receipts and logs. The long modular run and prior compiler runs are explicitly
historical evidence. None of these finite checks proves the all-order theorem.

The archive includes `assemble.py` and the explicit selection. After verification,
you can reproduce the same deterministic ZIP from its clean extraction, with
`--gate FINAL-GATE.json --gate-sha256 TRUSTED_GATE_HASH --output /new/path.zip`.
The output must not already exist. Keep it outside the frozen extraction.
