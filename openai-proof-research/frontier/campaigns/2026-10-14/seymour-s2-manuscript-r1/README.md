# Two Seymour vertices in every sink-free oriented graph

Myeongjin Kang, no affiliation. Manuscript r1, 2026-10-16.

The paper proves the entire frozen S2 statement: every nonempty finite sink-free oriented graph has two distinct vertices with exact second out-neighborhood cardinality at least first. Its only imported premises are the ordinary Seymour theorem and finite binary-relation pruning lemma from the pinned OpenAI manuscript at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Those are explicitly stipulated true, stated in full, and not re-proved here. All new deductions are proved in Sections 2–6.

This is the known Dara–Francis–Jacob–Narayanan Conjecture 2. The exceptional-boundary retention plus aggregate compatible-fiber gain is the added contribution. Subset deletion, transitive blowups, compatible-family objective and pruning closure are credited antecedents. No worldwide-priority certification is asserted.

Status: the frozen candidate has separate internal full-proof PASS and substantial-contribution PASS reports. This manuscript requires its own independent review and acceptance decision. No new-result count is awarded by this package. Nothing has been uploaded or submitted. Current formal coverage and audit state are in `formal-scope.json`; the full graph theorem is **not formalized**.

## Reproduce finite diagnostics

Use Python 3.10 or later, with only its standard library, from a clean public extraction:

```sh
python3 -B support/run_checks.py
```

This authenticates the two preserved checkers and the portable adapter, verifies unchanged mathematical code spans, then runs both diagnostics and checks exact outputs. It fails if a required input/check is missing or a result differs. It writes no files, so a public extraction remains verifiable after a normal check run. The frozen run is `checks/finite-checks.json`.

The author's bitmask checker covers 352,224 boundary identities over 23,664 small graphs and a six-vertex counterexample to a false shortcut. The independent reviewer's set-based checker covers 15,129 deletion endpoint cases, 198,936 blowup subsets and 151,362 anchor exclusions. The portable adapter removes only repository authentication and receipt writing from the reviewer program; unchanged originals and exact provenance are supplied. These are finite diagnostics, not a proof of full S2. See `support/PROVENANCE.md`.

## Build and inspect

The source is `main.tex` with its separate `formal-coverage.tex` include. The final PDF is `output/pdf/main.pdf`. Tectonic 0.17.0 and Poppler are used for recorded builds:

```sh
python3 -B support/build.py --tectonic /path/to/tectonic --only-cached
```

Omit `--only-cached` if first-time TeX dependencies must be downloaded. The build script fixes SOURCE_DATE_EPOCH, rejects overfull/underfull boxes and unresolved references, extracts text and renders every page into `tmp/pdfs/pages/`. Its build receipt is separate from the manual all-page inspection in `checks/visual-review.json`. Rebuilding changes or adds frozen payload files; work in a separate copy if retaining original release integrity. Other TeX versions may produce different PDF bytes.

## Verify a clean public extraction

Before executing code from a downloaded artifact, check the verifier and manifest identities against a trusted parent receipt. From the extracted `seymour-s2-public.zip`:

```sh
python3 -B support/verify_package.py --manifest-sha256 EXPECTED_MANIFEST_HASH
```

Omit the last two arguments for internal consistency only. The verifier requires exact membership, byte lengths, SHA-256 values, and essential payload anchors. It rejects missing/changed/extra payloads and symlinks. It does not need the ZIP, private primary texts, source checkout, or workspace paths. Its success is byte consistency, not proof or authentication of origin. Local handoff-only files intentionally make the unextracted working directory differ from the public payload: run this command on the clean extraction, not the authoring directory.

`support/freeze.py` deliberately constructs the allowlisted deterministic archive and manifests; it is a packaging utility, not a reviewer or acceptance gate. A refreeze requires renewed inspection and review. `output-manifest.json` and `SHA256SUMS` identify local handoff files, excluding the scratch render directory and the two manifest files themselves (SHA256SUMS also covers output-manifest.json).

## Files and boundaries

- `source-to-claim.md` gives the exact dependencies, attribution and actual reading extents.
- `input-manifest.json`, `source-identities.json` record original candidate/review/source identities without redistributing third-party manuscripts.
- `checker-identities.json` and `support/PROVENANCE.md` preserve mathematical checker origins and adapter boundaries.
- `formal-scope.json` and `formal-coverage.tex` state exact formal support and exclusions.
- `metadata.json`, `zenodo-preparation.json`, `mathdb-preparation.md` are local submission preparations, with no invented DOI, problem ID, account or public status.
- `public-files.json`, `public-manifest.json`, `seymour-s2-public.zip` are the allowlisted release payload and byte inventory. Render scratch is local only.
- `LICENSE-PROSE`, `LICENSE-CODE`, `RIGHTS.md` distinguish original CC BY 4.0 prose and MIT code from third-party rights.

The public payload contains no third-party PDF, extracted primary text, upstream source copy, private review body or private account information. Source facts are cited and supplied with identity receipts. Internal reviews and AI assistance are not external peer review.

## Lean support

`formal/` is an unchanged copy of the sealed 40-file implementation packet plus its original output manifest. It supplies eleven support theorems and seven controls, Lean 4.34.1 and a complete pinned Lake dependency manifest. The implementation's real fresh-source build and standard-axiom checks passed; independent formal audit is a separate gate and is not awarded here. No full graph formalization is claimed.

From `formal/`, provision the pinned compiler and dependencies separately, then run:

```sh
lake exe cache get
lake build
```

For the isolated rebuild/mutation runner, use explicit toolchain/cache arguments outside the original workspace, as documented in `formal/README.txt`. Its convenience default paths are not portable dependencies. The paper verification and finite-check commands require no Lean installation or workspace path. The formal payload includes no compiler, mathlib source or third-party PDF. Its README, code and original metadata retain their MIT license, including documentation, rather than being relicensed by the outer prose license.
