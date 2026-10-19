# T298P local release implementation and tested handoff

This development packet is complete for the active manuscript-r2. It contains a
portable preparation, the actual r4-gated local release, deterministic ZIP, strict
read-only identity/extraction tools, selected public originals, and test receipts.
It performs no acceptance, count-credit, staging, commit, upload or publication.
The campaign remains 17/20; publication remains STOPPED. Full analytic T298P is not
Lean-formalized. The exact frozen target and formal trust limits are in the payload
README, PROVENANCE and original manuscript.

`IMPLEMENTATION-MANIFEST.json` seals every file and directory here except `scratch/`.
Its external hash is delivered in the author handoff, not self-certified inside
this file. Scratch contains working builds, failed first-attempt output and unsafe
archive controls; none is a release payload. Do not redistribute scratch.

Deliverable tree: `final/payload/` (92 files plus its manifest).
Deliverable archive: `final/t298p-release.zip` (reviewable local release).
Final anchors:

- Bundle manifest: `e3830fe82c3c74efab72b57cc4981354a470a8a8e8d187df4b022c66285d108a`.
- ZIP: `4b9576c1b8528d8cc6988d4fad3b181bb9b896604ad65a8e5422e0e26d981fbc`.
- Preparation manifest: `60bf9ebcb036f10cbc0c9104d24b55d1699b244d18c77012dbff29ea3bd355ed`.
- Actual independent r4 review manifest: `891ed61f8321ab159ce35689737b9b264028659ed8677de2a717f55b181fe70f`.
- Explicit r4 layout policy: `865dfd119c949a6bee033123db3e619f1bfddbeae4500a759b179c1637cb5cb0`.

The policy was written only after reading the real completed r4 schema/report and
receiving its external manifest anchor. It checks verdict.json `/verdict` equals
`PASS_FULL_MANUSCRIPT_T298P`, `/required` is an empty array, and
`/manuscript_manifest_sha256` is the active r2 manifest. Its eight selected public
review artifacts include the human report and actual verdict, reading limits,
license, finite score diagnostic and receipt, PDF reproduction and visual receipt.
These are bound through the original review manifest; no guessed r4 schema or
future acceptance file participates. The historical r3 NEEDS_REVISION is rejected.
The nonblocking r4 O4 prose splice is preserved without editing frozen r2 bytes.

## Verified outcomes

See validation/summary.json and the detailed receipts. The 35 preparatory controls
cover real r3 rejection, absent gate, wrong anchors, missing/extra/modified files,
empty directories, links, traversal, nonportable paths, duplicate entries and safe
actual extraction. The 15 final controls exercise the actual r4 PASS, required
findings and wrong-object rejection through ephemeral mutations of its actual
schema, explicit anchor failures, repeated deterministic real assembly and three
finite diagnostics. No synthetic successful review is retained.

The final ZIP was safely extracted to a fresh directory. That extracted release.py
verified the exact extracted membership and replayed all required standalone work:
18-page PDF byte-identical; eight author declarations with matching types/axioms;
18 total independent declarations with matching sources, dependencies and logs;
five regenerated negative fixtures rejected, with all fixture/log bytes matching.
The five failing fixtures are explicitly labeled as non-theorems. The source,
compiler and dependency pins are reproduced; installed toolchain/runtime and
cached dependency oleans remain trusted. The analytic argument is human-reviewed,
not established by integrity or finite diagnostics. Original private-source checks
are identified as contextual, never silently counted as standalone PASS.

The inherited partial implementation was audited before reuse. Its obsolete r1
bindings were replaced by r2; explicit source/PDF bindings, portable filename
checks, a dedicated preparatory archive command and empty-array required-findings
check were added. An initial replay exposed the payload-size limit being applied
to the external 26 MB Tectonic executable; executable reads now have a separate
bounded 256 MB limit, while payload files remain limited to 16 MB. Final replay
passed after this fix. No frozen author/review inputs or old partial release files
were modified.

## Exact reproduction and finalization commands

Run from the research repository. All command outputs must be fresh and outside
sealed payloads. Set IMPLEMENTATION_ANCHOR to the separately delivered final
implementation-manifest hash. These variables identify the existing local tools;
a recipient supplies its own explicitly installed binaries and trusted pinned
cache. The commands do not fetch or vendor Lean dependencies.

```bash
REPO=/home/mj-kang/Documents/Dev/math/openai-proof-research
DEV="$REPO/frontier/campaigns/2026-10-14/t298p-release-r2-development"
REVIEW="$REPO/frontier/campaigns/2026-10-14/t298p-manuscript-review-r4"
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
LEAN_CACHE="$REPO/frontier/campaigns/2026-10-14/formal/.lake/packages"
TECTONIC=/tmp/frontier-typeset/tectonic
PREP_ANCHOR=60bf9ebcb036f10cbc0c9104d24b55d1699b244d18c77012dbff29ea3bd355ed
FINAL_ANCHOR=e3830fe82c3c74efab72b57cc4981354a470a8a8e8d187df4b022c66285d108a
ARCHIVE_ANCHOR=4b9576c1b8528d8cc6988d4fad3b181bb9b896604ad65a8e5422e0e26d981fbc
REVIEW_ANCHOR=891ed61f8321ab159ce35689737b9b264028659ed8677de2a717f55b181fe70f
POLICY_ANCHOR=865dfd119c949a6bee033123db3e619f1bfddbeae4500a759b179c1637cb5cb0
python -I -B "$DEV/release.py" verify-implementation --implementation-anchor "$IMPLEMENTATION_ANCHOR"
python -I -B "$DEV/release.py" verify --bundle "$DEV/final/payload" --anchor "$FINAL_ANCHOR"
python -I -B "$DEV/release.py" prepare --repo "$REPO" --implementation-anchor "$IMPLEMENTATION_ANCHOR" --output "$DEV/scratch/parent-prepared"
python -I -B "$DEV/release.py" assemble --prepared "$DEV/scratch/parent-prepared" --preparation-anchor "$PREP_ANCHOR" --manuscript-review "$REVIEW" --review-anchor "$REVIEW_ANCHOR" --review-policy "$DEV/policy/r4-layout.json" --policy-anchor "$POLICY_ANCHOR" --output "$DEV/scratch/parent-final"
python -I -B "$DEV/release.py" extract --archive "$DEV/scratch/parent-final/t298p-release.zip" --archive-sha256 "$ARCHIVE_ANCHOR" --anchor "$FINAL_ANCHOR" --output "$DEV/scratch/parent-extracted"
python -I -B "$DEV/scratch/parent-extracted/release.py" replay --bundle "$DEV/scratch/parent-extracted" --anchor "$FINAL_ANCHOR" --mode all --output "$DEV/scratch/parent-replay" --lean "$LEAN" --cache "$LEAN_CACHE" --tectonic "$TECTONIC"
```

The checked-in final/ output already underwent these operations; use fresh output
names to repeat them. The preparation is retained as `prepared/` so assembly can
also be repeated directly without accessing original selected repository packets.
No remaining technical release gate is open in this task. Independent parent
intake/integration and any acceptance decision remain separate; no result-count
change or publication follows automatically from these commands.
