# Shifted Jacobi manuscript and complete source certificate

Research candidate preparation, not independent review or acceptance. One family;
Jacobi credit 0. Counts remain 2/30 additional, 32/60 total. Distinct independent
final review and current novelty/subsumption adjudication remain root's gates.

Read paper.pdf (six pages), main.tex, PROOF.md, FORMAL-MAP.md, LIBRARY.md,
and provenance/preliminary-review.md. The latter's formal/paper status is
historical: the frozen endpoint is now closed. Its bounded novelty assessment
is not a current final acceptance. Primary bodies/titles/versions are in primary/.
No all-order analytic phase identification, original-variable novelty, new tool,
new database record, journal DOI, or worldwide priority is claimed.

Endpoint: `JacobiShifted.source_claim : JacobiShifted.SourceClaim`.
All 35 mathematical modules and the original runner are byte-identical copies.
SourceDefs SHA256 is df95c10e6a9371c1fc3f09424375a4ff51707980db0635e9a321d2c8a09033a5.
Frozen original/copy hashes before/after are in provenance/frozen-{before,after}.json.
Root freeze: 4c7d134d30dc4bf70f81899e5fefa1a3ac661255.

## Replay (explicit working directory)

From this lane, with a destination that does not exist:

```sh
python3 scripts/replay.py packet/jacobi-shifted-source-proof.zip verification/another-fresh-replay
```

The replay extracts into DEST/payload, checks the exact relative manifest,
compiles into DEST/build, and checks the immutable payload again afterward.
DEST/extraction-receipt.json binds the archive SHA and payload-manifest SHA.
The installed Lean binary and all nine manifest package checkouts are external
runtime prerequisites, asserted before/after with no fetching. Their paths,
revisions, binary hash/version, and clean tracked trees/indexes are checked.
Cli has no compiled library directory; the frozen runner includes the other
eight existing package library directories. No package sources are changed.

`python3 scripts/verify.py . verification/another-source-build` directly rebuilds
from source, with no initial local prebuilt artifacts. All Lean processes run
sequentially, -j1 -M4096, warningAsError=true, autoImplicit=false. The sampled
process-tree RSS ceiling is 3,145,728 KiB; total diagnostics cap 512 MiB. There
is no 512 MiB address-space limit. All mathematical logs must be empty.

The complete actual-origin inventory is 1,041 declarations across 35 origins,
including private/generated helpers and instances. No manually chosen subset
is used. verification/audit/declarations.json maps every actual name/origin,
safety flag and axiom closure to formal/WholeAudit.lean.log. The inventory's
isUnsafe flags are all false, including helpers whose names contain
`_unsafe_rec`; that substring is not an unsafe source command or a true flag.
Only propext, Classical.choice and Quot.sound are permitted. The verifier calls
actual #check and #print axioms using environment Names, avoiding ambiguity in
private numeric name components. Elaborators live outside the proof-module set.
SourceClaimInterfaces prints the abbreviated endpoint/definitions; the fresh
ExpandedEndpoint audit also prints the quantified endpoint with TwoLocal,
dyadicExponent and sourceKappa expanded and the finite source definitions.

## Packet determinism and receipts

```sh
python3 scripts/build_packet.py packet/regenerated.zip
cmp packet/jacobi-shifted-source-proof.zip packet/regenerated.zip
```

ZIP entries have sorted relative paths, fixed date/permissions, no caches or
compiled Lean artifacts. manifest.json lists every payload byte except itself.
The archive does not include its own hash or final extraction receipt. The
external packet/reproducibility.json and verification/fresh/extraction-receipt.json
bind those after construction; this prevents circular hashes. The successful
source-only development audit is immutable evidence inside the archive. The
fresh extraction repeats it and adds the expanded endpoint audit. Logs and
receipts identify their actual build steps; no inherited 58-declaration count
is presented as a whole-certificate count. ATTEMPTS.md preserves candid failures.

## Paper build and QA

```sh
python3 scripts/build_paper.py
pdftoppm -r 95 -png paper.pdf paper/render/final
```

The script uses the installed Tectonic 0.17.0 recorded in paper/build-command.json,
only-cached resources copied locally, fixed SOURCE_DATE_EPOCH and lane-local
TMPDIR. It never fetches resources. A fresh unpacked packet uses the already
installed ~/.cache/tectonic resource cache; the cache is not shipped. This
is a source-only research certificate with pinned external toolchain/library
prerequisites, not a vendored operating-system/TeX distribution.
Every final page was personally visually inspected; paper/qa.json binds all six
PNG hashes and paper/TeX hashes. Build logs are under paper/build/. The final
layout has no overfull boxes, clipping or missing glyphs; one underfull reference
line is benign. Full proof clarity was prioritized within six readable pages.

final-review-hashes.json outside the archive covers all retained load-bearing
lane files, including archive, receipts, paper, formal sources, scripts, pins,
actual declaration reports and inventory; it excludes itself and runtime caches
and compiled artifacts. No git mutations, children, count edits, shared/candidate
edits, browser mutations, posting, uploading or account/contact actions were used.
