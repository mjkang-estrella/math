# T298P portable local bundle

Read MANIFEST.json's `kind` first. PREPARATION_ONLY is an unaccepted preparatory
copy with no independent manuscript PASS supplied. REVIEWABLE_LOCAL_RELEASE is a
local package gated on an externally anchored independent manuscript PASS with an
empty required-findings list. Neither state accepts the result, adds count credit,
uploads or publishes anything. The campaign remains 17/20 and publication STOPPED.

The active paper is `paper/output/pdf/main.pdf` (18 pages), with exact LaTeX in
`paper/main.tex`. Myeongjin Kang is the author; no affiliation is asserted.
The theorem concerns exactly two bounded self-adjoint coordinates in a von Neumann
algebra with a faithful normal tracial state, with
`-infinity < chi < chi* < infinity`. Here chi uses the original operator-norm cutoff,
ordinary limsup and all matrix output sizes. The source specialization has k=2^32
and a liminf gap transfer factor k^-2. There is no generation claim or useful
explicit epsilon. Read the paper for exact hypotheses and quantifiers.

The full analytic theorem is NOT Lean-formalized. `formal/author/coverage.md`
and `formal/reviewer/review.md` delimit four support theorems and four scalar
controls. The independent supplement adds ten examples, giving 18 reported
theorem types and standard-axiom dependency audits. Scalar entropy placeholders are
finite real numbers, not extended-real entropy definitions. The permitted reported
axioms are propext, Classical.choice and Quot.sound. Five deliberately broken Lean
fixtures must fail; they are not advertised as proved theorems.

## Standalone commands

Use Python 3.10 or newer. Obtain the expected manifest SHA-256 from the sender's
external handoff, not by trusting a value calculated solely from the downloaded
bundle. Set BUNDLE to an extracted absolute directory, ANCHOR to that independently
received hash, and OUT to a fresh directory outside BUNDLE. All outputs must have
existing, real directory parents and must be disjoint from inputs.

    python -I -B "$BUNDLE/release.py" verify --bundle "$BUNDLE" --anchor "$ANCHOR"
    python -I -B "$BUNDLE/release.py" replay --bundle "$BUNDLE" --anchor "$ANCHOR" --mode all --output "$OUT" --lean "$LEAN" --cache "$LEAN_CACHE" --tectonic "$TECTONIC"

LEAN and TECTONIC must be explicit absolute paths to installed binaries. LEAN_CACHE
must be an external trusted cache containing all dependency repositories named in
`formal/author/lake-manifest.json`, at their exact locked commits, with compiled
`.lake/build/lib/lean` artifacts. The cache is neither included nor downloaded.
The installed Lean binary must match the SHA-256 in the original audit receipt and
report Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. Tracked Git
cleanliness and commit identity do NOT authenticate cached oleans. Compiler/runtime
and pre-existing dependency oleans are trusted, not bootstrapped or rebuilt here.
Original scoped support, controls and independent examples are freshly compiled.

Tectonic 0.17.0 must match the SHA-256 in `paper/validation/build-receipt.json`.
Its TeX bundle/cache and the installed Poppler `pdftotext` and `pdfinfo` commands
are external dependencies under their own licenses. The inherited author build
can fetch missing TeX inputs; preprovision its trusted TeX cache when offline
operation is required. No compiler or TeX distribution is redistributed here.
SOURCE_DATE_EPOCH is fixed by the author build. Replay requires a byte-identical
PDF; it fails if the result differs. Different TeX inputs are not silently accepted.

Replay modes `identity`, `pdf`, `author` and `reviewer` are also available. Identity
only verifies membership and hashes. PDF replay verifies reproduction, not the
analytic argument. Author and reviewer replay compare fresh types/axioms and logs
against the original bound references. `all` runs every listed standalone replay;
it does not run contextual private-repository checks. See PROVENANCE.md.

## Safe extraction

Run the trusted copy of release.py, supplying both externally received hashes:

    python -I -B release.py extract --archive "$ARCHIVE" --archive-sha256 "$ARCHIVE_SHA256" --anchor "$ANCHOR" --output "$BUNDLE"

Extraction rejects unsafe paths, links, extra members, metadata deviations, wrong
hashes and duplicate entries before publishing the fresh extracted directory.
The canonical archive contains files only; directory membership is derived from
those paths. Archive generation is deterministic within the same Python/zlib
implementation. External anchors establish identity, not mathematical truth.
