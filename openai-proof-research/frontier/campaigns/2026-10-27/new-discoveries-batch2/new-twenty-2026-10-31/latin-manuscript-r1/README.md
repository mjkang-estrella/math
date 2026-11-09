# MathDB 347712: finite field / uniform-target draft dossier

This is a manuscript/package/replay lane, not a new independent acceptance.
Accepted credit **0**; root acceptance and root final replay remain pending.
Campaign context stays **2/20 beyond 39**. No variant earns additional credit.

## Claim and limits

For the exact finite Definition 3 field in Czumaj–Kontogeorgiou–Paterson,
*Haystack Hunting Hints and Locker Room Communication*, DOI 10.1002/rsa.21114,
the cyclic first-maximum Latin strategy at n=5 has field 290 while the displayed
competitor Latin strategy has field 302. Both have five nonempty fibres.
Uniform-target success: 29/60 versus 151/300, gap 1/50.
Worst-target success: 58/120 versus 55/120, so this comparison **does not settle
source §2.1's worst-target objective**. The raw MathDB record omits distribution;
no blanket resolution of every interpretation is asserted. Probability
normalization is an ordinary counting argument, not a formal probability theorem.
No exact optimum, minimal order, necessity-direction, nonexistence of an optimal
Latin strategy, asymptotic improvement, or worldwide priority claim is made.

Both independent reviews are qualified PASS for this scope. Fidelity retains
HOLD for an unqualified/worst-target interpretation. Original review links:

- [Source/significance](../latin-source-significance-review-r1/REVIEW.md), [verdict](../latin-source-significance-review-r1/review.json).
- [Fidelity/formal](../latin-fidelity-review-r1/REVIEW.md), [verdict](../latin-fidelity-review-r1/review.json).

Exact copies of these four small files are under evidence/. Review scripts under
evidence/ are historical read-only provenance; **do not execute them** there.
Use this dossier's replay.py. Novelty is a bounded prior-art nonfinding inherited
from the source review; no new search or global priority certification is claimed.

## Contents

- paper.pdf: seven-page draft, every rendered page visually inspected.
- paper.py: complete reproducible manuscript source (ReportLab rather than TeX).
- proof-source.zip: exactly Latin.lean and Supplement.lean, byte-identical to the
  frozen author and reviewer originals; no compiled objects or replay scripts.
- replay.py: safe extraction into a new lane-local directory and strict replay.
- replay-result.json and replay-*/: full execution receipts, stdout/stderr,
  module-origin audit sources, dependency provenance, negative controls.
- enumerate.py, certificate.json, partition.csv: transparent exhaustive verifier,
  all 120 assignments, agreement vectors, all 250 magneticities and maxima.
- source-reference-index.json: selected source paths/hashes; frozen-inputs.json:
  authoritative complete 277 bindings. Original source trees are not copied.
- results.json / SUMMARY.md: machine-readable and human handoff.
- package-manifest.json: hashes of packaged payload before the dossier is sealed.
- manifest.json: final external manifest binding payload, original frozen inputs,
  PDF and both ZIPs. It is outside dossier.zip to avoid a self-hash cycle.
- dossier.zip: selected reproducibility payload, logs and reviews; excludes
  installed Python environment, generated local objects and unrelated dossiers.

## Replay

Run `python3 replay.py` from this lane (or an extracted dossier location). It
needs Python's standard library, Linux resource limits, and the existing pins:

- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52;
  `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
  `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.

Every run uses a new local directory. Existing local objects are never imported.
LEAN_PATH consists only of that directory and existing package caches. Upstream
own-project build paths are excluded. The sanitized environment, complete Lake
manifest, actual mathlib HEAD, executable hashes, flags, limits, exit codes and
timings are recorded under the run directory. Each Lean/checker process gets
-j1 (Lean), warningAsError=true (Lean), at most 2 CPUs, 8 GiB AS, 100 CPU seconds,
110 wall seconds. The package caches are read-only inputs; no dependency rebuild
or source-to-olean attestation is claimed. **Imported prebuilt oleans are trusted.**

Audit all 22 author and 17 supplement declarations by module origin, including
generated helpers: full types plus transitive axioms. Allow only propext,
Classical.choice, Quot.sound. No proof-level sorry/admit/new axiom/unsafe/
native_decide/ofReduceBool. Run leanchecker on both modules. Negative controls
must reject an ill-typed False proof and corrupt module. The actual successful
receipt is replay-result.json; root must perform its separate final replay.

Endpoint: `MathDB347712.source_refutation : ¬MathDB347712.SourceClaim`.
Nonempty robustness: `LatinFidelity.restricted_refutation` and
`LatinFidelity.ordinary_partition_counterexample`. See paper §5 for bridges.

## Count and PDF reproduction

`python3 enumerate.py` needs no external package and regenerates the full finite
certificate. Its independent loop computes actual fibre magneticities, not a
sample or agreement-only surrogate. Compare hashes before/after if preserving
a sealed package.

For the PDF, create a local venv and install the pinned requirements in
requirements-paper.txt, then run `python paper.py`. It uses system Liberation
Serif regular/bold and Liberation Mono regular TrueType fonts under
/usr/share/fonts; exact font hashes are in pdf-qa.json. Render with
`pdftoppm -scale-to 1250 -png paper.pdf render/page`. The PDF was inspected page
by page after correcting missing glyphs; no clipping, overlap or unreadable
symbols remained. PDF metadata timestamps may differ on rebuild.

## Source versions / frozen originals

v1 (2020) asserts optimal implies shift, a different statement. The Latin
biconditional is v2 (2021), ICALP Conjecture 25, published Conjecture 3.
The publisher-typeset institutional Warwick body inspected by both reviewers:
`../latin-source-significance-review-r1/published-warwick.pdf`, SHA256
`f55e68262549c29869875744130146fcbfebfe4452dda8a8e6a06105d9f48691`.
Lawful URL: https://wrap.warwick.ac.uk/id/eprint/170329/1/WRAP-Haystack-hunting-hints-and-locker-room-communication-Kontogeogiou-2022.pdf
No denied-source retry, current Wiley authentication, or complete erratum check.

Latin.lean SHA256:
`7c93a368b2d7007aa10102cb7bb92ca5f3585cc4bd46a2d54c26c859d46c5392`.
Supplement.lean SHA256:
`47624020f01dda04bed4017512b5b0c1f9ddf31039d36f8bb52f20fd40bdc353`.
All 277 frozen scientific bindings verified before and after. This lane alone
was written; no shared/historical/author/review edits, git operations,
publication/uploads/external messages/browser tabs or children. No running jobs
remain at handoff. The installed PDF-only venv is local and excluded from ZIPs.
