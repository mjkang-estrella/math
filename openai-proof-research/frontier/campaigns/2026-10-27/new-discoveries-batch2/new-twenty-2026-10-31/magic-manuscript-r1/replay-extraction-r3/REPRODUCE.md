# Reproduce the MathDB 381805 DRAFT

This dossier assigns zero accepted credit. The campaign remains 9/20 beyond 39;
root alone accepts. The exact minimum 26 is proved in PROOF.md and paper.pdf.
The byte-identical author module proves the refutation (strength at most 26),
not the ordinary lower bound. Review supplements are explicitly separate.

## Offline Lean replay

Prerequisites: Linux, Python 3 standard library, the pinned Lean installation and
read-only cached dependency builds. No network, lake update, git command or cache
write occurs. Examples of local dependency locations (override for portability):

```
python3 -I safe_extract.py source-only-proof.zip /absolute/path/to/NEW-directory
cd /absolute/path/to/NEW-directory
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

safe_extract.py rejects absolute paths, traversal, backslashes, symlinks,
nonregular members and duplicate names, and refuses an existing destination.
Use a new destination INSIDE this lane for the supplied verification exercise.
replay.py verifies source-manifest.json and binary hashes, verifies package
revision metadata without git, and refuses any existing .olean, controls/ or
replay-receipts/. It creates only proof/Magic.olean, proof/Magic.ilean,
controls/ and replay-receipts/ in its own extraction; it deletes nothing.
No supplied olean is included in the source-only archive.

Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib
commit d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned in pins.json,
with dependency revisions and binary hashes. The driver checks all package
HEAD metadata. This binds metadata, not the entirety of the dependency cache.
Imported cached oleans are trusted; no full upstream rebuild or source-to-olean
attestation is claimed. leanchecker uses the same Lean installation.

Each Lean/checker call uses at most two CPUs, RLIMIT_CPU=120 seconds,
wall cap 140 seconds, AS cap 64 GiB, MALLOC_ARENA_MAX=2 and a sampled 6 GiB
private-RSS guard (RssAnon+RssShmem, every 50 ms, over its process group).
Total VmRSS is also sampled and reported. Where a user systemd manager is
available, the call also uses MemoryMax=6G, MemorySwapMax=0 and CPUQuota=200%.
REPLAY_NO_SYSTEMD can disable that optional scope on a different host;
it was not disabled for the recorded replay. There is no cache mutation.

The strict build uses `lean -j1 -DwarningAsError=true`, followed by
`leanchecker Magic`. proof/ReviewAudit.lean is a reviewer supplement that selects
ALL declarations by originating module Magic, prints full types, flags, body
presence and transitive axioms, and enforces exactly 37 declarations with bodies,
none unsafe or partial. Only propext, Classical.choice and Quot.sound are allowed.
The source scan additionally rejects sorry/admit/axiom/unsafe/partial/native_decide
and ofReduceBool tokens in the literal mathematical module.

## Controls and their precise scope

The positive sanity control checks the hub label, absence of a chord, and failure
of the same certificate at 27. Six negative controls must be rejected:

- The same labeling asserted at 27: finite certificate is false.
- The negated endpoint used as a proof of SourceConjecture: type mismatch.
- A sorry proof under warningAsError: strict mode rejection.
- A duplicated vertex label asserted injective: finite assertion is false.
- An inserted axiom used by a theorem: the audit's allowlist rejects it.
- A malformed olean: leanchecker rejects its header.

These controls test the indicated checks; they do not establish source fidelity,
novelty, independence of the kernel, or formalize the lower bound. PASS requires
all expected exits and diagnostic strings, plus the full declaration audit.
replay-receipts/result.json records the result and every call has its log and
resource receipt. A failed assertion is a failed replay; use another fresh
extraction after resolving it rather than reusing generated artifacts.

## Paper and evidence

paper-source.json is the editable manuscript source; build_paper.py renders it
with ReportLab and writes the prose companion PROOF.md. For paper rebuild only,
install reportlab==5.1.0 and use the Liberation Sans font files named in the
builder (or adapt the paths). `python3 build_paper.py` produces paper.pdf.
The local authoring dependencies under tools/vendor are excluded from archives;
Lean replay needs only the standard library. PDF byte identity on rebuilding is
not claimed. All five pages were rendered with pdftoppm and visually inspected;
see qa/QA.json. The absent container artifact-marker hook is recorded honestly
in receipts/artifact-marker.json; it is not a PDF or Lean verification failure.

raw/381805.jsonl is a literal cached MathDB record, hash-bound by the manifests.
sources/author contains only target-related author sources and registry evidence;
evidence/review and evidence/prior preserve the independent reports, source
copies, receipts, scripts and diagnostics. Those reports are inherited evidence,
not newly rerun experiments or acceptance decisions. The author's original
packet replay receipts are in evidence/author-packet-replay, without its olean.
Unrelated MathDB 382220/382141 material is excluded from the dossier payload.
The frozen binding lists paths/hashes for the complete four specified inputs;
that inventory is not an inclusion of their unrelated mathematical contents.

No new literature fetch is claimed in this manuscript-only pass. The earlier
bounded reviews and their dated access receipts remain the basis for the
bibliographic discussion. Unread originals, review HOLDs and the later root
qualified ruling are preserved. No priority claim is made.

## Archive and manifest structure

source-manifest.json maps every source ZIP member except itself to its SHA256.
source-only-proof.zip contains the paper, proof, pins, driver, extraction helper,
source evidence and receipts available before fresh replay. The full-dossier ZIP
adds fresh replay receipts, QA, final bindings, summary and results. It omits
local vendor installations and generated oleans. dossier-manifest.json hashes
its payload except itself; archive-hashes.json externally hashes both archives.
ZIP manifests cannot hash themselves or their enclosing ZIP; these exclusions
are explicit. A fresh full-dossier extraction is hash-verified separately.
