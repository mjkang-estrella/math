# Cascade manuscript and proof packet

Independent final review and root extracted proof replay completed.
One scoped geometric-rate counterexample; no worldwide priority claim.
The final root decision and hashes are stored beside the accepted candidate packet.

Read paper.pdf (six pages) or main.tex for the complete ordinary proof.
PROOF.md records source mapping and literal certificate scope. Inputs are byte
copies of frozen sources/reviews, including the actual published article and
20-page archived publication-hosted supplement; no network is needed for proof replay.

Unzip cascade-source-packet.zip into a new directory and run `python3 verify.py`.
Use Python 3 and the exact absolute Lean binary and eight external package paths
in pins.json. It checks the binary SHA and version, all eight revisions, clean
tracked trees, and absence of additional untracked source files outside build
folders, without git commands. It copies only local source files to a new work/
and compiles serially with -j1, warnings as errors and autoImplicit false.
It never consumes root's output oleans. Upstream cached pinned oleans are external
trusted build inputs and all consumed source/olean bytes are audited.
Each process group is sampled every 50ms, killed at RSS >=3GiB or wall >=180s;
no limits are inflated. A new extraction is required for a repeat replay.
OriginAudit enumerates all declarations from the actual nine module origin tables,
including private/generated/instances; prints actual types, flags and transitive
axioms; and rejects unsafe flags, axioms and dependencies beyond standard three.

`python3 build_paper.py` builds the PDF twice and asserts byte identity with a
fixed SOURCE_DATE_EPOCH. External Tectonic 0.15.0, its resource cache (tex-cache/),
and system Liberation fonts must be available as recorded in provenance; they
are typesetting environment inputs, not mathematical certificates. The supplied
PDF was rebuilt twice identically. No overfull/underfull boxes remain. This is
an environment-pinned rebuild, not a promise across different font/engine versions.

`python3 build_packet.py` creates a sorted ZIP with fixed 2026-10-29 timestamps,
mode 0644, deterministic compression and embedded MANIFEST.json SHA256s. It
checks two independent archive constructions, extracts inside this lane, verifies
every payload hash, and runs this verifier from that extraction. It retains replay
logs separately. No .olean/.ilean/.ir or prebuilt proof artifacts enter the archive.
Baseline evidence is under evidence/, fresh receipts under extracted-replay/verification/.
The archive contains the manuscript PDF as a document, not a prebuilt proof.

No mathematical numerical script is used. Hash/provenance bookkeeping uses exact
bytes. The failed font build and stalled post-replay regex, fixed by bounded
per-declaration parsing, are preserved under failures/. Inherited component
failures (broad import RSS, CPU diagnostic) remain disclosed in copied summaries.
No proof module was edited. No git operations, children, browser tabs, external
contacts, uploads, acceptance or shared counts/ledgers were used.
