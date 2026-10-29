# Logarithm-arctangent source inequality: proof packet

Independent final review PASS for the displayed two-branch inequality.
Root acceptance is recorded separately in acceptance.json and the campaign ledger.
No worldwide priority claim. The separate between-means condition is not certified.

Read main.tex or paper.pdf for the self-contained ordinary proof. Its finite
arithmetic has a compact exact reconstruction rule and a full machine-readable
supplement. Run `python3 supplement/exact_check.py` (hard 512 MiB AS, 35 CPU
seconds; external 45-second wall deadline is enforced by verify.py; BLAS1).

Run `PYTHONDONTWRITEBYTECODE=1 python3 verify.py replay` from an extracted packet.
The replay directory must not already exist. It builds 35 unchanged mathematical
modules and 35 exhaustive origin audit modules, serially, using the absolute
pinned Lean binary and external eight package caches in pins.json. It does not
read root-generated candidate oleans. Only local extracted replay outputs and
pinned upstream package/toolchain oleans enter LEAN_PATH.

The monitor samples process-group RSS every 40 ms, kills at >=3 GiB, and applies
a 240-second wall deadline per process. Sampling is not a continuous bound or
virtual-address-space limit. Every passing sample must be strictly below 3 GiB.
No limit inflation is permitted. The checker has its own hard AS/CPU limits.

Each audit enumerates env.header.moduleData[i].constNames for a mathematical module,
not a namespace/name regex. Logs include generated/private/instance declarations,
actual types, transitive axioms, unsafe/partial/axiom flags. Only propext,
Classical.choice and Quot.sound are allowed. Unsafe declarations/custom axioms
are rejected. Harmless generated partial recursors can have partial=true and
unsafe=false; neither their names nor the substring unsafe is a rejection rule.
Consumed upstream mathematical source hashes are recorded separately. This
accepts pinned upstream mathematics as instructed; it does not reprove mathlib.

build_pdf.py uses the recorded existing Tectonic binary and a lane-local copy of
its cached resource bundle; no network is needed. Set SOURCE_DATE_EPOCH is fixed.
The archive is sorted, ZIP_STORED with timestamp 2026-10-29 00:00:00 and mode 0644.
`python3 pack.py` writes packet.zip and verifies its embedded SHA256SUMS after
extraction. Build twice and compare hashes. Source-only means no oleans or
prebuilt proof artifacts; manuscript and primary-source PDFs are documents.

Adjacent receipts document the actual extracted replay and PDF/ZIP comparisons.
Initial failures are retained outside the archive and described in FAILURES.md.
Input sources and inherited status notes are preserved verbatim under inputs;
obsolete no-Lean/journal-HOLD paragraphs there are historical, not current status.

Inventory correction: 561 audited module-data entries cover 560 unique kernel
declarations. LogArctangentMean.B.eq_1 is listed twice; its true origin is
MeanAnalyticDefs. The independent actual-kernel-map audit finds no missing
kernel declaration. Seven IR-only boxed/redArg names have no kernel type and
are not counted. Review reports and origin evidence are under inputs/final-review.
The current prior-art audit is dated 2026-10-29 08:10 UTC; its limits remain.
