# MathDB 381805 - DRAFT dossier

The five-page manuscript proves in ordinary mathematics that the seven-cycle
with four leaves at one vertex has super edge-magic total strength exactly 26.
The complete vertex/edge certificate gives 26; degree rearrangement gives
11c >= 98 + 187 = 285 and hence c >= 26. Deepthi's predicted value is 27.
The source domain and the role of zero pendant counts are stated explicitly.

The literal proof/Magic.lean is byte-identical to the frozen author module.
Its endpoint is Magic381805.source_refutation : ¬SourceConjecture, via the
upper bound strength <= 26. The exact lower bound is NOT claimed formalized.
The Lean correspondence table separates these results and the diagnostics.

Fresh safe extraction of source-only-proof.zip into replay-extraction-r4 passed:
strict -j1 -DwarningAsError=true build; leanchecker; all 37 module-origin
declarations audited, with bodies and no unsafe/partial flags; transitive axioms
restricted to propext, Classical.choice and Quot.sound; one positive sanity
control and six negative controls with their precise expected failures.
Receipts and logs: receipts/final-replay/. Earlier harness failures are preserved
and explained under receipts/earlier-attempts/; the mathematical module never changed.
Each final call had 2-CPU affinity, CPU 120 s and wall 140 s caps, AS 64 GiB,
sampled private RSS guard 6 GiB, MALLOC_ARENA_MAX=2 and a functioning systemd
MemoryMax=6G scope. Imported cached dependency oleans remain trusted.

All five final PDF pages were rendered and visually inspected (qa/QA.json).
The absent optional PDF-skill artifact hook is recorded in receipts/artifact-marker.json.
All 685 frozen input bindings match before and after; formal/Magic.lean identity
and the raw MathDB record hash are recorded in receipts/frozen-check.json.
Target-related source copies and access receipts are retained; unrelated
382220/382141 mathematical payloads are excluded. The binding inventories
cover entire frozen inputs without copying their unrelated contents.

Related work states the reproduced Swaminathan-Jeyanthi bounds 26 <= sm <= 27;
the unread 2003/2006, 2000/2001 and 2001 original bodies are named. Original
review HOLDs and root's later bounded qualified ruling are both preserved.
There is no priority claim and no inferred all-positive-leaf theorem.
The 831,600-assignment enumeration and mixed infeasible/timeout MILPs are
inherited diagnostics, explicitly separate from proof and not rerun here.

Deliverables: paper.pdf, paper-source.json, build_paper.py, PROOF.md,
REPRODUCE.md, pins.json, replay.py, safe_extract.py, source-manifest.json,
dossier-manifest.json, source-only-proof.zip, full-dossier.zip,
archive-hashes.json, results.json, sources/, evidence/, receipts/ and qa/.
The source ZIP has no oleans; the full ZIP adds final receipts and excludes
local vendor dependencies and generated oleans. See REPRODUCE.md for replay
instructions, trust assumptions, resource guards and manifest exclusions.

DRAFT; zero accepted credit; campaign remains 9/20 beyond 39 unchanged.
Root alone accepts. No child agents, git, publication, upload, external messages,
browser use or shared ledger edits. All launched jobs completed before handback.
