# Hetyei Conjecture6.10 proof packet

Full MathDB319292 source-conjecture resolution on the explicit finite count
formula(16): kappa_n<n*kappa_(n-1) for every n>=12, equivalently
K_n<n*K_(n-1) for every n>=11. Every count/composition/recurrence/finite-matrix/
spectral/coefficient-limit bridge is proved. The author's original game-position
enumeration theorem is credited upstream, not recoded.

Read paper.pdf, formal/SourceCounts.lean, PROOF.md, FORMAL-ADDENDUM.md,
proof-map.json, reviews/final/review.md and reviews/parent-final-addendum.md.
All69 reviewed original files are byte-preserved with reviewed-file-locations.json.
Only presentation and operational status wording changed in the release paper;
all Lean modules and verifier bytes remain exactly reviewed. Parent and independent
117-declaration16-module strict replay receipts are byte-identical. An extracted
replay is the last acceptance gate. Historical candidate/STATUS/progress/provenance
snapshots retain credit0; acceptance.json and campaign ledger are authoritative
only after extraction. No independent review is misattributed to new bytes.

Replay:
python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean-4.34.1/bin/lean --packages /absolute/path/to/pinned/.lake/packages

Pinned Lean/mathlib/dependency revisions: verification/pins.json. Raw-source
isolated rebuild, warningAsError, every actual declaration type and axiom set
checked. Only propext/Classical.choice/Quot.sound; no proof holes or new axioms.

One combined outcome. Classical finite spectral decomposition, power convexity,
Faulhaber and the author's enumeration are credited, not separately counted.
The source's auxiliary printed sign and K0 convention are not discoveries.
No global priority claim. Published JCTA and Sterling2018 access limitations,
Timber thesis-chapter scope and bounded novelty coverage remain disclosed.
