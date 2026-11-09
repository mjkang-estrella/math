# MathDB 347712 manuscript handoff

Completed: seven-page self-contained draft `paper.pdf`, reproducible ReportLab
source `paper.py`, transparent 120-permutation certificate, unchanged two-module
`proof-source.zip`, strict safe extracted replay and source-only `dossier.zip`.

Fresh replay PASS: 22 author + 17 supplement local-origin declarations, including
generated helpers, audited with full types and transitive axioms; only propext,
Classical.choice, Quot.sound. Both strict Lean compiles and both leanchecker runs
exit 0. Both deliberate negative controls rejected (exit 1). Every Lean/checker
process used <=2 CPUs, 8 GiB AS, 100 CPU seconds, 110 wall seconds; Lean -j1 and
warningAsError=true. Full logs and dependency provenance retained in replay-*/.
No author replay.py was executed. No upstream own-project objects imported.
Imported dependency olean-cache trust remains; no full upstream rebuild claim.

Finite Definition 3 field / uniform-target scope only: fields 290 < 302;
probabilities 29/60 < 151/300, gap 1/50. Both partitions nonempty and Latin.
Worst-target comparison goes the other way: 58/120 > 55/120. This does not settle
that objective or every interpretation of the raw MathDB wording. Probability
normalization is ordinary mathematics. No optimum, minimal n, necessity-direction,
nonexistence-of-optimal-Latin, asymptotic, or worldwide priority claim.

Both independent reviews remain qualified PASS; fidelity's unqualified/worst-target
HOLD is retained. Root final replay and acceptance are separate and pending.
Accepted credit **0**, context **2/20 beyond39 unchanged**. All **277/277** frozen
bindings match before and after. Both Lean sources byte-identical to frozen pins.
All seven final PDF pages visually inspected; unsupported glyphs corrected and
rerendered. No children, git, shared/author/review edits, browser tabs, external
messages, publication or uploads. No running jobs at handoff.

See README.md for exact commands, review links, source provenance, package contents
and caveats. External manifest.json binds the PDF, both ZIPs and authoritative
frozen source originals. package-manifest.json is the internal payload manifest.
