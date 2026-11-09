# H028 — Coordinator intake

2026-10-08. **Submission received; independent review required.**
Verified full factoring complexity improvement: **NONE**.

The coordinator consumed all 808 lines of the polynomial-sharing report.
Its unmodified bytes are preserved in [H028-submitted-draft.md](H028-submitted-draft.md),
SHA-256 e493c11555e6285c88caf8ab970c367d387f520263e8157b981f246d96b1152d.
Before checkpoint changes, all 17 consulted-input entries and all 13 owned
report/source entries in H028-sharing-provenance.json matched both bytes and
SHA-256. That manifest's hash is
5598e8b68cbefa4023dc01eec43c4bf730ee1500bcc75ee5d7e407882ba2852b.
Its input hashes are completion-time evidence, not read-time seals.

The submission reconstructs Coppersmith's balanced multi-field model, including
distinct field ideal columns, shared rational survivors, all K*M norm objects,
root work and proper splitting. It derives the known cold constant with cube
(92+26*sqrt(13))/27 and separates the smaller amortized factory constant.
Its proposed processing-only saving still has that same restricted relaxed
infimum even when the algebraic processing/root stages are free. This is a
statement about the specified model, not every multi-field method.

The second card specifies a compatible common square map. It supplies an
explicit N=55 counterexample to silently identifying ideals across different
fields, charges primorial congruence heights, and distinguishes isomorphic
field relabeling from new relations. A valid integer-column construction
q=a²+ell_i*N*b² has ordinary N-sized norms and returns a Dixon-type conditional
scale; changing the sign reaches the known square-difference setting.
No new survivor, implementation or finite experiment was selected.

Independent review must check the full baseline optimization and boundary
quantifiers, actual coefficient/norm widths, ideal valuations and derivative
denominators, both the counterexample and valid square map, aggregate batch
input length, candidate distinctness, rank/restarts and proper-split costs.
Neither the proposer nor this intake accepts new deductions as project theorems.
The balanced known-model obstruction must not become a general factoring
lower bound, and ordinary smoothness must not become an adaptive yield law.

Original task and review handles belong in tasks-H028.json. The reviewer owns
H028-independent-review.md and H028-review-* only; no finite experiments,
shared code/Lean edits, recursion, package installation, commits or publication.
