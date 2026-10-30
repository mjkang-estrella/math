# Independent parent audit of GLM finite variance support

Verdict: **PASS for the exact finite real scalar statements.** No new
research-result credit; this supplements R024. The parent read the entire
Lean source and the author's checks, rebuilt the source into a fresh
temporary `.olean`, and compiled the checks and a separately written
quantified type/axiom audit against that new output. The author's binary
was not trusted. All final commands exited zero without warnings.

The three public declarations have the expected arbitrary universe and
finite type I, `[Fintype I] [DecidableEq I]`, a real kernel K and arbitrary
real vector u. The exact identity assumes both row and column sums one;
positivity appears only in the nonnegative-deficit corollary. No dimension
or nonemptiness restriction or assumption of the desired conclusion was
introduced. The column lemma assumes only column normalization. `ParentAudit.lean`
checks the full generic identity and corollary, not just a fixed matrix.

The proof expands the square inside finite sums, collapses both diagonal
moments by the column sum and factors the mixed moment. Summing over
columns and exchanging finite sums invokes the row sum. The corollary
uses termwise nonnegativity and the exact factor two. These operations
match the written scalar algebra and the displayed theorem types. The
only active source option suppresses an unused-section-variable linter;
it does not bypass proof checking.

The fresh compiler reports only `propext`, `Classical.choice`, and
`Quot.sound` for each public theorem. There is no `sorryAx`, custom axiom,
`native_decide`, unsafe implementation, or declaration replacing the
conclusion. The toolchain is Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, with mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` independently checked from the
cached checkout. `validation.json` binds the exact input source bytes.

The author's `Checks.lean` covers an empty index type and a uniform Fin 2
example, including direct kernel-evaluated arithmetic. These are additional
checks by the same authoring agent, not a separate independent reviewer.
The symmetric Fin 2 example alone cannot distinguish every transposition;
the generic type audit and proof inspection establish the requested
orientation. No reliability claim about other GLM tasks follows.

The first parent harness omitted `[DecidableEq I]` from its own example,
although that instance was part of the requested and implemented statement.
Source and author checks already compiled; adding the original instance
to the harness fixed that parent error without changing GLM's source.
The initial log is retained transparently alongside the successful log.

Coverage is exactly finite real scalar counting-measure variance, its
per-column form and nonnegative deficit. It is not Hilbert-valued or a
measure-theoretic integral proof and does not formalize moving kernels,
Fatou, curved-arc positivity, conformal limits, resolvents, maximum
principles, Jin geometry or the full Crouzeix equality theorem.

`run_audit.py` reproduces this repository-cache audit; the separate
`matrix-disk-formal-v1` package supplies a portable pinned Lake project.
Neither author binaries nor dependency caches are release materials.
