# Strict connection–Dirac spectral dominance for every finite graph

One general theorem: for every nonempty finite face family closed under nonempty
subsets with all faces of size1or2, and every1<=k<=#faces,

    S_k(L)-S_k(D) >= sqrt(2)-1 > 0.

L is the literal simplex-intersection matrix. D is the literal signed simplicial
boundary Dirac matrix, with the canonical orientation determined by the vertex
order. S_k takes the k largest signed eigenvalues with multiplicities. Isolated
vertices, disconnected graphs, unused ambient vertices, and triangle boundaries
are included. All graph/block/face identifications are proved reindexes in Lean.
There are no residual rank, inertia, or eigenvector-existence hypotheses.

This establishes the full dimension-at-most-one case of Knill2601.18071v2
Conjecture1 /MathDB372758 with a uniform strict gap. The higher-dimensional
question remains unresolved by this work. No optimality of the gap is asserted.
The known hydrogen identity and variational tools are credited; known g=L^-1
and spectral-radius counterexamples are not discovery credit. One outcome only.

The complete proof has211declarations in17modules. After extraction reproduce:

    python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/pinned/.lake/packages

verification/pins.json binds Lean4.34.1 and all dependency revisions. The verifier
copies and compiles every source afresh with warningsAsError, checks every type
and axiom report, and rejects proof holes. Only propext, Classical.choice and
Quot.sound occur. Parent and independent final-review receipts are byte-identical.
The optional scripts/check_graphs.py needs NumPy and supplies supporting numerical
checks, not a substitute for the full proof.

All five independent review gates passed. Exact source and prior-art access limits
are retained in reviews/. The paper is three pages; its exact reviewed bytes are
unchanged. provenance.json, FORMAL-PROGRESS.md and frozen-parent-hashes.json are
historical parent-freeze records (credit0 pending review at that time), not final
acceptance records. reviews/parent-addendum.md describes current integration.
final-review-hashes.json binds current theorem and manuscript files. MANIFEST.json
binds the complete archive payload. Acceptance is controlled by the campaign
ledger and the external final archive receipt after fresh extracted replay.
