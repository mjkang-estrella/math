# Candidate verdict

No strong eligible candidate was found. No Lean packet is supplied: there is no novel full-scope endpoint to certify. All entries have zero accepted credit.

## 363447: complete ordinary proof, excluded as routine

Let A be any real symmetric n-by-n matrix, with least eigenvalue lambda and nonzero eigenvector v. Let i,j be the attachment coordinates of the two copies. The new matrix is

B = diag(A,A) + (e_i - e_(n+j))(e_i - e_(n+j))^T.

The update is positive semidefinite, so its least eigenvalue is at least lambda by the Rayleigh principle. Choose real a,b, not both zero, solving a v_i - b v_j = 0. Such a pair exists because this is one homogeneous equation in two unknowns, including when both coordinates vanish. Then w=(a v,b v) is nonzero, diag(A,A)w=lambda w, and the update annihilates w. Thus B w=lambda w, proving equality. The disjoint union also has minimum eigenvalue lambda. Apply this to the source's port-perturbed path matrix; the path length, optimality, and smallness of epsilon are unnecessary.

This proves the exact source claim, but the entire new argument is the elementary repeated-eigenspace rank-one-update observation plus the classical Rayleigh bound. Under the binding brief's routine-bridge rule it is excluded, not a strong discovery and not a reason to consume Lean capacity.

## Other apparent easy results

373726 is a source-corrected old statement. The October 2026 v4 prints both the corrected delta-(k-1) bound and the transitive-tournament obstruction. 374723 is already refuted by its own source. 367384 is explicitly proved in its source. 367448 and 376144 are the same already-solved family. 357804 is implied by the later unique-extremal theorem on a wider parameter range. These are not new candidates.

357547 is excluded by the current public Omega full-scope result: CyclicMorphismAttractorMinimum.result, manuscript Theorem 1.15, with source Proposition 34(3) giving the precise coefficient hypothesis. Primary manuscript and implementation source are retained. Its upstream machine-check claim was not replayed locally.
