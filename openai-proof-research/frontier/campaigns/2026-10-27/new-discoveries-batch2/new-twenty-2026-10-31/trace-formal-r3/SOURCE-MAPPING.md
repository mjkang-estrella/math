# Exact formal statements and source mapping

`TraceFormal.literal_nonzero_matrix_relation` in FullCE.lean proves, for every field K of characteristic zero:

    (relation48 : MvPolynomial (Fin 48) K) ≠ 0 ∧
    (relation48 : MvPolynomial (Fin 48) K) ∈ actualIdeal

`actualIdeal` is the kernel of simultaneous evaluation on **all full 3x3 matrix triples**, with the 45 literal source centered generators at indices 0..44 and tr(X),tr(Y),tr(Z) at indices45..47. This is a genuine specialization kernel, not a finite proxy. `relation48` is six times the r2 polynomial p, with source Ti indexed i-1. Its abstract separator is T1=6,T35=1, others0, giving6. The polynomial is homogeneous of source multidegree(3,2,2); this grading assertion is not yet a formal theorem.

MatrixRelation.lean proves the corresponding traceless identity over arbitrary characteristic-zero fields by 40 actual fundamental matrix identities: 16 q summands and 24 lower-product witnesses. The cyclic trace rewrites are proved from trace_mul_comm and associativity. No lower-identity membership premise is assumed. TraceFormal.lean proves the full-matrix alternating FTI over every commutative ring by actual 3x3 entry expansion and ring normalization.

FullCE.lean contains all45 printed generator formulas, not merely E1..35. Entry44 matches332311. SampleEvaluations.lean checks945 exact values of those formulas at the21 actual integer traceless matrix triples used by the80 certificates. EvaluationTables.lean proves the corresponding80 monomial evaluation tables exactly. InverseCertificates.lean checks their scaled inverse products with kernel `decide` and a proved checker-soundness theorem. InverseSound.lean connects the checker to genuine integer Matrix multiplication and proves a generic field injectivity lemma from a scaled right inverse.

FixedList.lean contains107 literal occurrences from Theorem4.1, preserving repetitions; their ordering is table-row extraction. Six letter permutations implement Remark4.2. Its kernel theorem identifies exactly the two degree-(3,2,2) tuples. This is a finite-list theorem, not an ideal-generation theorem.

ReductionData.lean stores the literal rational coefficients of P0-47Q/864 as integer numerator/positive denominator and trace factors. Its theorem checks all terms use each label1..7 once and all factors have length<=6 with at most one7. These are syntactic properties, not a matrix identity or normalization proof. Recursion.lean proves the actual list substitution strictly shortens such proper factors.

The missing full endpoint is the non-generation statement for the Ideal.span of the literal fixed Rstar(F(tuple)) list inside this actualIdeal, for a proved source-admissible Rstar. No theorem bearing that claim is present. The precise missing semantic lemmas are listed in unresolved-semantic-lemmas.json. No abstract conditional result is called a full resolution.

Pinned dependencies: Lean4.34.1, commit5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, dependency revisions in formal/lake-manifest.json. Replay uses existing cached package builds, whose locations are in deps.json/env.sh. It creates formal-source.zip, extracts it afresh inside this lane, removes local oleans and compiles every source with warningAsError, <=2CPU and -M6000. Run `bash replay.sh`; see strict-replay.log. Audit.lean prints axioms for all945 sample checks, all80 table and inverse certificates, and the semantic theorems.
