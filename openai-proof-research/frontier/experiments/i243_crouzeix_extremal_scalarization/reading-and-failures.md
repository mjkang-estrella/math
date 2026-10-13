# I243 — reading record, failed routes and analytic validation

## Scope

All work stayed in `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Read the root `AGENTS.md` and `sources/upstream.json` in full, and family 325's two catalogue entries at `sources/CONTENTS.md` lines 7929–7947 with one trailing line of context. The immutable source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every pinned theorem and lower operation was accepted as stipulated; matching provenance hashes is not a source-truth audit.

Only the assigned I243 report, analytic note, reading record, authentication JSON, literature index and fully read excerpts were written. No subordinate agents, live I241/I242 or other sibling contents, shared ledger edits, staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots or seals were used. An initial filename inventory was broader than necessary and returned historical filenames; no contents from those paths were opened. Subsequent local reads were narrowly targeted to the authorized I238 literature, required guidance/catalogue, and I243 files.

Short Python invocations performed retrieval, primary-text extraction and provenance hashing only. They did not evaluate any matrix family or mathematical inequality. All mathematical validation was by the symbolic arguments recorded in the analytic note.

## Primary reading

1. **Pinned direct proof.** Read `thm:main`; all of Sections 2 and 3, including exterior coordinates, Faber coefficients, positivity, both coefficient inequalities, original-matrix resolvent, both ordered products, reciprocal weights, and positive-block comparison; read `lem:approx`'s statement. The full relevant Sections 2–3 and the two needed statements are retained. The new proof uses those lower operations exactly, including their unnormalized Hilbert–Schmidt norms and normalized angular measure.
2. **Pinned structural companion.** Read coordinate/evaluation conventions, conformal-coordinate lemma, optimal-metric and common-representation statements; all of Section 2, including feasibility, optimality, common density, separation, endpoint support, balance and the finite unitary realization. Retained precisely those passages. The companion does not state the new four-dimensional equality result. Its strictly enclosing-domain metric is not presumed to be an equality metric for W(A).
3. **ACV arXiv:2608.27346v3.** Fully read and retained Sections 2, 5, 7 and 11, and Theorem 1.3. These include exact quotient norms, rectangular attainment, the complete first-variation proof, the reason for the dimension-three restriction, scalar/column/row equality, the scalar polynomial classification, and inverse-algebra caveats. Section 11 was first read in the authorized I238 retained text and then extracted into I243 from the primary HTML. No theorem about matrix-valued output rigidity is asserted by the portions used.
4. **Hartz–McCarthy arXiv:2606.02922v1.** Fully read and retained Section 4, including its sequence version of the variational lemma and proof. This establishes the prior-art ownership of the constant-matrix ball-automorphism argument.
5. **Jin, Rigidity at the Extremal Crouzeix Constant, v2.** Read the primary abstract, introduction and Theorem 1 through the web rendering. Retained only the theorem statement and accurate access notes, not an unread full proof. The scalar disk theorem is an explicitly external dependency. ACV Section 11's application of it was also fully read. The proof does not pretend to derive this all-dimensional scalar theorem anew.
6. **BCD Section 5.2.** Read the complete retained primary excerpt in the authorized I238 literature: Theorem 5.2, proof, Corollary 5.3, proof and Remark 5.1. This rules out treating the final two-dimensional ellipse reduction as a new estimate.

Three targeted public searches screened the phrases complete equality/dimension four, complete rigidity/four, and positive-rank extremality. No matching four-dimensional equality theorem appeared. Search snippets were not used as mathematical premises and no unrelated source copies were retained. This is a bounded overlap check, not a full literature priority search.

## Route changes and corrected failure modes

- **Scalar rigidity of P[A].** Rejected from the start. The supplied (1,2,1) weighted chain remains a counterexample, including after embedding the base into dimension four. The successful proof instead concerns the rank of the original-A positive resolvent at a supporting line.
- **Simple substitution of dimension four into ACV.** Insufficient. Their rectangular reduction leaves a genuine 2-by-2 matrix level. Their dimension-three monogenic contradiction does not automatically eliminate it. The quadratic-column lemma handles rows/columns only, and is not treated as the full result.
- **A bare minimal-polynomial condition.** The paid auxiliary invariant nu(A)=sum floor(r_A(lambda)/2) controls the square-zero ideal and scalarizes columns when nu<=1. It does not by itself eliminate complete 2-by-2 witnesses. No standalone complete theorem is inferred from it.
- **Optimal-metric endpoint assumption.** One could scalarize an extremal if a suitable endpoint eigenspace were one-dimensional, but there was no intrinsic reason to assume that. This route was abandoned. The final proof uses the source's direct positive-block slack and needs no new metric hypothesis.
- **Vanishing normalized slack without a uniform bound.** Insufficient. The direct residual initially gives only E_B/a^2 ->0. The new exterior derivative bound |h'|<=4c and interior-spectrum resolvent bound make a^2 uniformly bounded, paying the absolute limit E_B->0. This is the essential new analytic step.
- **Passing Faber series to a nonsmooth limit.** Avoided. Every series identity is applied separately on a regular analytic outer domain. The limiting argument needs only compact support-point convergence, a positive arc length, and the uniform resolvent/derivative estimate. No coefficientwise or derivative convergence at corners is assumed.
- **Boundary-spectrum reduction losing the original domain.** Corrected explicitly. A scalar extremizer bounded on W(A_0) need not be bounded on K=W(A). The proof applies the quotient column argument on the original K, and so keeps precisely the required supremum norm.
- **Changing vectors while taking polynomial lifts.** Avoided. Finite-dimensional polynomial correction provides exact-evaluation lifts of one quotient extremal. Its singular pair and full Schmidt ranks stay fixed in every outer-domain calculation.
- **Confusing polynomial degree with minimal-polynomial degree.** Avoided. The unrestricted theorem allows unbounded polynomial lift degrees. The separate quadratic theorem preserves degree by compressing the original coefficients. The Crabb C_3 example shows why this distinction matters.
- **General Kippenhahn reducibility.** Not assumed. The repeated top/bottom eigenvalues in order four give two double eigenvalues and explicit two-generator Hermitian relations. The resulting block calculation is written out; no higher-dimensional version is claimed.

## Symbolic validation checklist actually completed

- Verified the exact residual identity including the factor 3 on ||Y*X||_HS^2 and both product orders.
- Verified exterior tangent orientation, the sign in the integrated Herglotz formula, normalized measure, and the bound 4c.
- Verified a^2 = integral ||Y*R X||_HS^2, and the uniform estimate using unit Hilbert–Schmidt norms and boundary resolvent separation.
- Verified tr(DJDJ)=||D^(1/2)JD^(1/2)||_HS^2, the isotropic dimension bound and the compression rank estimate k-1.
- Verified that a simple-support interval cannot have a constant support point when the spectrum is interior.
- Verified support-point convergence without boundary smoothness of K, and the arc-length lower bound with the factor (2 pi)^(-2).
- Verified the four-dimensional repeated-pencil diagonalization, including its segment degeneracy.
- Verified all quotient and actual-polynomial quantifiers separately, including exact polynomial correction and degree preservation.
- Checked the weighted-chain obstruction and the C_3 quadratic nonattainment obstruction symbolically. No numerical values were sampled.

These are analytic checks, not software tests or a formal proof-assistant verification. No independent external reviewer was invoked under the no-subagents instruction.

## Retrieval limitations

The first extraction attempt tried `lxml`, which is not installed; it failed before writing an excerpt. It was replaced by Python's standard `HTMLParser`. No package was installed. One pinned-excerpt extraction used a missing starred subsection marker; it was corrected and rerun. No source conclusion depends on either failure.

Full primary transports are not retained. Pinned source transport hashes and Git blob hashes, exact retained ranges, local guidance/catalogue provenance, and all final I243 output hashes except the authentication file's own hash are recorded in `input-authentication.json`. Its own detached hash is supplied in the final return.

## Disposition

Theorem 4 is a proved new-to-this-record complete equality result, materially beyond the cited dimension-three statement and beyond the excluded direct-sum/ellipse calculations. Theorem 4Q provides the requested scalar quadratic witness. The argument remains explicitly dependent on the stipulated complete proof and the externally cited scalar-tuple theorem; literature-wide originality has not been certified. Submit the candidate for parent review without changing the count of nine accepted findings.
