# H019 coordinator disposition

2026-10-08. **Accept the finite implementation and individual certificate after
independent review. Preserve the overall INCONCLUSIVE experiment outcome.**
Verified full factoring complexity improvement: NONE.

The [original finding](H019-root-certificate-screen.md) records the single
frozen trial: five correct controls, one research pass, three unknowns, zero
verification failures/errors/timeouts/unstarted cases, 5.834619 seconds.
Only the 262144-bit, degree-52 case passed the fixed count comparison.
The preregistration required both largest inputs; its criterion is unchanged.

The [independent review](H019-independent-review.md) found no defect requiring
revision. Its separately frozen arithmetic replay verified all nine outcomes,
all 115 research disks and all four exact count comparisons in 3.500754 seconds
(3.496181 through sealing), with zero failed/error/timeout/unstarted cases.
It reconstructed the N inputs and base polynomials, checked the prime and
modular Bezout certificates, full-root Rouché accounting, Gaussian Taylor
predicates, pair/triple geometry, and huge count-product operands/hashes.
It did not rerun Aberth, import original arithmetic modules, or change evidence.

For the one archived N, its verified degree-52 f, and H=2^328, the recorded
790-bit C bounds the number of primitive irreducible positive-leading quadratics
in the stated height box satisfying the exact global-resultant cutoff.
The bound is an upper count, not an exact cardinality or factor output.
The three other trial expressions are not certified population bounds.

The parent read the complete 136-line review and checked all 76 review-frozen
files, all 37 owned file hashes, all 30 sealed replay files and the completion
link. All match. Review freeze SHA-256:
8d5e1621830052c706db3fdbc68d6919db749c40fb23fee9d93ab9891f54b5be.
Review seal SHA-256:
a6f8dc6837a96224950ff78f81995feefe7ab504aac580c585717b353e46d5a2.
The earlier original-evidence verification also passed. Hashes establish byte
correspondence, not independent historical proof of every pre-freeze action.

Keep the finite scope: public odd inputs without a semiprime/hardness promise;
square-free f, not certified irreducible f; primitive irreducible g only;
reducibles and contents require their separate accounting. No field-selection
frequency, uniform asymptotic geometry, useful-relation supply, rank or proper
splitting theorem follows. Unknown sufficient comparisons do not establish
positive supply or refute H017. There is no Lean refinement of this verifier.

Shared checks passed after the original code handoff: 12 Python tests, Lean
source screen, seven-job build and axiom audit. The later review introduced
only exclusive audit artifacts and no shared-code or Lean changes.

No larger parameter sweep or criterion repair is authorized by this result
itself. A later study requires a new substantive question and preregistration.
Current priority is the separate H021 generator review and H022 model review.
