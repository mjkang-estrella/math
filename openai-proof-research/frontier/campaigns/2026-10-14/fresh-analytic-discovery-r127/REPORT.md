# Analytic r127 outside report: T372L127 author proof sealed for independent review

Outcome: AUTHOR FULL PROOF SEALED FOR INDEPENDENT REVIEW. No correctness verdict, contribution verdict or campaign count is assigned. Campaign state remains 18/20, and publication and uploads remain stopped.

Runners: the round was started by GPT-6 Astra (high). A user stop interrupted it; there was no mathematical failure. Factory Droid (Opus 5.5, high) resumed and completed the round.

## Frozen theorem (unchanged, SHA256 6e39d59e65aecf9fc8710244c7eccbe7964e38af10287ad173663585539d790a)

Let Omega be any bounded connected open subset of R^3 with C-infinity boundary, and fix c>0 and M>0. Then there are C<infinity and alpha>0, depending only on Omega, c, M and the fixed Sobolev norms, with the following property. Let (lambda_j,mu_j), j=1,2, be any real smooth pairs on the closure of Omega with mu_j>=c, 3lambda_j+2mu_j>=c and ||lambda_j||_C1000+||mu_j||_C1000<=M. Let delta be the H^(1/2)->H^(-1/2) operator-norm distance between their full static physical displacement-to-traction maps. Then

||lambda_1-lambda_2||_Linf(Omega)+||mu_1-mu_2||_Linf(Omega) <= C [log(3+1/delta)]^(-alpha), with the right side read as 0 at delta=0.

The statement assumes no boundary agreement, collar, smallness, symmetry, finite-dimensional model or extra measurement.

## Anchors

- FINAL.json SHA256: bf1f7e54da87fa799201fa78c30a45bec7fdee6631ff14e9aaf78f66aa30c15f
- packet/MANIFEST.json SHA256: a48867c451ac1ebf79fc6fdf38472a7a39873f6346620f305a9e43c1e0b65af3. It lists 97 payloads and 21 directories, including the root.
- The SHA256 of this REPORT.md is detached: it is supplied outside this file.

Verification command (read-only, artifact integrity only):

    python3 packet/public/verify.py --root . --final-hash <FINAL> --report-hash <REPORT>

## What to read

Read packet/public/proof.md together with transport-calculation.md and boundary-calculation.md; these three files are the argument. The record of the resumed check is consistency-check.md, and the post-interruption clarifications are proof.md Section 9. For selection and timing, see prefreeze.md, other-screens.md, reading-limits.md and report.md.

## Resumption result

The resumed runner checked the proof against the frozen scope, both calculation files and the retained source372 contracts. It found no inconsistency. Nor did it find a gap that would need a new mechanism, a narrower scope or a conditional repair. It added seven disclosed clarifications without changing exponents, derivative budgets or the frozen bytes:

- bounded exterior components;
- the meaning of the H^-2 dual norm;
- explicit support radii;
- the support of the dbar derivative;
- independence of the comparison from h;
- the m=0 boundary step;
- a scratch numeric spot-check, which is not a gate.

## Remaining risks

1. Uniformity over the finite-regularity class (proof Section 2) is argued by finite-regularity compactness. This covers frames, plateaus, the Carleman and solvability constants and the supported estimates. The argument is not written line by line.
2. The derivative budgets are author counts with wide slack against C1000.
3. Parts of the boundary-layer error bookkeeping are described but not fully expanded. Lin–Nakamura was read only after freeze.
4. The weak-to-strong residual step (supported least squares, adjoint pairing, global direction patching) is the proposed integrated operation, and it needs combined review.
5. The source is stipulated, but the external primaries are not.
6. No substantiality claim is made, and the complete theorem may be technical.

## Integrity controls

The read-only verifier requires both the detached FINAL hash and the detached REPORT hash. It denies writes, network and subprocess use through an audit hook. It checks the exact payload inventory, the frozen and prefreeze bytes, the proof and record anchors, the complete 13223-entry tree, 41 canonical acquisitions (11 retained, with Git blob checks), 6 primary pairs, the history and context copies, and the search receipts. The copied mutation controls (controls/run_controls.py, receipt in controls/receipt.json) run only on temporary copies inside the owned directory, which are then removed. They test artifact integrity only and are never mathematical gates. The original root is hashed before and after the controls.

One control result was a genuine integrity finding. In the first full control run, a byte change to the private search hits, re-anchored consistently under a new detached FINAL, was accepted. The cause was that the verifier checked only hit structure, not the hit bytes. The verifier now binds the broad-prefreeze hits, inventory and receipt to fixed SHA256 constants. Those files were written before the freeze and were not changed. The packet was then resealed with the anchors above. Superseded seal: FINAL 919f013ae76875286301d8881cef8c2072a8f9c7ab139f85faeab0a4a6ab11a2, MANIFEST 59e1be49b43037195cb56de39591cc00eea8892e5fb73f10b243a93bd04b5a47. Another control, a re-anchored proof append under a new detached FINAL, is expected to be accepted. It shows that the detached FINAL hash, not the packet's internal hashes, is what binds the proof text.
