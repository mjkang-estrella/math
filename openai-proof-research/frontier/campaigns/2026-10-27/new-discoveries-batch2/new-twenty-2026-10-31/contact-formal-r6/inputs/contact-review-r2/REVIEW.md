# Final formal-fidelity review: MathDB 365301

Recommendation: **HOLD for a local-definition repair; zero acceptance credit.** This is an independent review, not acceptance. The ordinary five-vertex counterexample passes. The Lean proof of its stated proposition has no identified proof hole. However, the general contact predicate is not a faithful local definition for arbitrary inputs: its unrestricted existential neighborhood can include a different boundary singularity. This defect is inherited from the earlier review's proposed definition, rather than introduced by r5. The final fidelity gate must catch it regardless of provenance.

## A. Definition fidelity: FAIL in general; candidate mathematics survives

I read SourceContact.lean line by line against the preserved primary bodies: arXiv:2410.10695, Sections 2.2, 4 and 6, and Bickel–Hong, equations (4)–(6), Section 3.1, equations (12)–(13), Remarks 3.1–3.2. These are actual source-body reads. The cached HTTP receipts report status 200 with SHA-256 bindings; no new HTTP access or new novelty clearance is asserted.

**Resolvent: PASS.** SourceContact lines 48–57 use adjacency minus the color diagonal and the diagonal entry of its inverse. True means z and false means w. There is no reciprocal or sign swap. Lean's totalized inverse away from nonsingular matrices is harmless here: the certificate represents the function on the open bidisk after betaInv, and BidiskStable proves Q nonzero there. GraphResolvent supplies the actual five-vertex matrix, determinant and cofactor. The witness is connected, has both colors, and has a z root.

**Distance: PASS, with deliberately restricted domain.** Lines 77–80 require an attained w-reaching walk of length d and a lower bound on every such walk. This is exactly finite shortest-path distance. An empty reachable w class, including the no-w case, supplies no d; an unreachable w in another component does not contribute a walk. A w root has distance 0. These conventions restrict the conjecture's scope rather than inventing a finite distance. They do not make the witness vacuous: nearest_w_one proves distance 1 explicitly.

**ReducedCertificate: PASS.** Lines 63–73 require a nonzero stable polynomial denominator, common-divisor reduction over C[Z,W], equality to beta(f(betaInv Z,betaInv W)) throughout the open bidisk, support bounds, unit-norm phase and coefficient reflection. The support bounds prevent truncated natural subtraction in reflect from changing its meaning. Bounds rather than exact degrees permit precisely the extra monomial factors in Bickel–Hong equation (6): reflecting in enlarged degree multiplies by Z^a W^b. At (-1,1) these are local units. Thus this is not an illicit degree relaxation. The candidate has actual degrees (3,2), phase 1 and an unconditional certificate.

Equality on the open bidisk and polynomial reduction determine the rational function and its reduced pair up to nonzero scalar. A zero numerator cannot satisfy the reflection of a nonzero denominator with unit phase. Constant inner functions cannot provide the required boundary numerator zero. No spurious-certificate or cancellation shortcut was found.

**Point and maximum convention: PASS.** The maps beta(v)=(1+iv)/(1-iv) and betaInv(v)=i(1-v)/(1+v) are the source maps. Their coordinatewise action sends (infinity,0) to (-1,1) independently of the graph. No graph-dependent output normalization moves that input point. This does not say that every graph has a singularity there; the contact hypothesis restricts to those that do. Bickel–Hong Remark 3.2 uses the maximum of matched local branch orders. Infimum radial height gives this maximum, not a minimum of exponents. The direct zero-set route avoids depending on a generic-level theorem in Lean.

**Locality of HasZeroSetContact: FAIL.** Lines 13–21 existentially choose any positive rho. They do not require the upper witness to approach tau2, nor allow the neighborhood to be made arbitrarily small. The boundary-zero clause q(tau1,tau2)=0 does not link the witnesses to that zero. The predicate can measure another boundary point in the same rho ball. Consequently it can hold for several K at the same named point, even for a reduced stable rational-inner pair.

Here is an explicit diagnostic using the submitted polynomials q6=bidiskNumerator and p6=bidiskDenominator. Define

    p*(Z,W) = p6(Z,-W) (2+Z-W),
    q*(Z,W) = q6(Z,-W) (2ZW+W-Z).

The denominator is stable: p6 is stable, and |Z-W|<2 on the bidisk. The numerator is the reflection of the denominator in bidegree (4,3); reflection commutes with W -> -W here because p6 has W degree 2. The pair is reduced; independent exact polynomial gcd checks verify this, including the cross factors. This is therefore a legitimate reduced rational inner pair, not an arbitrary analytic function or an inserted common factor.

At Z=-1, q6(-1,W)=-8i(W-1)^2. Thus the q6(Z,-W) roots converge to W=-1 and have heights of orders 6 and 2 by the submitted complete branch analysis. The remaining factor has root

    W = Z/(2Z+1),

which converges to W=1. On |Z|=1, setting h=|Z+1| gives |2Z+1|^2=1+2h^2. Hence this root has height 1-1/sqrt(1+2h^2), comparable to h^2, with quotient by h^2 tending to 1. The true local contact at (-1,1) is therefore 2.

Nevertheless the existing predicate at (-1,1) admits BOTH K=2 and K=6. Choose rho=1 and shrink delta: only the root converging to 1 contributes, giving 2. Choose rho=3: every point in the disk is included, so the sixth-order roots converging to -1 supply the upper witness; all other heights are bounded below by a positive multiple of h^6. This gives 6 at the same named point. The unrotated product and the rotated pair's coprimality are checked in scripts/independent.py. The asymptotic comparison above is an ordinary proof, not a newly compiled Lean theorem.

I have not claimed that this diagnostic product is itself a graph resolvent. It conclusively refutes the general predicate's stated interpretation for reduced rational inner certificates. A separate graph-class theorem excluding this contamination would be an alternative repair, but none is present. Therefore one cannot justify the universal statement's fidelity solely by saying its extra hypotheses weaken the source: that inference requires a genuinely local contact hypothesis.

**Effect on this witness:** the actual q6 has only W=1 above Z=-1. Its exhaustive roots tend there, and RootLocalization/CayleyLocalization establish arbitrarily small witness neighborhoods. Thus this review finds no wrong-point or false contact computation for the five-vertex graph. The mathematical refutation survives; the literal formal definition needs correction before exact-source acceptance.

**SourceConjecture: HOLD pending that repair.** All n, finite simple graphs, Boolean colors, roots, certificates, d and positive even K are explicitly quantified. Fin n covers all finite graphs up to relabeling. No candidate jets or branch-equality assumptions occur in the conjecture. With a repaired local contact predicate the contact-existence and nearest-distance hypotheses are legitimate restrictions; negating that restricted assertion is sufficient. As currently written, the locality loophole prevents the advertised general correspondence. HasHalfPlaneContact has the analogous existential-radius issue, although the final endpoint uses the bidisk predicate and the concrete half-plane roots all converge to zero.

## B. Mathematics spot check: PASS

The independent script computes the determinant and cofactor of the displayed graph matrix and obtains exactly N and Q. It verifies the cleared level equation, the slope-one jet through degree 6 and slope-three jet through degree 2 by exact residual cancellation, the R clearing identity, and the residual coefficients -17/2+i and 6-4i. The analytic divided-difference denominators have nonzero values 2 and -2, so these residual calculations imply convergent analytic remainders rather than merely formal jets. Imaginary pole orders are 6 and 2 with negative leading coefficients -1/2 and -2. Exhaustiveness and uniform lower bounds correctly turn the sixth-order branch into the infimum-height exponent.

The script also independently checks coprimality of the global bidisk pair, its actual bidegree and the phase-1 reflection identity. I checked the explicit Cayley comparison: conjugation sends lower-half-plane pole roots to upper-half-plane numerator roots; the height bounds and real circle chart yield lower constant 1/512 and upper constant 16. The proof explicitly avoids x=0 and exceptional chart denominators. Contact-two exclusion localizes the sixth-order witness inside any asserted contact-two neighborhood. The paper's ordinary local counterexample is sound.

## C. Lean and replay evidence: PASS within review scope

I read all 28 modules, totaling 2,012 lines, including all five audit modules. No sorry, admit, added axiom, native_decide, unsafe proof, hidden branch hypothesis or surrogate endpoint was found. The keyword scan matches only rejection messages in the audit code. local_sqrt_one uses the analytic inverse function theorem; quadratic branches are exhaustive; analytic remainders and exact orders are proved; the global certificate is unconditional. Refutation.lean applies refutation_of_bidisk_contact to bidisk_contact_six. The earlier conditional implication is not being passed off as an unconditional result.

I inspected both the r5 fresh-extraction and manuscript fresh-replay receipts and independently compared their source hashes to all 28 current formal modules. Each set contains 69 receipts: 28 strict compilations, 28 separate leanchecker invocations and 13 negative controls. Successful jobs return 0; negative controls return 1; none reports a resource kill. Maximum recorded sampled RSS is 4,624,683,008 bytes in r5 and 5,027,528,704 bytes in the manuscript replay; maximum job wall times are 39.21 and 33.28 seconds. The inventory has 314 declarations, no unsafe or partial declarations, and only propext, Classical.choice and Quot.sound. The manuscript source-only zip passes CRC checking and contains byte-identical formal sources.

These are verified supplied replay records, not a new independent compilation. I ran no Lean process and did not run the full replay, as instructed. Cached dependency binaries remain a stated trust boundary; no dependency-source rebuild is claimed. The locality objection is semantic and is not something kernel checking or the existing negative controls can detect.

## D. Manuscript: QUALIFIED_PASS; formal-correspondence claim needs repair

I read all eight PDF pages and the source/proof/correspondence text, rendered all pages and inspected both four-page sheets. No clipping, missing mathematical lines or unreadable glyphs were found. Pages 1–5 correctly present the graph, quotient, analytic branches, direct zero-set proof and Cayley estimates. Page 6 accurately quotes the existing Lean formula, but calling its predicate a general local comparison and claiming that the extra hypotheses only weaken the source needs correction after Gate A. Pages 7–8 candidly state binary-dependency, source-journal, search, unindexed-literature and bounded-priority limits. No new novelty acceptance is inferred here. The manuscript has no priority claim and explicitly reserves acceptance to root.

The requested lowercase statement-correspondence.md does not exist in r5; I reviewed and bound the actual STATEMENT-CORRESPONDENCE.md. This naming discrepancy is administrative, not mathematical.

## Required next actions

1. Repair the contact predicates so witnesses genuinely localize at the specified second coordinate. For example, require the two-sided comparison in arbitrarily small positive neighborhoods (each with a sufficiently small parameter interval), or impose and prove an isolation condition selecting the local zero cluster. Merely imposing rho<1 does not solve the general issue: distinct boundary points can be closer than 1.
2. Reprove contact six using the already available arbitrary-neighborhood localization, and rederive the literal refutation for the repaired SourceConjecture. Add a regression showing that the diagnostic pair has local contact 2 at (-1,1) and cannot borrow order 6 from (-1,-1).
3. Update the correspondence and manuscript page 6; obtain a fresh source-only extracted replay and a bounded independent check of the repaired definition. No new mathematical search is needed for the five-vertex example.
4. Root alone adjudicates acceptance and the previously documented novelty limits. This review grants no credit and edits no ledger.

## Scope and artifacts

New files are confined to contact-review-r2. No children, git, external messages, browser tabs, uploads, publication or shared ledger edits were used. No background job remains. scripts/independent.py and logs/independent.log retain exact algebra, locality diagnostic, archive and receipt checks. logs/paper-pages.txt and page images retain the complete manuscript read. Input manifests bind all requested input groups before and after; the supplemental before manifest includes the actual uppercase correspondence filename. Hash verification is recorded separately. Light read commands were short; substantive computation used two-CPU affinity, CPU 120 seconds, a 6 GiB address-space cap, MALLOC_ARENA_MAX=2 and wall timeout 140 seconds. Computations ran serially.
