# Independent preliminary review

Recommendation: **EXCLUDE from substantive discovery credit under the campaign's routine-adaptation rule**, conditional on root adopting the explicit method bridge below. This is not a claim that an earlier publication already refuted the conjecture. If root regards the common-coefficient extraction as a substantive new idea, the alternative is HOLD for bounded novelty completion, not acceptance. Counts remain 9 additional / 39 total / next 40; root alone adjudicates.

| Gate | Decision |
|---|---|
| SOURCE | PASS: literal universal maximality claim in v1, v2 and published body |
| MATH | PASS: entire closed simplex, every n >= 1 |
| SUBSTANTIVE | FAIL recommended: complete elementary finite-envelope/recurrence bridge exhibited below |
| NOVELTY | HOLD: no exact earlier refutation identified; registry/history coverage incomplete |
| FORMAL-FEASIBILITY | PASS in principle only: finite polynomial identities and strong induction; no Lean written or replay claimed |

## Source and quantifiers

Frozen original/copy bindings precede scientific reading in this review. See freeze-record.json for original paths and SHA256. Actual arXiv v1 (2 July 2023), v2 (1 May 2024), and the complete published PDF were read. Journal correspondence is Mathematics and Informatics 67(2), 2024, pp111–118, DOI 10.53656/math2024-2-1-pro; the publisher body, not its abstract, confirms the claim. Crossref records print 29 April 2024, online 30 April 2024, with a later 9 June 2025 deposit. The deposit is not the publication date. Current arXiv landing page still identifies v2 as latest on this review's 30 October 2026 access.

The source uses iid positive integer increments supported in {1,...,k}, allowing zero masses, sum p_j=1; u0=1 and u_n=sum_{j<=min(n,k)} p_j u_{n-j}. Its domain A_k is the closed (k-1)-simplex. Its polynomial class (call it script-A_k to distinguish it from the domain) consists of real polynomials in p1,...,p_{k-1}, total degree at most k-1, below m_k=min_{n>=1}u_n on the whole domain. The order is pointwise non-strict inequality. Maximality means a member dominating Q_k must equal it. It does not mean merely that no polynomial has a larger value at one selected point.

Conjecture 3.7, v1 p4, v2 p5, journal p115: for every k>=3, Q_k is maximal in script-A_k, and largest in the specified smaller class. Definitions are v1 pp2–3, v2 pp2–3, journal pp112–113. The k=4 construction refutes the first assertion and hence the universal conjunction. It does not assert failure for every k or classify maximal elements.

The printed max in the minimum clause of Proposition 3.1 is inconsistent with definition (2.4), Corollary 3.4 and surrounding prose. The present proof is independent of this error: it proves P<=u_n for every n. It would also work with infimum. The journal's commentary saying no maximal element is likewise not the theorem's no-largest assertion; neither commentary typo is used.

## Universal proof independently checked

Write x=p1,y=p2,z=p3,w=p4, t=x+y+z, with all four nonnegative and t+w=1. Let Q=x(x+y)t and P=x²t+xy. After eliminating w this is a polynomial of total degree 3 in precisely the allowed three variables; P-Q=xyw>=0. At the uniform point Q=6/64 and P=7/64, so they differ as polynomials and functions.

Direct recurrence expansion gives u1=x,u2=x²+y,u3=x³+2xy+z. Exactly,

    u1-P=x(1-y-xt),
    u2-P=x²w+y(1-x),
    u3-P=xy(1-x)+z(1-x²).

Since xt<=x and x+y<=1, all three gaps are nonnegative. Also 0<=P<=u1<=1. At n=4, u4=w+xu3+yu2+zu1>=w+(1-w)P>=P. At n>=5 all four predecessor indices are positive and smaller, so strong induction and sum p_j=1 give u_n>=P. No division, positive-mass, aperiodicity, limit theorem or attained-infimum assumption is present.

This includes x=0 (P=Q=0, even for periodic laws), w=0, y=0, z=0, all intersections of faces, and all four vertices. Strict improvement is needed only somewhere, not on faces; xyw>0 gives it, including interior points.

For the homogeneous certificate put s=x+y+z+w. Homogenized initial masses of degree3 are U1=xs², U2=x²s+ys², U3=x³+2xys+zs². Homogenized P is x²t+xys=Q+xyw. Independent exact expansion reproduces every listed monomial/coefficient in the candidate. check-results.json retains these expressions. Nonnegative coefficients prove the inequalities on the nonnegative orthant; evaluating s=1 connects them to the renewal masses. The rational grid (455 points, denominator12, times1–32) is diagnostic only.

## Strongest substantive objection: a complete transferable bridge

This objection is stronger than shortness, positivity in general, an available algorithm, or an unsuccessful literature search. It supplies a concrete construction directly from the source's finite-envelope and positive-recurrence setup, and in fact produces a stronger improvement without guessing the candidate P.

Elementary coefficient-subtraction lemma: if homogeneous polynomials D_i=U_i-Q have nonnegative coefficients and the coefficient of a monomial M is at least c>0 in every D_i, then U_i>=Q+cM throughout the nonnegative orthant. Proof: subtract cM from each coefficient list; every coefficient remains nonnegative. On a probability simplex, an initial bound B=Q+cM<=u1,...,u_{k-1}, with B<=1, propagates by the source recurrence: u_k>=p_k+(1-p_k)B>=B and thereafter convex combinations preserve the bound. Thus this is a finite polynomial-minorant improvement method with a complete all-time bridge, not an appeal to an optimization package.

Here the actual three source-data gaps, computed from recurrence (2.2) and product (2.5), are

    D1=w²x+2wx²+2wxy+2wxz+x²z+xyz+xz²,
    D2=w²y+wx²+2wxy+2wy²+2wyz+xy²+xyz+y³+2y²z+yz²,
    D3=w²z+2wxy+2wxz+2wyz+2wz²+xy²+3xyz+2xz²+y²z+2yz²+z³.

All coefficients are nonnegative, and their common support is {xyw,xyz}. The monomial xyw, which vanishes on the terminal face w=0, has common minimum coefficient 2. Coefficient subtraction therefore outputs B=Q+2xyw immediately. It has degree3 after w=1-x-y-z, B>=Q with strict inequality when xyw>0, and B<=u1,u2,u3, hence B<=u1<=1. The preceding recurrence proof supplies every later n. The proposed P is (Q+B)/2, so its admissibility also follows by convexity from this explicit stronger bound and Q. This is the complete instantiated bridge behind the routine-adaptation recommendation; no infinite search, numerical optimization or unproved approximation theorem is hidden in it.

The source's Proposition 3.1 proof uses precisely positive recurrence propagation; Proposition 3.3 derives polynomial masses from that recurrence; Corollary 3.4 supplies the finite envelope; Proposition 3.5 establishes Q via positive recurrence induction. The new coefficient operation is elementary algebra on their explicit objects. It is not stated as a theorem or counterexample in the source. Root must decide whether this concrete adaptation falls below the campaign's substantive threshold; historical nonnovelty does not follow merely from it. The stronger B is review evidence, not a separate proposed outcome or credit claim.

## Proposition 3.8 and the smaller class

The full relevant preceding arguments and Proposition 3.8 proof were read in both versions and journal pp115–117. The latter first uses the k=3 envelope min(x,x²+y), degree<=2, vanishing on x=0 and equality along y=0 to force any dominator to x(x+cy); approaching x=1 forces c=1. It then uses cumulative-specialization degree and a quadratic Hessian determinant/boundary maximum argument for largestness. Neither step proves maximality in degree3 with an extra coordinate. Its quadratic boundary obstruction leaves room for a cubic perturbation. It does not itself construct xyw; the explicit bridge above does.

There is an ancillary printed algebra error: for P=ax²+bxy+cy²+dx+ey+f, degree<=1 of P(x,1-x) requires b=a+c, not the printed 2b=a+c. With the corrected relation the printed determinant identity 4(a-1)c-(b-1)²=-(a-c-1)² is valid. This review does not import that incorrect coefficient relation. It also does not inherit unrestricted claims about degrees of all later masses from Proposition 3.3.

In cumulative coordinates X=x,Y=x+y,Z=x+y+z, the proposed P becomes XY+X²(Z-1). Its specialization degrees are 1,2,3. Thus it satisfies the displayed v2 and journal smaller-class definition, taking the natural cumulative-coordinate interpretation of the source's misindexed substitution. The v1 prose termwise prefix restrictions would instead exclude X²Z. Those restrictions are not equivalent to specialization after cancellation. No conclusion is made for that stronger intended termwise class. The primary maximality result is unaffected, and survives unchanged in the published body's unrestricted script-A4. It is consequently a true full-scope refutation, not merely an excluded typo/formulation correction.

## Novelty limits and recommendation

The actual closest prior proof bodies covered here are both source versions and their published correspondence, all before this candidate. The source references Feller 1967, Feller 1970 and Mitov–Omey 2014; their actual book bodies were not newly accessed here and no specific theorem in those books is asserted to subsume the construction. Frozen scout arXiv query responses were inspected as search metadata only, not as proof bodies or clearance. Their many unrelated hits do not establish novelty. No later paper is called an earlier proof merely because it now appears in a query. Current public registry heads and inaccessible historical intervals remain PARKED/UNCLEARED; denied GitHub, ScienceDirect and challenge routes were not retried. No exhaustive registry or citation sweep is claimed.

The mathematical question is resolved negatively by this polynomial, including the published statement. My strongest objection to campaign investment is the completely explicit coefficient-subtraction adaptation above. Recommend EXCLUDE from discovery credit on that substantive basis, while retaining the valid proof uncounted. If root rejects that substantive assessment, HOLD pending a targeted novelty review and subsequent independent formal gates; an open label is not evidence sufficient to INVEST or accept.

No shared files, git state, browser, public service data, MathDB, Lean or manuscript was changed. No acceptance or count authority is exercised.
