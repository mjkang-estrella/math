# Independent preliminary review: Richardson integrality

Decision: **HOLD for discovery acceptance. SOURCE PASS; MATH PASS; SUBSTANTIVE borderline, with no demonstrated exclusion; NOVELTY HOLD; FORMAL-FEASIBILITY plausible but unverified.** No Lean or manuscript investment is recommended at this stage. Root alone accepts, counts and stages. Administrative snapshot remains 9 additional / 39 total / next 40; this review grants no credit.

This is an independent review of the frozen `sol-hankel-full-prime-power-r2/PROOF.md` and `discovery.md`, the predecessor `sol-hankel-breadth-depth-r1`, and `root-hankel-prime-power-route-r1`. The proposed product, sum and carry mechanism originated with root, while Sol supplied the recurrence proof. That attribution supplies neither mathematical authority nor a presumption of novelty. No candidate checker was imported or reused.

## SOURCE — PASS, with bounded current-status limits

The actual Richardson journal body, *The Filbert Matrix*, Fibonacci Quarterly 39(3) (2001), 268–275, Definition 1.1 and Conjecture 5.1 on p272, was read from the frozen text, with the adjoining Theorems 5.1–5.3 and Section 6. A fresh lawful retrieval of https://www.fq.math.ca/Scanned/39-3/richardson.pdf at 2026-10-30T07:28:46.441688+00:00 returned exactly the inherited PDF SHA256 `09eebfb07b263e5dd20e935f114888e31433266f572966dbf0ede2afaf233d4e`. The journal explicitly retains the conjecture; that does not establish its status today. Its arXiv precursor math/9905079v1 was submitted 12 May 1999. The source's one-based Hankel index is b_(i+j-1), where b_k(r)=C(k+r-1,r); therefore the zero-based matrix is exactly

    R_ij = 1/C(i+j+r,r), 0 <= i,j < n, for ALL positive integers n,r.

The literal conjecture is integrality iff n=0 or 1 modulo every prime power dividing r. This equals r|n(n-1), since gcd(n,n-1)=1. Distinct maximal prime powers can choose distinct branches. The source's preliminary discussion r>3 does not restrict its subsequently stated positive-r conjecture. Theorem 5.2 already gives an explicit inverse, not a new result here. The separate Fibonomial conjecture in Section 6 is outside the reviewed claim.

Actual Berg Theorem 2.1 and its proof were read, not just the abstract: https://arxiv.org/pdf/math/0609283, PDF SHA256 `2813148b9e7d1c56a3971ef8a529a3921d0b27d80afa7f0b6a796740fc180b8c`. It identifies the coefficient matrix of the orthonormal reproducing kernel with the inverse moment Hankel matrix. Section 4's reciprocal alpha+i+j family is different from the present beta moments; its particular integrality assertion cannot be transplanted without the beta specialization below. Inherited metadata give v1 11 September 2006 and v2 5 August 2010; the cached PDF's 26 November 2024 footer remains an unresolved discrepancy. This review does not authenticate a new Berg journal version.

Actual Guo–Zeng Section 2 Eq.(2.1)–(2.3), Section 4 Lemma 4.2, Eq.(4.4), and the proof of Theorem 4.1 were read: https://arxiv.org/pdf/1101.0983, PDF SHA256 `f437468e19a45ca2c7e5d2f534f07e13f6fa519e58c5db1b7e65bc29b8a91d6e`. Fresh https://arxiv.org/abs/1101.0983 at 2026-10-30T07:28:50.473920+00:00 confirms v1 5 January 2011 and v2 1 April 2012, with body stamp matching v2. Its parameter r in Lemma 4.2 is a power, NOT the arbitrary Jacobi shift here. No separate typeset journal authentication for Guo–Zeng is claimed.

## MATH — PASS: complete independent bridge

All binomials below have nonnegative upper argument and are zero for lower argument outside [0,upper], except an explicitly separately defined zero endpoint T_0(0). We use exact rational arithmetic for matrices.

**1. Kernel and normalization.** For dmu=r(1-x)^(r-1)dx on [0,1], the s-th moment is r*s!*(r-1)!/(s+r)!=1/C(s+r,r). A nonzero polynomial has positive squared integral against this positive interior weight, so R is invertible. Define

    P_i(k)=C(k,i)C(k+r+i-1,i),
    Q_k(x)=sum_(i=0)^k (-1)^i P_i(k)x^i.

Leibniz applied to D^k[x^k(1-x)^(k+r-1)]/[k!(1-x)^(r-1)] gives the coefficient formula by Vandermonde. This proves normalization independently of Jacobi naming conventions. The first k-1 derivatives of the differentiated polynomial vanish at both endpoints for every r>=1 (including r=1); for k=0 no integration by parts is required. Consequently Q_k is orthogonal to every lower degree polynomial. Its leading coefficient is (-1)^k C(2k+r-1,k). Integrating against Q_k itself k times gives squared norm 1/(2k+r) for the unscaled weight and r/(2k+r) for mu. Thus C R C^T=D with C_ki=(-1)^i P_i(k), D_kk=r/(2k+r), and

    (R^-1)_ij=(-1)^(i+j)/r * sum_(k<n)(2k+r)P_i(k)P_j(k).       (K)

The diagonal of C never vanishes. This is the complete applicable specialization of Berg's classical kernel theorem; a citation alone is unnecessary. The corner equals n(n+r-1)/r, so integral inverse implies r|n(n-1). This is necessity, not corner-based sufficiency.

**2. Arbitrary-shift integral multiplication.** Put X=k(k+r) and B_h(X)=prod_(a<h)(X-a(a+r))/(h!)^2. Then B_h(k(k+r))=P_h(k) and

    X B_l=(l+1)^2 B_(l+1)+l(l+r)B_l.

For every i,j>=0, set A(i,j,l)=C(l,i)C(l,j)C(r+i+j-1,i+j-l), supported on max(i,j)<=l<=i+j, and zero elsewhere. The identity B_i B_j=sum_l A(i,j,l)B_l follows by induction on j, starting with B_0=1. Multiplication by X-j(j+r) reduces the step to

    (j+1)^2 A(i,j+1,l)
      =l^2 A(i,j,l-1)+(l(l+r)-j(j+r))A(i,j,l).                 (R)

In the old support, d=i+j+1-l>=1. For l>=j+1, divide by the positive A(i,j,l):

    A(i,j+1,l)/A(i,j,l)=(l-j)(r+i+j)/((j+1)d),
    l^2 A(i,j,l-1)/A(i,j,l)=(l-i)(l-j)(r+l-1)/d.

The second formula is still valid at l=i or l=j because the previous coefficient vanishes. After factoring l-j, (R) reduces to

    (l-i)(r+l-1)+(l+j+r)(i+j+1-l)=(j+1)(r+i+j).

At l=j>=i, the entire recurrence is zero. At the new top l=i+j+1 it is the factorial identity (j+1)^2 C(i+j+1,i)^2=(i+j+1)^2 C(i+j,i)^2. Below the support or above the new top, all terms vanish. These cases include i=0, j=0, and their common corner. There is no division by a zero coefficient at a support boundary. Evaluation at any integer k is legitimate, including l>k, where P_l(k)=0. This proves the full mixed-index shifted identity, with integral A, rather than inferring it from a square-only formula.

**3. Shifted weighted sum.** Define S_l(n)=sum_(k<n)(2k+r)P_l(k), and for n>=1 put

    T_l(n)=(n+r-1)C(n,l+1)C(n+r+l-1,l), T_l(0)=0.

For k>=l,

    T_l(k)=(k+r-1)(k-l)P_l(k)/(l+1),
    T_l(k+1)=(k+1)(k+r+l)P_l(k)/(l+1).

Their difference is (2k+r)P_l(k). At k<l all terms vanish, including k=l-1; the first nonzero increment is at k=l. Hence S_l(n)=T_l(n). At k=l=0,r=1 the two polynomial expressions give T_0(0)=0 and T_0(1)=1, so this endpoint does not use C(-1,0). For l>0 at n=0 the upper binomial argument r+l-1 is already nonnegative and C(0,l+1)=0. For l>=n the sum and formula vanish.

**4. Arbitrary prime powers.** Fix p^e|r, e>=1. If n=1 mod p^e, T_l(n) is divisible by p^e from its factor n+r-1. If n=0 mod p^e and l<n, put m=l+1, t=v_p(m), a=v_p(n)>=e, z=min(e,t). From m*C(n,m)=n*C(n-1,m-1),

    v_p C(n,m) >= max(0,a-t) >= max(0,e-t).

In C(n+r+m-2,m-1), the two complementary parts are m-1 and n+r-1. Both are -1 mod p^z. Their final z base-p digits are p-1. The first addition has 2p-2>=p; each next position has 2p-1>=p including its incoming carry. There are at least z carries. Legendre's factorial formula, equivalently its digit-sum identity, makes each carry contribute one to the valuation, so this binomial has valuation at least z. The total is at least max(0,e-t)+min(e,t)=e. If z=0 the carry assertion is empty, correctly. At m=1 the first binomial already supplies e; at m=n the same estimate works. No factorial is presumed a p-unit, no m<p^e restriction is made, and p=2 works verbatim. Cases l>=n are zero.

**5. Full sufficiency and endpoints.** Substituting step 2 into (K) expresses every numerator as sum_l A(i,j,l)S_l(n), an integer combination. Step 4 makes each summand divisible by every maximal prime power of r. Coprimality gives divisibility by r. The corner supplies the reverse implication. For r=1 there are no prime-power obligations and (K) is integral. For n=1 the matrix is [1] for every r; the formulas give N_00=r. In a mixed CRT case, for example r=72,n=9, n is 1 mod 8 and 0 mod 9; the proof works although n is neither 0 nor 1 mod 72. This resolves all positive n,r and all matrix indices. It does not prove the stronger exact common-denominator conjecture observed in the predecessor, or the Fibonomial analogue.

No mathematical error requiring a changed theorem was found. The candidate's one formal negative-top notation in the sum formula is adequately isolated by its separately specified endpoint; write T_l(0)=0 globally in any future formal statement to avoid a convention mismatch.

## SUBSTANTIVE — borderline; complete routine-adaptation objection exhibited

Guo–Zeng's ACTUAL unshifted basis is U_i(k)=C(k,i)C(k+i,i). Their Eq.(2.2) square expansion has coefficient C(2i,i)C(i,t)C(i+t,t) on U_(i+t), equal to C(i+t,i)^2 C(2i,i-t), exactly step 2 at shift 1 and i=j. Eq.(4.4) supplies their mixed-product mechanism, and their proof of Theorem 4.1 uses precisely

    sum_(k<n)(2k+1)U_l(k)=n C(n,l+1)C(n+l,l),

which is step 3 at shift 1. Their Lemma 4.2 inducts on powers using these expansions. Thus the product-linearize, telescope, divide strategy is already present in an actual prior body, not merely similar terminology.

The COMPLETE applicable classical adaptation is steps 1–5 above: beta moments -> normalized Jacobi kernel -> integer quadratic-Newton-basis multiplication with recurrence (R) -> shifted telescoping -> complementary valuations from a binomial identity and carries -> maximal-prime-power CRT -> corner necessity. This chain is universal and exhibits every missing bridge. It is a serious concrete argument that the result may be a routine adaptation under the campaign standard. It does not depend on proof length.

Nevertheless, neither Berg nor the read Guo–Zeng result itself states the all-shift multiplication formula or the reciprocal-binomial arithmetic criterion. Setting their parameter r equal to our shift is invalid, and setting the actual shift to 1 removes the denominator problem entirely. The arbitrary-shift integral coefficients and the precise two-factor valuation split must still be supplied. The latter is a useful arithmetic connection, particularly beyond squarefree r and for large indices. The predecessor's Lucas proof did not provide it.

My independent judgment: this is a sound and potentially substantive source-conjecture resolution, but its originality margin is narrow. I do NOT recommend categorical exclusion merely because a complete elementary adaptation can now be written down. The complete bridge establishes a credible routine objection, not a located published full-scope subsumer. At this preliminary gate, retain it uncredited on HOLD rather than claim either substantive PASS or a demonstrated classical exclusion. Root's authorship changes none of this assessment. If root applies a stricter notion of routine adaptation, the complete bridge above is the precise basis for that decision; no helper or shifted subcase deserves separate credit.

## NOVELTY — HOLD

No inspected primary body here contains the full criterion as a proved theorem. That is a limited observation, not historical clearance. A fresh bounded arXiv search at the exact URL in http.jsonl returns Richardson as the relevant hit; it is not a full-text, citation, or specialist-index sweep. The earlier lanes' current screen, history-screen.json and failures were read and retained. Their 1563 indexed-original history screen is bounded, misses unindexed/recent lanes, and is not independently rerun over all history here. Administrative accepted/excluded/held context was consulted: no Richardson acceptance or exclusion was identified in it; that snapshot is not an exhaustive campaign search. Root's route and this predecessor are one uncredited follow-up, not new independent discoveries.

Inherited GitHub API/raw/codeload/diff/patch, ScienceDirect, and Google challenge denials are binding; none was retried, proxied, bypassed, or accessed with TLS disabled. No current complete public proof-registry head/tree/body is authenticated. No new access denial occurred in this lane. No MathDB edit, browser session, external message, post or upload occurred. Subscription indexes and worldwide priority remain unchecked. Do not turn unavailable registry coverage into a clean search result. Do not reopen parked historical merge-tree or capped intervals without concrete new legitimate evidence; none was supplied here.

The next useful gate, if authorized by root, is narrow primary-source/citer work on arbitrary-shift Newton/Jacobi binomial products and reciprocal-binomial inverse arithmetic, respecting all existing denials. This is not permission for Lean or a manuscript now.

## FORMAL-FEASIBILITY — plausible, NOT certified

The finite-sum algebra and elementary divisibility proof are well suited to exact formalization. The main engineering costs would be either the beta/Rodrigues moment bridge or an alternative exact matrix inversion, polynomial recurrence support bookkeeping, and factorial valuation/carry lemmas. Merely proving numerator divisibility for an abstract kernel would leave the literal matrix endpoint unproved. A future certificate must quantify over all positive n,r, use the actual rational matrix, prove invertibility and the iff, and handle zero-support and n=1,r=1 endpoints explicitly. No Lean command, library audit, certificate or manuscript was produced in this task.

## Validation and custody

`independent_check.py` uses its own exact rational Gauss–Jordan inverse and direct moment inner products. It passed 18,634 recurrence controls, 9,317 product controls, 32,076 telescoping controls, 225 Jacobi inner-product/norm controls, 414 inverse-integrality iff cases, 13,110 exact inverse-entry comparisons, 1,074 prime-power sum controls, 525 valuation-split controls, and six mixed CRT hypotheses with 418 sum controls. These are finite error-detection tests, NOT the universal proof above. See check-results.json.

Assigned scientific inputs were selectively copied and byte-hash-checked before their scientific contents were read; no recursive historical tree was copied. Input-bindings identifies originals and frozen copies. Administrative NEXT/ledger/context are time snapshots only; live mutable administrative originals are not final scientific dependencies. Final original/copy verification applies to scientific inputs and rules, while administrative copies alone are hashed. Exact primary URLs, inherited retrieval metadata, fresh UTC/body hashes and version limitations are preserved in provenance.json, http.jsonl and the frozen metadata. The final manifest excludes itself and verification-receipt.json explicitly and is checked in a separate guarded invocation after final writes. Failures/deviations are retained in FAILURES.md.
