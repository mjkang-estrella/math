# Independent correctness review, T088P133, recovery round 3

Verdict: **PASS_FULL_T088P133** for the entire unchanged frozen theorem. No blocking mathematical gap or necessary same-scope mathematical repair was found. This is a correctness assessment, with no contribution, acceptance, campaign-count, publication, or formalization verdict.

Reviewer runner: Codex / GPT-6.1-Sol / high reasoning / default service tier. Exclusive writable root: `frontier/campaigns/2026-10-14/t088p133-proof-r3/`. No nested agent, git operation, browser UI, author edit, old-review edit, upload, submission, or contact was performed.

## Exact object of the verdict

For **every** convex polytope K in R^4 with nonempty interior and **at most six actual facets**, with h_(Pi K)(u)=V_3(K|u-perp) for unit u,

    V_4(Pi K) <= (160/3) V_4(K)^3,

with equality **if and only if K is a simplex**. Every exactly-six-facet case is strict, including nonsimple polytopes, repeated Gale knots, zero intermediate coefficients, and boundary sign patterns. The proof audited is the original author's `packet/public/proof.md`, SHA256 `971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84`; the frozen scope SHA256 is `86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354`. No narrower replacement theorem was used.

All claims in the pinned OpenAI revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including their operative proof operations, are stipulated true. Their truth was not audited. The proof in fact rederives the needed reduction and uses no new unproved assertion from a previous discovery or contribution review. Classical inputs are justified or checked with their usable hypotheses below.

## Recovery evidence and independence

Round 1 ended with provider/network failure, no mathematical verdict. Round 2 ended at a 402 five-hour Droid Core limit, with partial checks but no FINAL, REPORT, review.md, or complete analytic/geometric audit. The failure records, both full prior briefs, current full brief, snapshots, and complete listed round-2 code, notes and outputs were read. The old snapshots independently reproduce **5** and **20** files, respectively, including the accidental round-2 pycache, unchanged. Authentication is not a correctness proof.

Round 2 initially omitted V in M=(n+1) NPtilde V Den-D Nptilde^2, then corrected its own implementation before the saved output. It also replaced repeated-knot samples by distinct nearby samples after a denominator failure. Neither action was an author repair or a proof of continuity. The saved corrected M is correct; the earlier omitted-V expression would be incorrect for nonconstant V. Comments referring to an undelivered review.md supply no evidence. All continuity and strictness arguments are evaluated below independently.

The contribution review root, parent contribution disposition and adoption were not opened. The required shared acceptance ledger contained an incidental contribution-status sentence; this was not followed or used as mathematical evidence. No independent verdict can be based on that sentence. Active unrelated roots and all older excluded roots were not entered. A first repository filename search listed AGENTS paths broadly; no excluded-root contents were opened.

## 1. Classical hypotheses, factors, and facet-section maximum

Here K is compact, full-dimensional, with its **actual** irredundant facets, areas f_i>0 and distinct outer unit normals u_i. Translate an interior point to 0, so all h_i>0. No simplicity or generic position is assumed.

**F1.** For every constant vector v, the divergence theorem gives sum_i f_i<u_i,v>=0; hence sum w_i=0 for w_i=f_i u_i. If their span were proper, a nonzero vector orthogonal to every facet normal would be a lineality direction of the intersection of the facet halfspaces, contradicting compactness. Thus W has row rank n. Applying the divergence theorem to x/n also gives sum f_i h_i=nV(K), in this normalization.

**F2.** For almost every line parallel to a unit u over the projection, its two endpoints lie in facet interiors. Projection from a facet has Jacobian |<u_i,u>|. Counting the entry and exit gives half the sum of projected facet areas. The exceptions are projections of lower-dimensional faces and facets parallel to u and are null. Thus the segments are exactly [-w_i/2,w_i/2]. The same argument is explicitly proved in pinned Source P, Lemma `lem:facets`, read in full. The projection body here is the unpolarized one.

**F3.** Translating each centered segment gives [0,w_i], of **length |w_i|**, with no additional 2^n. For completeness, adding [0,v] to a compact convex set extends each nonempty fiber parallel to v by |v|. Fubini yields the extrusion formula

    V_n(Z+[0,v])=V_n(Z)+|v| V_(n-1)(Z|v-perp).

For a lower-dimensional Z this formula is still valid by the same fiber argument. Induction on the number of generators and dimension, using |v| times each projected determinant as the absolute determinant with v adjoined, gives sum over all n-subsets |det W_J|. Each unordered subset occurs once. Dependent subsets contribute zero. This proves the determinant formula needed here.

**F4 and F6.** The only mixed-volume inequality needed is

    (1/n) sum_i f_i h_L(u_i) >= V(K)^((n-1)/n) V(L)^(1/n)

for two compact convex bodies with nonempty interiors; L need not contain 0. Here is a justification, including its classical analytic foundation. Prékopa's integral inequality (1973, Theorem 3) applied to indicators of convex sets gives the multiplicative Brunn-Minkowski inequality. To get its power form, put a=V(A)^(1/n), b=V(B)^(1/n), apply the multiplicative inequality to the equal-volume sets A/a and B/b at weight b/(a+b), and scale by a+b. This gives V(A+B)^(1/n)>=a+b, and homogeneity gives all nonnegative weights.

For a fixed full-dimensional polytope K and a compact convex L, the first variation is

    d/dt V(K+tL)|_(t=0+) = sum_i f_i h_L(u_i).

One can first translate L to contain 0: the swept first-order layers over facet interiors have normal thickness t h_L(u_i); neighborhoods of the finitely many ridges contribute O(t^2), since L is bounded. This proves the formula; translating L back changes the sum by <sum f_i u_i,v>=0. Differentiating V(K+tL)^(1/n)>=V(K)^(1/n)+tV(L)^(1/n) proves the stated inequality and identifies the usual mixed volume as the derivative divided by n. No equality classification from Minkowski is needed: the maximizing body below is exhibited directly.

For Brunn's section principle, identify all parallel n-dimensional sections of a convex body of dimension n+1 by translation into the same n-space. Convex combinations of two sections are contained in the intermediate section. The power Brunn-Minkowski inequality in that n-space gives concavity of the nth root of section volume. It applies to Δ of dimension m-1=n+1 and the nonconstant functional a. Its sections have positive n-volume for every t between the extreme knots: such a t has a barycentric representative with all coordinates positive. Finite concave functions are continuous on the open interval. The volumes are bounded, also directly because every section is contained in a fixed ball. These observations justify F6 without any regularity of the knots.

**Lemma 1.** For every lambda with sum lambda_i=1, the affine injection x -> lambda-W^T x maps L_lambda exactly onto (lambda+R) intersect Δ. Its n-Jacobian is sqrt(det WW^T)>0. In particular its preimage of the compact simplex section is compact when nonempty. Empty or lower-dimensional sections have n-volume zero. If L_lambda has interior, its true supports satisfy h_(L_lambda)(u_i)<=lambda_i/f_i, even when individual trial numbers lambda_i are negative. F4 therefore bounds its mixed volume above by 1/n and below by the volume expression, proving

    n^n V(L_lambda) <= V(K)^(1-n).

Mixed volume is translation invariant, so negative trial supports cause no hypothesis failure or change of sign in this argument. The exhibited lambda*_i=f_i h_i/(nV(K)) sums to one, is strictly positive, and makes L_lambda*=K/(nV(K)). Its volume attains the bound exactly. Thus this is a genuine maximum over the whole affine hyperplane, not just a supremum or a lower-bound transfer.

## 2. Gale determinants, coarea, Gamma constants, and attainment

For m=n+2, rank W=n and sum w_i=0 imply ker W is two-dimensional and contains 1. Subtracting the mean from an independent vector produces a nonzero a perpendicular to 1. Hence R={1,a}-perp. All this remains true for nonsimple polytopes and repeated coordinates of a.

**F8 and Lemma 2.** Write W=MU with orthonormal rows U. Then WW^T=MM^T and sqrt(det WW^T)=|det M|. Complete U by the two orthonormal rows 1/sqrt m and a/|a|. Jacobi's minor formula follows, for example, by writing minors of Q^-1 via complementary cofactors and using Q^-1=Q^T and |det Q|=1. Consequently each n-minor of U has absolute value |a_i-a_j|/(sqrt m |a|), where {i,j} is its complement. Summing gives precisely D(a)/(sqrt m |a|). Repeated knots simply make the corresponding summands zero; no inverse difference is used.

**F7.** The simplex Δ=conv(e_1,...,e_m) has intrinsic volume sqrt m/(m-1)!: its edge Gram matrix is I+11^T, of determinant m. In affine coordinates s_1,...,s_(m-1), s_m=1-sum s_i, the substitution E_i=r s_i has absolute Jacobian r^(m-1). The joint exponential density becomes e^-r r^(m-1), independent of s. Normalizing proves S~Gamma(m), s uniform on Δ, and independence. Direct integration gives E[1/S]=Gamma(m-1)/Gamma(m)=1/(m-1).

The gradient of <a,s> in the affine hull H is exactly a, because a perpendicular 1. Resolving Lebesgue measure in an orthonormal coordinate along a gives the linear coarea formula

    phi_X(t)=sigma(t)/(|a| H^(m-1)(Δ)),   X=<a,s>.

The continuous interior version is legitimate by the section argument above. Values assigned at the two endpoints do not affect this density, even if an endpoint section has positive n-volume.

For every t in I=(min a,max a), two opposite nonzero coefficients can be selected in Y_t. Their sum has bounded continuous asymmetric-Laplace density g; convolution with any independent remaining sum therefore has a bounded continuous density. Zero coefficients and repeated coefficients in the remainder do not matter.

Independently, Y_t=S(X-t) gives a density at y by integrating phi_X(t+y/r)/r against the Gamma(m) density. Boundedness of phi_X and integrability of gamma_m(r)/r give dominated convergence at y=0. Both this version and the convolution version are continuous there and agree almost everywhere, so their values at zero agree. Thus

    f_(Y_t)(0)=phi_X(t)/(m-1),
    sigma(t)=sqrt m |a| f_(Y_t)(0)/(m-2)!.

This verifies the factorial and the direction of the Gamma factor independently; using m-1 instead of its reciprocal in the first line would be wrong.

For lambda in H, its section depends exactly on t=<a,lambda>. Every real t is attained by such a lambda. Lemma 1 supplies a global maximum at lambda*, and its strictly positive barycentric weights ensure t* strictly between the minimum and maximum of a. Consequently the same maximum is attained in **open** I, regardless of whether boundary sections vanish. Multiplying Lemmas 1-3 yields

    P_n(K)=n^n D(a) f_(Y_t*)(0)/n!,
    P_n(K)/c_n=max_(t in I) D(a) f_(Y_t)(0)/(n+1).

This is the author's Proposition A, including attainment and all constants. In particular n=4 gives c_4=5*4^4/4!=160/3.

The actual [FHLX v1](https://arxiv.org/abs/2610.13953v1) TeX Section 4, propositions labelled `prop:transfer` and `prop:codim-one-product`, has the credited one-sided transfer and compatible simplex/cube normalization. It does not by itself supply this exact maximum for every K; Lemma 1 pays that obligation. FHLX's higher-dimensional perturbation/lifting is outside this theorem. No mathematical inference here uses its counterexamples to infer a four-dimensional upper bound.

## 3. Normal form and the genuine-facet exclusion

Fix t in I, select one actual maximum and one actual minimum coordinate, and set mu=2/(max a-min a)>0, alpha=mu(t-min a), beta=mu(max a-t). Both are positive, sum to two, and all n remaining coefficients b lie in [-alpha,beta]. This is available even if extrema have multiplicity. Centering the **coefficients** a_i-t preserves all pairwise distances; positive scaling multiplies D by mu and divides the continuous density at zero by mu.

For U=beta E'-alpha E'', direct convolution gives

    g(u)=exp(-u/beta)/(alpha+beta) for u>=0,
    g(u)=exp(u/alpha)/(alpha+beta) for u<=0.

The two expressions meet at zero. Therefore g(-W_b) uses alpha on W_b^+ and beta on W_b^-, exactly as in the proof. The two outer knots contribute 2 to D; each remaining knot contributes |beta-b_j|+|b_j+alpha|=2. Thus total distance is 2(n+1)+D(b), and the resulting factor is 1+D(b)/(2(n+1)). There is no lost 1/2 or reversed Laplace parameter.

If b=0, v=a-t1 belongs to ker W, is supported just on the two selected extreme indices, and has coefficients with opposite signs. Then v_+ w_+ + v_- w_-=0 implies w_+ is a **positive** multiple of w_-. Their positive areas force the same outer unit normal. A full-dimensional polytope has only one exposed facet at a specified normal, so these cannot be distinct actual facets. This excludes b=0 for every t in I for a genuine n+2-facet polytope. No simple-polytope assumption enters this argument. Repeated extreme knots cannot invalidate it: an unselected nonzero extreme would itself already make b nonzero.

## 4. Log-concavity, conditional laws, and the Laplace bound

Each nonzero signed exponential summand has a log-concave density on its supporting half-line, extended by zero. Zero summands are omitted; b!=0 leaves at least one genuine absolutely continuous summand. Convolution preserves log-concavity. The needed marginal/convolution statements and their proofs were read in [Prékopa 1973, Theorems 6-8](https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf), printed pp.342-343. In particular apply marginalization to f(x-y)g(y). To obtain a survival function, apply it to f(x+r) times the indicator r>=0 and integrate over r. These inputs are nonnegative measurable log-concave functions with finite required marginals; convex half-line supports are allowed. Smooth or strictly log-concave densities are not required.

The support of W_b is (0,infinity) up to endpoints if all nonzero b_j>0, the negative counterpart if all are negative, and all R when both signs occur. The last assertion follows by taking positive summands sufficiently large and negative ones small, or conversely; the underlying exponentials have positive density on every positive open interval. Thus p=1, p=0, or 0<p<1 exactly in those three respective cases. There is no atom at zero for any nonzero b. The density is continuous at interior support points by log-concavity, and in the mixed case by convolution of an opposite-sign pair as well. A one-summand density may jump at its support endpoint; nothing requires continuity there.

Restriction to W>0 and reflection/restriction to W<0 preserve log-concavity. When their conditioning probabilities are nonzero, these laws have support (0,infinity), no atom at zero, finite strictly positive means. Finiteness follows from E|W_b|<=sum|b_j|. The one-sided cases can use W_b itself, or its reflection, with the same properties.

For Lemma 6, write H(x)=P(X>x), G(x)=integral_x^infinity H. The densities in use give H(0)=1, G(0)=mu>0, continuous H, and G'=-H. Concavity of log H makes H(x+r)/H(x) nonincreasing in x wherever H>0. Therefore

    G(x)/H(x)<=integral_0^infinity H(r)dr=mu.

If H vanishes, its tail integral vanishes too. Hence G'<=-G/mu and G(x)<=mu exp(-x/mu). This also covers an eventual finite support endpoint. On [0,R], integration by parts gives

    integral_0^R e^(-sx) H(x)dx
       = mu-e^(-sR)G(R)-s integral_0^R e^(-sx)G(x)dx.

G(R)->0, and the established exponential bound makes the remaining integral finite for s>=0. Letting R tend to infinity gives a lower bound mu/(1+s mu) for the integral of the survival function. Independently Fubini applied to 1-e^(-sX)=integral_0^X s e^(-sx)dx gives

    E e^(-sX)=1-s integral_0^infinity e^(-sx)H(x)dx <=1/(1+s mu).

At s=0 equality is immediate; the same integration has no residual boundary term. The inequality directions in the author proof are correct. No convex-order or reliability-name assertion is needed beyond this actual derivation.

## 5. Universal two-bracket algebra and strictness

Set d=D(b)/(2(n+1))>=0. If p=1, then P>0, 2d<=P, and alpha<2 implies d<=P/2<P/alpha. The Laplace comparison yields Psi<1. If p=0, use N>0 and beta<2 symmetrically. These arguments include D=0; no division by d occurs.

In the mixed case let A=P/p>0, B=N/(1-p)>0. All divisions are justified, including alpha,beta>0. Conditional Laplace comparison gives Psi at most

    (1+d)[p alpha/(alpha+A)+(1-p) beta/(beta+B)].

I independently expanded the numerator of its slack as

    (alpha+A)(beta+B) - (1+d)[p alpha(beta+B)+(1-p) beta(alpha+A)]
     = p A beta+(1-p) B alpha-d alpha beta
       +AB-d[p alpha B+(1-p) beta A].

After division by alpha beta and substitutions P=pA,N=(1-p)B, this is exactly the author's two-bracket formula. `crosscheck.py` additionally verifies it as a zero polynomial in **six independent formal variables**, not just numerical samples.

From 2d p^2<=P and 2d(1-p)^2<=N, the second bracket is nonnegative. Strict (S)(b) makes its first contribution d p^2 alpha/P<alpha/2; this conclusion also holds when d=0, since P>0. Thus the second bracket is strictly positive. For the first bracket, adding sqrt(2d)p<=sqrt P and sqrt(2d)(1-p)<=sqrt N and applying weighted Cauchy-Schwarz gives

    2d <= (sqrt P+sqrt N)^2 <=2(P/alpha+N/beta).

Both brackets have the asserted signs and the positive multiplier AB/(alpha beta) makes the total slack strictly positive. Hence Psi<1 for every permitted nonzero b, with no box constraint required at this step. Under scaling b->lambda b, P,N,d,A,B scale by lambda and p does not; the cleared slack divided by lambda is affine in lambda as described. That remark is not an extra assumption in the proof.

## 6. Partial fractions, independent finite witness, repeated knots and zeros

### Original partial-fraction and quotient operations

For distinct nonzero c_j, the transform of |c_j|^-1 exp(-x/c_j) on the half-line x c_j>0 is 1/(1+s c_j), including when c_j<0. The common open strip around zero is given by |Re s|<min_j 1/|c_j|. Multiplying by (1+s c_j) at the pole s=-1/c_j yields A_j=product_(i!=j) c_j/(c_j-c_i). The rational partial fractions sum to product_j(1+s c_j)^-1; the difference has no poles and vanishes at infinity. All signed exponential terms define finite signed measures with exponential moments on a smaller strip. Analytic continuation and Fourier uniqueness therefore identify their sum with the probability law. Integrating the positive-side terms gives p=sum_(c_j>0) A_j and P=sum_(c_j>0) A_j c_j. Negative coefficients A_j cause no problem: only the final sum must be a probability density.

Zero c_j are omitted rather than counted as distinct poles. For k positive u_i and l negative -v_j this gives the exponent k-1+l in the numerator for p, and k+l for P. The author's sign in the Vandermonde identity is correct: moving u_i from its ordered position past its i-1 predecessors gives (-1)^(i-1). Multiplying each positive term by Den and V gives exactly the displayed alternating sums. Alternating polynomials in the u_i vanish at every u_a=u_b; the distinct linear differences are relatively prime, so their product divides the numerator in Q[u,v]. Substitution by ordered gaps preserves the resulting polynomial identity. The author's exact division algorithm performs leading-term cancellation in lexicographic order with rational arithmetic, fails if cancellation is impossible, and terminates as leading monomials decrease. It succeeds on all ten patterns.

Den=product_(i,j)(u_i+v_j) is strictly positive whenever k>=1,l>=1 and all surviving u_i,v_j>0, including repeated positive or negative knots. If l=0 it is the empty product 1. The rank formula for sorted D is sum_i(2i-5)s_i for n=4; equivalently, and as used in my separate code, it is the direct sum of the nonnegative ordered differences s_j-s_i. Zeros contribute to those distances even though they do not contribute exponential summands.

### Independent reconstruction, not a rerun as the proof

The full expanded rational-coefficient witness is `certificate-witness.json`, generated by `independent_certificate.py`. Its derivation uses a **different probabilistic recurrence**, with no author or round-2 import, no interpolation, partial fractions, or polynomial division.

Let U_i=sum_(a>=i) u_a E_a and V_j=sum_(b>=j) v_b E'_b. Think of each as the completion time of successive independent exponential phases. The first U phase wins against the first V phase with probability v_j/(u_i+v_j), and the V phase wins with probability u_i/(u_i+v_j). The exponential memoryless property leaves the unfinished phase independent with its original mean. The time elapsed in that race subtracts equally from both completion times, so their difference is the difference of the remaining times. Therefore both q_ij=P(U_i>V_j) and R_ij=E(U_i-V_j)^+ obey the same two-branch recurrence. At i=k both are zero; at j=l they are 1 and sum_(a>=i)u_a respectively. The state (k,l) is unreachable from a live race and is immaterial; the implementation's i=k boundary takes precedence.

Clear the rectangular denominator Den_ij=product_(a>=i,b>=j)(u_a+v_b). If N denotes either numerator, the recurrence becomes the polynomial identity

    N_ij = v_j product_(b>j)(u_i+v_b) N_(i+1,j)
           +u_i product_(a>i)(u_a+v_j) N_(i,j+1).

Every coefficient and operation here is integer-exact. The boundary values have denominator 1. This proves that q_00=Np/Den and R_00=NP/Den **also for repeated rates directly**, because every racing denominator is positive. Applying the recurrence to ordered gaps and computing T=5 NP Den-D Np^2 yields:

    (k,l,z)  terms(T)  degree(T)  minimum nonzero coefficient
    (1,0,3)      1        1                  2
    (1,1,2)      2        3                  2
    (1,2,1)      5        5                  2
    (1,3,0)     14        7                  2
    (2,0,2)      2        1                  2
    (2,1,1)     15        5                  2
    (2,2,0)    118        9                  2
    (3,0,1)      3        1                  2
    (3,1,0)     84        7                  2
    (4,0,0)      4        1                  2

Every stored coefficient is positive; omitted coefficients are zero. The entire witness is stored, not only these summary counts. Moreover each T contains a pure endpoint-positive monomial `c*x_k^(2kl+1)`: c=2 for k=1, c=6 for k=2, c=12 for k=3, c=20 for k=4 (only the admissible l for that k occur). This is positive because x_k>0. Thus it survives **every** zero interior gap, irrespective of the y gaps. Other endpoint monomials are recorded as well. This verifies strictness over every stratum with a positive coefficient, stronger than the mixed-stratum strictness needed in Proposition B. No strict inequality is inferred merely by continuity from the interior.

The independent generated Np,NP,Den,D,T were then compared coefficient-for-coefficient with all five author polynomials in each pattern, using copies inside this review root. All match. They also satisfy the corrected round-2 identity T V^2=M exactly for all ten patterns. This supplies a new independently derived witness for the original certificate operation; it changes no author proof or theorem.

### Continuity and complete coverage

For a sequence b^(r)->b!=0, couple all W using the same exponentials. W_(b^(r))->W_b almost surely. Since P(W_b=0)=0, the sign indicators converge almost surely; dominated convergence gives continuity of p. In a bounded coefficient neighborhood, |W_(b^(r))|<=C sum E_i, an integrable bound, giving continuity of P as well. D is continuous. Thus the author's rational identities extend from strictly ordered gaps to repeated same-sign knots whenever the surviving endpoint variables are positive, since Den remains positive. Zero coordinates belong to the separate z-patterns already enumerated. If a positive or negative endpoint tends to zero, reclassify the limiting nonzero vector into its actual sign pattern; continuity still holds and its **own** endpoint witness gives strictness when mixed. At b=0, p is defined as P(0>0)=0 and P=D=0; (S) holds directly without a continuity or density assertion there.

For no positive coordinates p=P=0. For only nonnegative coordinates with at least one positive, p=1 and P=sum b_i; the four l=0 patterns prove the inequality, also directly implied by D<=3 sum b_i<5 sum b_i. Pure negative vectors have p=P=0 and their mirrors are covered. Both-sign vectors have exactly 0<p<1. Hence these ten patterns, the no-positive cases and the zero vector exhaust **all R^4**. Applied to b and -b they pay both hypotheses of Proposition B. Repeated Gale extrema, zero middle knots, and nonsimple geometry have all been retained.

### Assessment of round-2 computation

Its tensor Newton interpolation samples strictly positive ordered gaps and computes exact fractions. The reported coordinate degree bound deg_i M is a safe search bound for a polynomial quotient if it exists: deg_i M=deg_i T+2 deg_i V in the polynomial domain. The grid has deg_i M+1 distinct nodes, enough for the interpolation class (the comment saying 'exceeds' the degree is harmless wording). Interpolation of a rational function alone would not prove polynomiality. Crucially the saved checker **then multiplies symbolically** and requires T V^2-M to be the zero coefficient dictionary. That establishes the identity on V!=0 regardless of interpolation heuristics. Its coefficient and endpoint scans are exact; with all stored coefficients positive its endpoint existence test is sound. I did not rerun the heavy interpolation or its n=5 interpolation control; I independently reproduced its final symbolic condition using the recurrence witness. Its spot samples were read and supply diagnostics only. The fresh universal identity and continuity proof above replace no missing premise with a sample.

## 7. Final geometry and equality

A full-dimensional n-polytope has at least n+1 facets: after translation to contain 0 in its interior, its polar is full-dimensional and has one vertex per actual facet, and a full-dimensional polytope needs at least n+1 vertices. If there are exactly n+1 vertices they are affinely independent and their convex hull is a simplex; its polar is a simplex too. Thus in dimension 4 the only possibilities under the frozen facet bound are five-facet simplices and exactly-six-facet polytopes. The elementary polar correspondence here follows directly from the irredundant facet inequalities and the convex hull of their normalized normals.

The standard simplex has volume 1/n!, facet area vectors -e_i/(n-1)! and (sum e_i)/(n-1)!. All its n+1 full-size minors have absolute value 1/((n-1)!)^n, so the projection-body volume is (n+1)/((n-1)!)^n. Dividing by (1/n!)^(n-1) gives c_n exactly. Under an invertible A, each facet area vector transforms by |det A| A^-T; this map has determinant of absolute value |det A|^(n-1). Thus the ratio is affine invariant and every simplex attains c_4=160/3. This also agrees with Source P `prop:simplex`; the float simplex control is not the justification.

For an exactly-six-facet K, Proposition A yields its ratio at the attained t* in I. The normal form gives alpha,beta in (0,2) and four intermediate coefficients b. Lemma 4' ensures b!=0. Proposition C supplies (S)(b),(S)(-b), strict in the mixed case; Proposition B therefore gives Psi(alpha,b)<1. Hence P_4(K)<160/3. An attained maximum is essential: pointwise strictness alone would not exclude a supremum equal to one. The proof has the required attainment. Combining the two facet cases proves the stated equality **if and only if**, without assuming K is simple, smooth, simplicial, or generic.

## Presentation-only observations and scope limits

1. The phrase that a negative-coefficient control 'rejects (S)_5' should say it rejects **this nonnegative-coefficient certificate**. A negative coefficient alone is not an inequality counterexample. The author's separate corner asymptotic is valid: with r=n-1, Z~Exp(1), A~Gamma(r), and W=epsilon A-Z,

       p=1-(1+epsilon)^(-r),
       P=r epsilon-1+(1+epsilon)^(-r),
       D=r(1+epsilon).

   Expanding these exact functions gives the stated limiting ratio 2(n-1)^2/(n(n+1))>1 for n>=5. An independent concrete n=5 epsilon=1/100 calculation is recorded; its ratio is `5495618760267/5255309886352>1`. This checks the auxiliary side claim independently of the coefficient control. It says nothing adverse about the frozen four-dimensional theorem or the geometric inequality in dimensions 5-8.
2. In Lemma 4, centering should be phrased as replacing the coefficient vector a-t1 by itself under reparametrization, rather than suggesting that a can be replaced by a-t1 while holding the original Y_t definition's t fixed. The subsequent displayed computation unambiguously uses mu(a-t1), which is correct.
3. Clarify the empty negative list in Proposition C: y_l>0 applies only when l>0. The implemented empty products and l=0 cases are correct. Similarly, no density or continuity at the all-zero b is needed.
4. The original proof sketch and exact auxiliary certificate existed **before** the disclosed 17:21:32Z freeze. The proof does not claim that its ideas first arose afterward. Author FINAL records a sealing time 17:31:58Z, whereas notes describe later 17:36-17:45Z drafting/packaging. Those timestamp statements are internally inconsistent as a detailed chronology; immutable bytes and mathematical correctness do not establish which timestamp is accurate. Preserve and explain this process metadata rather than infer a cleaner chronology. The disclosed late Petty/acceptance reads and temporary /tmp hit-list deviation remain disclosed; no original was rewritten here.
5. No optimality of the auxiliary constant 5 is certified. No all-dimensional positive threshold theorem, generic-body solution, full Brannen solution, worldwide priority, or contribution conclusion is included. No claim about dimensions 5-8 or >=7 facets is added. A future presentation can add classical references and expose the full coefficient witness for convenience; neither is a missing mathematical premise in this review.

There are **no blocking mathematical obligations left open at the frozen scope**, and no minimal mathematical repair is required. The observations above do not condition the correctness verdict on author edits. The recurrence reconstruction is independent verification of the existing certificate, not a replacement theorem or an author repair.

## Actual reading, authentication, tests, and limits

- AGENTS.md, all three complete role briefs, complete common brief, upstream.json and CONTENTS entry088 were read. Acceptance rules at the beginning of NEW-TEN were read as instructed; this live ledger is not a frozen mathematical input and was not searched for a contribution conclusion.
- Author scope/proof/certificate.py/geometry_control.py/reading-limits.md/report.md, work/notes.md, FINAL and manifest were read in full. All five supplied detached anchors, all 24 manifest payloads and 14 directories authenticate. The entire author root was snapshotted, including scratch; not every scratch script was semantically read or used. No old bytes, modes, directory layout or link counts were intentionally changed.
- The complete listed round-2 progress/checkers/outputs/start and measured hash lists were read. Copies of its checker and the author scripts were used only inside this root with Python -B. Copied author exact certificate and 40-polytope float control were rerun and pass; the independent recurrence and coefficient comparison are the finite proof checks. No numerical geometry or Monte Carlo result is used as a full-scope proof.
- Source P README, main.tex and references.tex were read in full from the preserved round-2 bodies and authenticated by fresh pinned-URL downloads. Its facet, affine and simplex operations are exact usable interfaces, stipulated true; no upstream truth review was undertaken.
- Eight Source P/Petty bodies were fetched afresh from pinned raw GitHub URLs, authenticated against the SHA256-bound complete 13223-entry, nontruncated tree by Git blob SHA1 and length. Petty README/main and introduction lines1-100 were read; its fetched conclusion/consequences and internal proof sections were not read for a dependency. It supplies no operative premise of this upper-bound theorem, so there is no need to audit its lower-bound proof.
- FHLX eprint and PDF were independently fetched from arXiv versioned URLs and match the preserved round-2 bytes. The TeX body read is introduction/preliminaries lines157-374 and **all Section4 lines991-1602**, covering the actual statements and complete relevant proofs, including perturbation and lifting. Section3's unrelated dimension-three proof was not read. The PDF was byte-authenticated, not visually or body-read; TeX, rather than PDF metadata, is the body evidence. The primary webpage metadata and abstract were also inspected. No conclusion rests just on that abstract.
- Prékopa 1973 actual PDF text was read, especially Theorem3 with its induction and Theorems6-8 with proofs; it was downloaded privately. The required F5 hypotheses and the classical Brunn-Minkowski foundation used above are explicit. Original Minkowski/Brunn/Jacobi/Shephard/Dirichlet historical papers were not acquired: the relevant operations were justified directly above. No broad literature or contribution search was conducted.
- Primary/private source/history bodies remain under original rights in packet/private. Public original review prose is CC BY4.0; new original review code is MIT. Copied author code retains its own MIT notices. No redistribution or publication was performed.
- Stable used-original bindings were recorded before substantive review and rechecked afterward, including the full author/r1/r2 directory trees. Parent late dispatch or commit-validation files are outside the stable-input set and, if observed, recorded separately without changing that set. The verifier accepts explicit external FINAL/MANIFEST/outsideREPORT SHA256 anchors and optionally checks the actual originals against their recorded complete layouts. Copied tamper controls are artifact tests only. They neither prove mathematics nor confer acceptance.
