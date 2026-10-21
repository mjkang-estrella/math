# Prefreeze feasibility calculation — 337

Authorized Codex / GPT-6 Astra / high / default service tier. Both pinned main statements and all mathematical section includes were read before this calculation was developed. Source truth and operative proofs are stipulated. Initial penalty calculations preceded completion of the selected primary-proof reads; this chronology is not relabelled. No scope is frozen in this note.

The original T337E full exact-equality proof and scope have been read and remain unchanged. Q286's full uniform finite-volume asymmetry question and its actual obstruction calculations have been read; it remains unchanged. Neither is resubmitted. The possible additional operation is a quantitative *selected-current shell concentration* statement for all cycle dimensions n>=3 in arbitrary proper CAT(0) spaces. Its conclusion would concern a filling-close replacement cycle, with a radius fixed by the original mass, and a dimension-only explicit modulus. It would not be a quantitative flat-ball classification, a bound on the original cycle's support, or a replacement answer to Q286. No degree-one sharp filling is used.

## Selection and normalization

Write s=(n+1)omega_(n+1), c=1/((n+1)s^(1/n)), q=(n+1)/n. V denotes minimum integral filling mass. For nonzero compact T, normalize M(T)=s for the calculation and write V(T)=(1-delta)omega_(n+1). Choose lambda=sqrt(delta)>0 and H=1+lambda. In any compact convex ball Y containing T, minimize

    Phi(B)=c M(B)^q - V(B) + lambda V(B-T)

over integral n-cycles. Source compactness, filling continuity and the linear cone bound give attainment: c M^q-L M is coercive, and the negative filling term is continuous on mass-bounded sequences. Nonnegativity of c M^q-V gives

    V(A-T)<=omega_(n+1)lambda,
    1-lambda-lambda^2 <= (M(A)/s)^q <= 1+lambda.

For every cycle B, the triangle inequality for V and minimizing comparison give

    c(M(A)^q-M(B)^q) <= H V(A-B).

Scale the metric by H/R_A, R_A=(M(A)/s)^(1/n). In that metric m=M(A)=s H^n and the coefficient c/H obeys (c/H)q m^(1/n)=1/n. The entire source radial and small-set arguments therefore have their original normalized coefficients. The source's assumption m<s was used to produce a critical quotient below threshold, not for gradient closure, small-set comparison, compact embedding or the contradiction from an independently assumed subthreshold quotient. Consequently the sharp critical inequality still holds:

    4/(n-2) E(u)+n int u^2 >= n s^(2/n) ||u||_(2n/(n-2))^2.

A detailed applicability check is required in the author proof; no arbitrary near-extremizer is asserted to be the source's positive maximizer.

## Dimension-only localization

If A=C+D is a mass-additive nonzero cycle splitting with a=M(D)<=m/2, deleting D gives

    m^q-(m-a)^q <= H a^q.

But the left divided by a^q is at least 2^q-1. Thus lambda<2^q-2 excludes such splitting. A disconnected compact support has a separated compact partition, giving precisely this cycle splitting. Hence support is connected.

For a ball restriction U of mass a, fill its slice by R of mass d<=c_(n-1) P^(n/(n-1)). If d<=a/2 and a<=m/2, comparison with A-U+R gives

    2^(-1/n) a/(2n) <= c_n(3a/2)^q.

This forces a>=s(n+1)^n/(n^n 3^(n+1)). Therefore at smaller masses,

    a'(r)>=(a(r)/(2c_(n-1)))^((n-1)/n).

The monotone distribution may have a positive singular part; integrating the absolutely continuous lower derivative is still valid. At every support center this yields a(r)>=min(a0,b r^n), where

    a0=s(n+1)^n/(4 n^n 3^(n+1)),   b=omega_n/2^(n-1),
    r0=(a0/b)^(1/n).

Connectedness and disjoint r0-balls along distance levels then give a dimension-only diameter bound. With lambda_n=min(1/4,(2^q-2)/2), mbar=s(1+lambda_n)^n, one may use D_n=3r0(mbar/a0+1).

## Finite-parameter chord calculation

For a fixed center y in support, r=d(y,.)<=D_n, nu=mu/m, L=int r^2 dnu, J(a)=int(1+a r^2)^(-n)dnu, k=(n-2)/2, and G(a)=k int_0^1 J(au)u^(k-1)du. The source's completed radial estimate and actual smooth tests w(r)=(1+a r^2)^(-k) give the exact upper energy n m G(a). The critical lower bound gives

    H^(-2) J(a)^((n-2)/n) <= G(a).

This is the added finite-defect operation; setting H=1 without justification would erase the error. Set C=H^(2n/(n-2)), h=G^(-1/k). Then

    a h'(a)>=h(a)-C,    J(a)<=C h(a)^(-n/2).

The source zero-parameter integration cannot be copied, because C>1. Instead the scalar Taylor bound for (1+t)^(-n), followed by the tangent inequality for x^(-1/k), gives at every a0>0

    h(a0)>=1+2La0-gamma D_n^4 a0^2,
    gamma=n(n+1)/(n+2).

Integrate from a0 and optimize a0=sqrt((C-1)/gamma)/D_n^2. The positive asymptotic slope is at least 2L-2D_n^2 sqrt(gamma(C-1)). The *actual* tangent density lower coefficient s/(2^n m), combined with J<=C h^(-n/2), bounds that slope by 4C. Consequently

    L<=2C+D_n^2 sqrt(gamma(C-1)).

If the displayed slope is nonpositive, the same L bound is immediate. If lambda=0, let a0 tend to zero. No uniform tangent scale is presumed; the error has already been incorporated into the asymptotic slope before the tangent-density limit.

## Barycenter and every-point shell

CAT(0) variance at the barycenter o gives 2 int d(o,x)^2 dnu <= int L_y dnu(y). The radial test g=1 gives int d(o,x)dnu>=1. Therefore

    int (d(o,x)-1)^2 dnu <= eps_n(lambda),
    eps_n(lambda)=C-1+(D_n^2/2)sqrt(gamma(C-1)).

A support point with t=|d(o,x)-1| has a ball of radius min(t/2,r0) on which the squared integrand is at least t^2/4. The density bound upgrades this to

    t <= 2 max{(mbar eps/b)^(1/(n+2)),
               (mbar eps/(b r0^n))^(1/2)}.

This tends to zero at order lambda^(1/(2(n+2))), hence delta^(1/(4(n+2))). It gives containment in a metric annulus, not an isometric flat sphere or a filling interior point. All constants above are dimension-only and explicitly expressed through Euclidean unit-ball volumes.

## Comparison and remaining decision

Boegelein–Duzaar–Fusco's actual 2015 proof already pays penalty selection, filling-distance continuity, density localization, and Euclidean graphical stability; those are credited. The proposed extra operation is the quantitative critical-transform integration with C>1, combined with metric density/connectedness to remove the original diameter from the bound. It uses the pinned all-dimensional CAT(0) sharp theorem essentially. No worldwide priority or contribution grade is assigned.

Before freeze, finish primary comparison and independently recheck the displayed constants, the application of the source subthreshold contradiction, and all scaling. The n=2 endpoint does not follow from this critical transform and is not included in the possible new scope. An all-dimensional flat-ball stability result remains unpaid and will not be claimed.

## Decision before extended author proof

The BDF 2015 penalization, bounded-support reduction, graphical regularity application and main theorem proof have now been read; Wenger's main filling-continuity proof and Propositions 5.8–5.9 have been read; Stadler's actual density-one rigidity proof has been completed. Their deeper imported regularity and decomposition antecedents are not claimed fully read. The source radial derivation uses the normalized comparison coefficient, not its original sign relative to c_n; the only strict m<s_n use in the minimizer proof is its constant test that supplies Lambda<S_*. Substituting an assumed subthreshold quotient permits exactly the same minimizer/chord/variance contradiction. The source proofs are stipulated operations, not audited here.

The scalar constants have been rederived: the density contradiction threshold is s(n+1)^n/(n^n 3^(n+1)); integrating a'>=(a/(2c_(n-1)))^((n-1)/n) gives b=omega_n/2^(n-1); the Taylor coefficient after the h transform is gamma=n(n+1)/(n+2); the tangent coefficient gives slope at most 4 C^(2/n)H^2=4C. All scales in the comparison are degree n+1, so its coefficient is unchanged by metric dilation and rho=R_A/H is the required normalization.

These checks support freezing the selected-current shell theorem below. This is an author feasibility decision, not an independent correctness or contribution gate. No quantitative flat-ball conclusion, degree-two endpoint, original-support bound, or Q286 replacement is inferred. The explicit modulus may be very large except at very small deficit; its stated limit, not numerical usefulness at the endpoint, is the assertion.
