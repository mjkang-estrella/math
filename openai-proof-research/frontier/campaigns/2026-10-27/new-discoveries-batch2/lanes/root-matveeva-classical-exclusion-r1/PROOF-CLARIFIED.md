Root clarification of the frozen r100 proof after independent review. Only homogeneous-solution normalization and Laurent boundedness wording are clarified; frozen candidate bytes are preserved. No discovery credit.

# Full ordinary argument, classical reduction; discovery credit 0

This is a proof using standard named arithmetic differential-equation theorems, not an elementary proof or a proposed new intermediate theorem. It requires independent checking of the imported theorem applications before root adoption. No formalization or paper is supplied.

## Statement and conventions

Let d be any nonnegative integer, a_k,b_k rational with a_k nonzero for 0<=k<=d, and s_n rational for every n>=0. Suppose

    sum_{k=0}^d (a_k*n+b_k)*s_{n-k}=0   for every n>=d.

If the recurrence is imposed only after a larger finite starting index, the same argument applies. An exceptional index at which a_0*n+b_0=0 is allowed: the premise is an actual sequence satisfying the recurrence, not a division-based rule for constructing one.

Write S(x)=sum s_n*x^n. Then these are equivalent: S is algebraic over Q(x); S is a diagonal of a rational function regular at its expansion origin; S is globally bounded. Here global boundedness includes positive complex radius and integers C,D>0 with D*S(C*x) in Z[[x]]. This is equivalent to the source positive-index scaling convention for rational s_0: enlarge C and clear the constant by D. Conversely, if D*C^n*s_n is integral, (D*C)^n*s_n is integral for n>=1.

This covers the entire finite-order quantifier in Matveeva Conjecture 4.1, not just order two or the parameter-cancellation slice.

## Classical dependencies actually used

1. Chudnovsky: a system with a solution vector of G-functions whose components are linearly independent over Q(x) satisfies Galochkin's condition. Galochkin's condition implies global nilpotence; Katz then gives regular singularities and rational local exponents. These are stated in Beukers, AWS2008 Lecture3 slides10 and17 (the latter also explains the nilpotence step). Applied to a minimal scalar equation, every local solution has a regular-singular Frobenius expansion with rational exponents. Rational changes between a cyclic scalar equation and its first-order system preserve the differential module and this property.
2. André's integral primitive theorem: f in Z[[x]] with f' algebraic is algebraic. Bostan–Caruso–Roques 2304.05061v2 Theorem5.6 states this precise form; Matveeva Theorem4.2 supplies the globally bounded version. Scaling variable and function deduces that version directly from the integral one.
3. Eisenstein's denominator theorem for algebraic power series; Furstenberg's diagonal theorem; and exponential denominator bounds for rational-function diagonals. The last two are the source Propositions3.2–3.3. These are classical dependencies, not new results of this lane.

We do not infer a property of all solutions just from one integral solution of an arbitrary nonminimal operator. Minimality below is essential.

## Proof

Put A(x)=sum a_k*x^k and B(x)=sum (k*a_k+b_k)*x^k. Directly summing the recurrence gives

    x*A(x)*S'(x)+B(x)*S(x)=P(x),

where P is a rational polynomial supported on the finitely many indices before the recurrence starts. Indeed the coefficient of x^n on the left is exactly sum_{k<=min(n,d)} (a_k*n+b_k)*s_{n-k}. In particular A(0)=a_0!=0. Set r=-B/(x*A) and q=P/(x*A), so S'=r*S+q.

The direction algebraic => diagonal => globally bounded follows from the classical dependencies. We prove the remaining direction. A globally bounded analytic S is a G-function: its rational coefficients and their common denominators up to n have exponential bounds after clearing C,D; analyticity gives an exponential absolute bound. The displayed equation also gives D-finiteness after homogenizing. If S is rational there is nothing to prove. Hence assume S is not rational.

If q=0, S is a nonzero solution of the order-one operator D-r. This operator is minimal because a nonzero function has no order-zero rational annihilator. The Chudnovsky–Katz theorem makes it regular singular with rational local exponents. Its solution S is therefore algebraic, by the rank-one argument below. (One could instead apply the classical algebraic logarithmic-derivative theorem.)

Suppose q!=0. The functions S and S' are linearly independent over Q(x): a relation u*S+v*S'=0 gives (u+v*r)*S+v*q=0; since S is not rational, both coefficients must vanish, and q!=0 forces v=u=0. Consequently the monic order-two annihilator

    L=(D-q'/q)*(D-r)

is minimal for S. The vector (S,S') consists of G-functions (differentiation preserves the bounds) and has independent components. Chudnovsky–Katz therefore applies to this cyclic equation L, giving regular singularities and rational local exponents at every finite point and at infinity.

Let H be a local nonzero solution of H'=r*H, with its multiplicative constant to be normalized algebraically below. Then L(H)=0. The local singularity argument applies to any nonzero constant multiple; algebraicity over Qbar(x) is asserted only for an algebraically normalized branch. Because r is rational, its integral has the form a rational function plus a finite sum of residues times logarithms. A pole of r of order>=2 would give an exponential of a negative power in H near that pole, incompatible with a regular-singular Frobenius expansion. A nonzero polynomial part of r would do the same at infinity. Thus r has only simple finite poles and has no polynomial part. At a finite pole alpha the local solution is (x-alpha)^rho times an analytic nonvanishing factor, with rho=Res_alpha(r). Since H is a solution of L and all its local exponents are rational, rho is rational. Therefore

    H=constant*product_alpha (x-alpha)^{rho_alpha}

is algebraic over Qbar(x) when the multiplicative constant is chosen algebraic. The normalized branch H=x^rho*h with h(0)=1 used below is also algebraic: its normalizing constant is an algebraic value of the finite product of rational powers at the algebraic point zero after removal of x^rho. No claim is made for arbitrary transcendental constant multiples. This is the rank-one argument also used in the q=0 branch. Bostan–Caruso–Roques Proposition3.1 gives the same criterion and its proof. No assertion that arbitrary rational functions have rational residues is used.

We still have to justify applying the primitive theorem at the original possibly singular origin. Since r belongs to Q(x) and has at most a simple pole at zero with rational residue rho, normalize

    H=x^rho*h(x),  h(0)=1.

The equation h'/h=r-rho/x has rational Taylor coefficients, so recursive integration and exponentiation give h in Q[[x]]. The preceding argument shows h is algebraic; indeed it is algebraic over Q(x), since all its coefficients are rational and algebraicity over Qbar(x) descends by taking a finite product of conjugate equations. Choose N>=1 with N*rho integral. Then H(t^N) is an algebraic Laurent series in Q((t)).

Here a globally bounded Laurent series means a Laurent series which becomes a globally bounded Taylor series after multiplication by a finite integral power of t; it does not mean applying the source Taylor-series definition to a pole. Finite shifts and rational principal-part subtraction preserve this property after a constant multiplier is allowed.

The algebraic Laurent series 1/H(t^N) has only a finite pole and, by Eisenstein, has globally bounded power-series part. Products of globally bounded series are globally bounded, as is S(t^N). Hence

    U(t)=S(t^N)/H(t^N)

is a globally bounded Laurent series. Differentiating, with exact cancellation of the r terms, gives

    U'(t)=N*t^{N-1}*q(t^N)/H(t^N),

which is algebraic. Subtract the finite rational principal part R(t) of U and put V=U-R in Q[[t]]. It remains globally bounded and V'=U'-R' is algebraic. After integer scaling, André's theorem shows V is algebraic. Thus U and S(t^N)=U*H(t^N) are algebraic. Finally Q(t) is algebraic over Q(t^N), so transitivity shows S(t^N) algebraic over Q(t^N); renaming t^N as x proves S algebraic over Q(x). This proves all three equivalences. The d=0 case is also immediate directly: all but possibly one coefficient vanish.

## Strongest objection, falsifier, and boundary

The strongest objection is substantive originality: this is a short structural reduction to deep established theorems, not a campaign-eligible discovery. It is self-excluded from credit even if the ordinary argument passes review. No independently new inequality or arithmetic theorem is claimed.

The principal mathematical falsifier is a failure of the minimal-equation application of Chudnovsky–Katz: treating a nonminimal equation as globally nilpotent would invalidate the argument. The rational branch and the independence calculation explicitly remove that defect. A second falsifier would be omitting global boundedness after ramification or Laurent-pole removal; the explicit rational-Puiseux argument supplies this bridge. These are the specific review points, rather than unproved finite-to-infinite extrapolations. There is no asserted residual mathematical lemma in the ordinary argument, but independent review has not occurred and exact source-theorem applications remain subject to it.

Novelty/current-source completeness remains HOLD: a capped historical registry segment and a bounded web search cannot establish worldwide priority. The report supplies no acceptance recommendation, Lean endpoint, manuscript, or count change.
