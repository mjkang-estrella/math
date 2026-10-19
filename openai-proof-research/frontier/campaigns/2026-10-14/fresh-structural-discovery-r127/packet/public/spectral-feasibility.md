# Smooth spectral generator: feasibility, not a frozen claim

The unfrozen question was whether there exists a smooth volume-preserving diffeomorphism T of the three-torus and a real centered **smooth** function f whose bilateral Koopman orbit is an orthonormal basis of the entire centered L2 space. No dimension change, proper invariant subspace, bounded-only function, finite set of correlations or subsequence is offered as a replacement. No exact target was frozen and no general proof is claimed.

## Actual source operation

Source144, *A smooth three-torus diffeomorphism with simple Lebesgue spectrum*, September23,2026, `01-introduction.tex` thm:main and `05-completion.tex` prop:stage, constructs T smooth but f in L2. Each intermediate map in its physical chart is

    S(theta,u,a)=(theta+phi(u),u,a).

On a good arc I, phi' does not vanish. A smooth packet A(u,a) exp(2 pi i m theta), m nonzero, has spectral density equal to the pushforward of |A|^2 du da by m phi modulo one. Finite smooth packet sums supported compactly in I have smooth densities. The source flat-vector construction permits nonsmooth endpoint cutoffs. Its final whitening divides by sqrt(p) and adds a flat vector on the zero-density spectral set. This is an L2 operation. Its exact norm cost is the Hellinger expression

    ||G||_2^2 + 1 - 2 integral sqrt(p).

The stage theorem independently permits arbitrary smooth map/inverse closeness and arbitrary L2 vector closeness. It does not assert smooth vector closeness. The complete stage proof and block iteration were read, including the parameter ordering, not merely that theorem's headline.

## Feasible operation 1: a smooth real flat vector at one twist

This calculation preceded any freeze. Choose a positive integer m so that the image interval J=m phi(I) has length greater than one. Choose b smooth, real, compactly supported in J, whose translates cover the circle in the sense

    D(s)=sum_(k in Z) b(s+k)^2 > 0  for all s.

Such b exists by taking it positive on a closed interval of length greater than one inside J. D is smooth, positive and one-periodic. Define

    a(s)=b(s)/sqrt(2D(s)),
    A(u)=sqrt(|m phi'(u)|) a(m phi(u)),
    W(theta,u,a)=A(u)e(m theta)+A(u)e(-m theta).

Extend A by zero outside its compact support in I. Then A and W are smooth and W is real and centered. Each of the two angular modes has constant folded spectral density 1/2: the Jacobian cancels |m phi'| and sum_k a(s+k)^2=1/2. The two angular modes are orthogonal. Hence W has density one and norm one. This removes endpoint discontinuity at a **single stage**. It is not a new system or a proof of the unfrozen question.

The sign of phi' does not affect the calculation because of the absolute Jacobian. The spare coordinate has probability mass one. Choosing m outside any prescribed finite set is allowed.

## Feasible operation 2: smooth whitening with a positive reserve

Let G be a real finite smooth packet sum with smooth even spectral density p. Choose W as above at an angular mode pair disjoint from every mode of G. The full cyclic subspaces are orthogonal, not just the vectors, because the twist preserves angular indices. For epsilon>0, set F=G+epsilon W. Its density is p+epsilon^2, everywhere positive. The multiplier

    psi(z)=(p(z)+epsilon^2)^(-1/2)

is smooth, real and even. Thus F'=psi(U_S)F is real, smooth, centered, and exactly flat. In packet coordinates psi(U_S) multiplies the m-th amplitude by psi(m phi(u)); finite support and smoothness are retained. There is no measurable zero-set term.

Moreover

    ||F'-G||_2 <= [integral (sqrt(p+epsilon^2)-1)^2]^(1/2)+epsilon.

As epsilon decreases to zero the first squared term tends to ||G||_2^2+1-2 integral sqrt(p). If a target H was approximated by Psi(U_S)G, then

    G=sqrt(p+epsilon^2)(U_S)F' - epsilon W.

Consequently the same target is approximated from F' using the smooth multiplier Psi sqrt(p+epsilon^2), with additional error at most epsilon ||Psi||_infinity. Smooth multipliers may be uniformly approximated by Laurent polynomials. Epsilon is chosen after the finite old estimator is fixed. This pays finite-stage smoothness, exact flatness and retention of a specified finite prediction simultaneously. No claim of uniform derivative bounds is made.

## What the source's strongest passage actually saves

The source passage uses sigma_N(a)=1/N+J(a)/N^2 and output index j of order N times an old frequency. Its density has a fast phase Nz. It would be incorrect to infer physical derivative growth N merely from that phase: on an output packet,

    z=j sigma_N(a),    Nz=j+(j/N)J(a),

so differentiation in a gives (j/N)J'(a), not j J'(a). The free large N therefore cancels in this particular derivative. The source's support drift estimates and refresh/transmission lemma explicitly keep normalized index and temporal frequency close, while allowing J to be chosen before N. These compatible operations were checked after the first feasibility calculation and before archiving.

This saving does not yet bound all physical derivatives through the full iteration. The physical chart itself changes, cutoffs depend on the actual packets, and broad neutral jitter and its derivatives are fixed before the passage integer. In the prediction blocks, the actual densities approximate

    p_r(z) product_i [1+2 lambda Re((b_r-q(z))e(-L_i z))].

The centering estimate is integrated; it pays Hellinger loss O(delta^2) per block while n lambda^2 is comparable to delta. The proof expressly requires no uniform derivative bound for successive q. Frequencies L_i are selected after the fixed coefficient lists to implement phase averaging. The sum of uncentered first-order absolute derivative costs is not controlled by the second-moment cancellation. The source guarantees arbitrarily small L2 transport, not the needed estimates on derivatives of that transport in the physical chart.

## Precise remaining step and diagnostic

A sufficient new stage interface would retain all map/inverse/prediction/bad-arc requirements and produce a smooth exactly flat f' with ||f'-f||_(C^r) below a prescribed tolerance for each prescribed finite r. Such an interface, with tolerances summable in a diagonal construction, would close this route. It is not proved here. Nor is a different full construction supplied.

Even inside the class of finite smooth packets, Hellinger closeness by itself cannot be converted to such a bound. Starting from a smooth flat W above, multiply its amplitudes by sqrt(1+epsilon cos(2 pi M m phi(u))). Its density is 1+epsilon cos(2 pi M z), using both conjugate modes and the evenness of this density. The Hellinger correction tends to zero with epsilon, whereas derivatives of its multiplier contain epsilon M and higher powers on any interior interval with nonzero amplitude and phi'. Taking epsilon=M^(-1/2) separates these norms. This is a diagnostic of an insufficient norm estimate. It is not shown to be an unavoidable output of the source's stage algorithm, and is not a counterexample to the full question.

## Antecedents and reading boundary

The actual parent-r7 screen already noticed the L2-only whitening issue and proved the separate finite-iterate-retention/subexponential-derivative consequence. Its entire argument was read. Kunde's author manuscript, *Smooth zero-entropy diffeomorphisms with ergodic derivative extension*, Lemmas3.1–3.2 and their complete retention proof, fixes a conjugacy before shrinking the rotation increment, controls finitely many iterate observations and sums future errors. It supplies a compatible map-retention operation; it supplies no estimate on a new spectral whitening multiplier. The primary is an unversioned author PDF, recorded by SHA256. No claim is made that its other sections exhaust smooth-generator literature.

Analyticr93's continuous-time screen distinguishes an L1 spectral density from a pointwise value at zero. That earlier obstruction was read at the recorded paragraphs; it is not a smooth-generator construction. Generic existence of a smooth cyclic vector, if obtained by a random dense smooth series, would not supply a flat spectral density. It is not offered as a reduced candidate.

A late full reading of analyticr95 `rescaled-carrier.md` and `stationary-clock.md`, after this note was first drafted and before sealing, found stronger physical-chart and stationary-phase bookkeeping for the distinct continuous-time target. In particular its rescaling cancels a carrier term, but its next winding-coordinate jitter has a derivative cost; its locally designed clock realizes a one-pass neutral matrix-density estimate without a proved global iteration. These are credited antecedents, not new operations claimed here. They do not supply the missing repeated-block smooth-generator estimate.
