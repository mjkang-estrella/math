# Elliptic translates and the existing tensor interface

This is a preselection feasibility/comparison record, not a frozen candidate or a request for a gate. The calculation below was used to test the strongest compatible reduction. No original theorem scope was frozen, weakened or replaced. All pinned source operations are stipulated true. External primary statements are credited at the actual reading extent below.

The exploratory family was the following. Fix a nonsingular real elliptic curve

    E: y²=x³+a x+b,   a,b real algebraic,

an arbitrary real point P, and an arbitrary finite subset S of the real algebraic points of E. Assume P+Q is not the identity for Q in S. Put t_Q=x(P+Q) and p(t)=((1−t²)/(1+t²),2t/(1+t²)). Could every such finite circle configuration be obtained from source172 at its original scale, for every finite coloring, without a restriction on |S| or the transcendence of P? The compatible certificate below indicates yes; no quantitative dimension bound is extracted. Duplicate points can be discarded, and configurations of at most two distinct points use the elementary source cases.

## Actual source and historical operations

The pinned source's `thm:classification` is a tensor criterion over the actual coordinate field F. It requires a matrix whose tensor evaluation vanishes at every configuration point and whose multiplied spatial block is the identity. Its `alg:equivalence` permits coefficients in a larger real tensor ring and descends them to F⊗_Q F by a field-linear coefficient expansion. Its `cons:quadratic` clears a determinant by adjugation and normalizes only by a scalar with nonzero multiplication image. These are substantive paid operations, not inferred from a spherical headline.

The actual arithmetic r42 `candidate.md` already constructs a bidegree-(2,2) polynomial by multiplying two (1,1) Möbius relations, with diagonal specialization (X−Y)². It explicitly localizes at the multiplication kernel, clears denominators AND annihilators, converts the quadratic coefficient matrix into the circle tensor, and descends coefficients. Structural r119 `two-frame.md` already handles arbitrary algebraic finite spherical blocks in two real projective Lorentz frames using adjugation and a separability projector. The local tensor/diagonal descent operation therefore cannot be offered as new here. The relevant I17 body passages also record the six-point and generic-seven-point comparisons; not all of I17 was reread.

## Strongest compatible elliptic calculation

Choose a finite real number field k containing a,b and the coordinates of S. If P is algebraic, all output coordinates are algebraic and the source's algebraic case applies. Otherwise write P=(u,v). Then u is transcendental over k and v≠0. Set K=k(u,v), so K is the function field of the geometrically integral curve E over k.

Work first in the localization A of K⊗_Q K at the kernel of multiplication m. Algebraic constants have equal left and right images in A: for c algebraic, factor its minimal polynomial difference as (c_L−c_R)g; the multiplication image of g is its nonzero derivative, hence g is a unit. Thus one can use identities over K⊗_k K in A. The latter tensor ring embeds in the function field of E×E because E is geometrically integral. Only finitely many identities are used.

Write Δ=u_L−u_R and

    D=(v_L+v_R)²−(u_L+u_R)Δ²,
    s=Δ²/D.

The denominator is a unit of A because m(D)=4v²≠0. Consequently s belongs to A and m(s)=0. Generically, d=D/Δ² is the x-coordinate of P_R−P_L, by the chord law. For every Q in S, its left and right images coincide, so

    (P_R+Q)−(P_L+Q)=P_R−P_L.

This exact cancellation, rather than an assumed independent relation for each output, supplies one COMMON parameter s for the whole configuration.

For short Weierstrass form the classical third summation polynomial is

    f3(X,Y,Z)=(X−Y)² Z²
      −2[(X+Y)(XY+a)+2b] Z
      +(XY−a)²−4b(X+Y).

Its sign choice is harmless: three points with the relevant x-coordinates can be chosen to sum to the identity. Multiplying f3(X,Y,1/s) by s² gives

    Q_s(X,Y)=(X−Y)²
      −2s[(X+Y)(XY+a)+2b]
      +s²[(XY−a)²−4b(X+Y)].

It has bidegree at most (2,2), vanishes at every (t_{Q,L},t_{Q,R}), and has exact multiplied specialization (X−Y)². The relation is first an identity at the generic point of E×E; as a regular localized identity it holds in A, including along the diagonal. Dividing by Δ was only a generic derivation, not an assertion that Δ is a unit at the diagonal.

There is an elementary independent check of the formula. With f(T)=T³+aT+b, direct polynomial expansion yields

    [f(X)+f(Y)−(Z+X+Y)(X−Y)²]²−4 f(X)f(Y)
       =(X−Y)² f3(X,Y,Z).

This is the elimination of the two y-coordinates in the chord law. The finite coefficient check recorded with this packet supports this displayed identity only; the general argument uses the algebraic identity, not sampling.

Clear the finitely many denominators of Q_s in the localized tensor ring. For each of its finitely many zero evaluations, localization provides an annihilator outside ker(m); multiply all these annihilators. The resulting coefficient matrix has exact zero evaluations in K⊗_Q K and multiplied matrix a nonzero scalar times the coefficient matrix of (X−Y)². Normalize by that real scalar. This is precisely the existing r42 operation; dropping the annihilator step would not justify exact zero evaluations in a tensor ring with zero divisors.

For completeness, let q(t)=(1,t,t²)^T and

    L=[[1,0,1],[1,0,−1],[0,2,0]],   S0=diag(−1,1,1).

Then Lq(t)=(1+t²)(1,p(t))^T. If J is the coefficient matrix of (X−Y)², L^T S0 L=−2J. For the normalized coefficient matrix C of Q_s, the matrix −2L^(−T) C L^(−1) has multiplication image S0 and zero tensor evaluations on every (1,p(t_Q)). Since 1+t_Q² is nonzero, those divisions are legitimate field operations. The source's coefficient descent then supplies its exact actual-coordinate-field contract. Its classifier supplies the all-coloring conclusion.

## Primary versions and timing

Initial elliptic feasibility preceded the primary formula comparison; every step remained before any freeze. The original Semaev eprint2004/031 PDF was denied with HTTP403. Its abstract/search result was navigation only. Galbraith–Gebregiyorgis, *Summation polynomial algorithms for elliptic curves in characteristic two*, author PDF `shishay.pdf`, §2.1 Lemma1, was read and page3 visually inspected. The displayed last term there prints a product X1X2 where the short-Weierstrass formula requires a sum X1+X2; this is visible in the PDF, not just an extraction error. We do not silently attribute the corrected formula to that version.

[Kosters–Yeo, arXiv1503.08001v3](https://arxiv.org/pdf/1503.08001v3), §2, defines the general symmetric S_A,3 in terms of b2,b4,b6,b8. Substituting a1=a2=a3=0, a4=a, a6=b gives exactly the formula above. Proposition2.1 states the point-sum interface over a general field. Its short proof reduces to r=2,3 and refers to Diem Lemma3.4; that helper was not followed. The displayed short-Weierstrass identity and the chord calculation independently check the specific r=3 use here. DLMF23.10.1 was also read through the web representation; direct retrieval was denied. None of these readings is backdated to initial feasibility.

## A boundary, not an alternative nominee

Allowing arbitrary real a,b while replacing algebraic S by points algebraic over the coefficient field is a genuinely different proposed family and is too broad. For transcendental r>1, let E_r:y²=x³−x+r. For seven distinct nonnegative rational c_i, the points with x_i=√(r+c_i) and positive y_i=√(x_i³−x_i+r) lie on this nonsingular curve and are algebraic over Q(r). With P the identity, the circle outputs are exactly Pálvölgyi's TheoremA.9 family in [2609.23327v1](https://arxiv.org/html/2609.23327v1).

That primary gives a derivative certificate with D(r)=1, H(T)=∏(T−x_i), w_i=x_i/H'(x_i). The moments in its equation(A.7) vanish by the degree-six Lagrange identities, while Σw_iD(x_i)²=−1/(4H(0))≠0. We read A.7, A.9 and LemmaA.1's invariant proof. The external coloring lemma used at the last step was not independently reread. This is an existing primary boundary, not an original non-Ramsey result or a source172 objection. It does not classify all variable-modulus elliptic configurations.

No unpaid compatibility operation was identified after the COMMON difference-point parameter, exact diagonal specialization, source descent and actual older local-tensor construction were put together. The elliptic headline alone is not a reason to nominate this screen. A general classification of Ramsey circle configurations, or a genuinely new higher-degree mechanism, remains unconstructed here. No claim of worldwide duplication, exhaustion, correctnessPASS or contribution rating is made.
