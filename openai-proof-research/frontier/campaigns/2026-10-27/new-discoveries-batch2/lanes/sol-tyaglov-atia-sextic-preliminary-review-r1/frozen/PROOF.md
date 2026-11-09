# Ordinary proof: a sextic refutes Tyaglov–Atia Conjecture 3

Status: complete ordinary counterexample proof; provisional research nomination only. No Lean, manuscript, acceptance or count change.

Primary: Mikhail Tyaglov–Mohamed J. Atia, arXiv:1912.04951v5, 19 June 2020, printed p24, Conjecture 3; definition (3.20). Actual frozen body: ../sources via this lane's sources/1912.04951.pdf, SHA256 7242fff819de94524d106fca14e8da73cf16fd249d391cd580f69a30de459ab6. Exact retrieval https://arxiv.org/pdf/1912.04951. The conjecture quantifies over every real polynomial p of even degree n with no real zeros and with all zeros of p' real. Its middle clause asserts, for every 1/2<kappa<=(n-1)/n,

    Z_C(p)-2 <= Z_R(Q_kappa[p]) <= Z_C(p),
    Q_kappa[p]=(p p''-kappa (p')^2)/p^2.

Zero counts include multiplicities. The example below has eight DISTINCT real zeros, so no convention about multiplicities rescues the upper bound. A counterexample to this clause refutes the full conjunction; the other two regimes are not refuted or separately credited.

Take kappa=3/4 and

    P(x)=50x^6-13200x^4-600x^3+177450x^2+304200x+108312103.

Then

    P'(x)=300(x+13)(x+2)(x+1)(x-3)(x-13).

Thus P has degree n=6 and its derivative has five simple real zeros. Since P tends to positive infinity at both ends, it attains a global minimum at a critical point. At the five critical points -13,-2,-1,3,13 its respective values are

    3, 108210303, 108172803, 109772803, 5272803.

Every value is positive; therefore P(x)>=3 for every real x. In particular P has no real zero and Z_C(P)=6, by the fundamental theorem of algebra with multiplicity. Also 1/2<3/4<5/6, strictly within the source middle regime.

Direct polynomial multiplication gives

    4PP''-3(P')^2=1200 J,
    J(x)=25x^10-13200x^8-900x^7+414050x^6+1064700x^5
         +525944015x^4-79953900x^3-57294664659x^2
         -1479679536x+127901873749.

Consequently Q_(3/4)[P]=300 J/P^2. Its denominator is strictly positive everywhere on R, so each real zero of J is a zero of the literal source rational function, with the same multiplicity and no cancellation at a real point.

The following exact integer evaluations exhibit eight disjoint open sign-change intervals:

|Interval (a,b)|J(a)|J(b)|
|---|---:|---:|
|(-20,-19)|4354463200869|-4696251086376|
|(-14,-13)|-266271947271|164736|
|(-13,-12)|164736|-184798658075|
|(-2,-1)|-89273499975|72692123616|
|(1,2)|69574984344|-96403570119|
|(12,13)|-31266038939|287895043800|
|(14,15)|209008140921|-472396598816|
|(19,20)|-2185650428544|7526093619429|

By continuity and the intermediate value theorem, each interval contains a zero. The open intervals are pairwise disjoint; shared endpoint -13 is not a zero. Hence Z_R(Q_(3/4)[P])>=8>6=Z_C(P), contradicting Conjecture 3. This completes the refutation. Exact total zero count, smallest possible degree and optimal replacement bound are not asserted.

Independent validation: work/proof_check.py uses only integer list arithmetic, independently reconstructs P', multiplies both numerator sides and checks all endpoint values. SymPy's root isolation was discovery assistance; it is unnecessary for this proof. The independent checker is finite arithmetic support for the displayed identities, while positivity and existence of roots follow from the ordinary arguments above.

Closest later body: Katkova–Tyaglov–Vishnyakova arXiv:2406.00686v1 (2 June 2024), Theorem2.2, Sections9/12/16, especially Example16.2, was read before finalizing. Its middle-regime three-crossing example has degree FIVE and real zeros; it does not satisfy this source conjecture's positive-even-polynomial hypotheses. Its Theorem2.2 handles kappa>(n-1)/n and therefore does not preclude this counterexample. Its H_kappa has the OPPOSITE numerator sign and its rational Q uses denominator (p')^2; these conventions must not be silently identified with the original Q. Our real zeros cannot occur at P' roots either, as P'' is nonzero there and P>0. The later paper supplies a related public mechanism, not a demonstrated exact full-positive-sextic subsumer. Whether a specialist prior proof/construction already resolves this precise target remains an independent eligibility gate.
