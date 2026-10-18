# T022BA43: two attempted primitive-approximation routes

**Full frozen target UNRESOLVED; no nomination.** Neither route proves or refutes the assertion for every badly approximable shift and arbitrary divergent totient-weighted tolerance function. The fixed target in frozen-scope.md has SHA256 `4d10bf5feae4b1bbb1bfa19e1bfcbc46e4ac6c1e99d8181c43568344b367bf9f`. There is no replacement by monotone, dense-support, extra-divergence, quadratic-shift-only, or unrestricted-numerator scope.

The source022 main theorem gives arbitrary numerators, not gcd(a,q)=1. The current primary negative results were checked before freezing: Hauke-Treuer–Maynard–Pollington2609.30921v1 Theorem1 requires nonzero γ with |γ−r/s|<exp(−s^12) infinitely often (rational representations need not be reduced); its Remark1 explicitly leaves non-Liouville shifts unresolved. He–Liao2609.30870v2 Theorems1–2 give all nonzero rational shifts and a residual set of shifts. Neither statement says a badly approximable shift is a counterexample. Residual does not imply intersection with the badly approximable set. The exact ordinary numerator convention matters even under integer shifts.

## Route A: determinant separation, then aggregate rotation counting

Work first on R/Z and let E_q be the union of radius ρ_q=ψ(q)/q intervals centered at (a+γ)/q for a mod q coprime to q. For ψ≤1/2 their interiors are disjoint and

    μ_q=|E_q|=2φ(q)ψ(q)/q.

All subsequent claims about overlap are exact necessary conditions or upper estimates; none is a substitute for the full-measure assertion.

Write q=gm, r=gn, (m,n)=1. If two intervals meet, an integer determinant satisfies

    |na−mb+(n−m)γ| < Δ,
    Δ=nψ(q)+mψ(r)=(rψ(q)+qψ(r))/g.                (A1)

For q≠r the badly approximable hypothesis gives

    Δ≥cγ/|n−m|,
    g² ≤ cγ^(-1)|r−q|(rψ(q)+qψ(r)).              (A2)

The same condition holds for circular overlap by inserting the appropriate integer determinant. Before coprimality restrictions, each determinant has g pairs per first-coordinate unit period; hence an elementary upper bound is

    |E_q∩E_r| ≤ 2g min(ρ_q,ρ_r)(2Δ+1),           (A3)

with zero overlap when (A2) fails. Endpoints have measure zero. The source's actual ar:cycle and ar:sieve refine this count by residue averaging and small-prime exclusions when the determinant window is sufficiently long. For Δ<1 the additive 1 in (A3) is decisive.

### A uniform pairwise replacement is false, even for one quadratic shift

The attempted shortcut was |E_q∩E_r|≤Cγ μ_q μ_r for every distinct sufficiently late q,r. Here is a full counterexample to that shortcut, not to T022BA43.

Let γ=(sqrt(5)−1)/2 and F_j be Fibonacci numbers, F_0=0,F_1=1. This γ is badly approximable with constant1/3: for an integer l nearest hγ, the nonzero integer

    (hγ−l)(hγ'−l)=l²+hl−h²,  γ'=−1−γ,

has magnitude at least1, while |hγ'−l|≤sqrt(5)h+1/2≤3h.

Take j divisible by6, j≥6, set k=F_j,l=F_(j−1),n=k+1 and ε=γ^j. Then kγ=l−ε. Also gcd(l,n)=1: any common divisor divides2 by Cassini's identity because j is even, while l is odd because j−1 is not divisible by3.

Choose any prime p≥3 not dividing nl. It may be arbitrarily large. Put

    q=p, r=pn, ψ(q)=2ε/n, ψ(r)=2ε.

These tolerances are at most1/2. For every a∈{0,...,p−1} except the two distinct classes a=0 and na+l=0 mod p, let b=na+l. Then gcd(a,p)=1 and gcd(b,pn)=1, because b≡l mod n. There are p−2 such pairs. Their two centers are separated by ε/(pn), while both radii are2ε/(pn). Their intersection length is3ε/(pn). These particular intersections are disjoint as a varies and lie in [0,1] (j≥6 suffices), so

    |E_p∩E_(pn)| ≥ 3ε(p−2)/(pn).

Meanwhile

    μ_p=4ε(p−1)/(pn),
    μ_(pn)=4ε(p−1)φ(n)/(pn).

Therefore

    |E_p∩E_(pn)|/(μ_p μ_(pn))
      ≥ 3(p−2)pn/[16ε(p−1)²φ(n)]
      ≥ 1/(16ε) → ∞.                            (A4)

This disproves the proposed pairwise shortcut with q and r both arbitrarily late. It does not force failure of an averaged second moment, since each such cluster can still be charged linearly to first mass. Treating (A4) as a counterexample to the frozen limsup target would be invalid.

### Attempt to pay the bad pairs in aggregate

For integers 0<|h|≤H, the points hγ mod1 are cγ/(2H)-separated (compare two indices). Consequently an interval of length2δ contains Oγ(Hδ+1) such points. This is a direct spacing bound, not a probabilistic independence assertion.

As a model computation, let all q lie in [N,2N] with a common tolerance ψ(q)=1/N. For pairs with gcd g, their reduced difference h=(r−q)/g lies in an interval of length O(N/g), and the short-window condition is ||hγ||≤O(1/g). Per first row this gives at most Oγ(N/g²+1) possible h. There are at most O(N/g) first rows divisible by g. Multiplying by the additive-window overlap scale O(g/N²) gives

    Oγ(1/g²+1/N)

at each g≤2N. Summing is Oγ(1). Terms with long determinant windows are also bounded by the quadratic first-mass scale. Thus this crude rotation calculation does control the dense equal-width model. It is consistent with the target but does not prove it.

The attempted extension to sparse nonmonotone ψ fails at a concrete place: the count Oγ(Hδ+1) is an ambient-interval bound, not a bound in the selected denominator mass. For M selected rows in [N,2N], it yields M(N/g²+1)-type estimates with an ambient N term rather than the M² term demanded by first mass. Arbitrary selections may focus on return differences. Moreover (A3) discards both primitive densities; μ_q contains φ(q)/q, which can be arbitrarily small. A bound in Σψ(q) cannot replace a bound in Σφ(q)ψ(q)/q. The source's sieve pays some long-window factors, but not the short-window, highly selected, totient-weighted quadratic form. No new estimate controlling that form was derived here.

A sufficient missing mechanism would construct, on every sufficiently late totient-mass block, primitive-supported weights with positive local first mass and an Oγ(W+W²) second moment, with constants independent of the support and the prime factors of its denominators. Uniform pairwise quasi-independence is stronger and false by (A4). Ordinary ambient rotation discrepancy is too weak for that mechanism.

## Route B: modify the source's projected-array construction

This attempt preserves the source's actual mechanism instead of assuming its main theorem applies to primitive centers. The operative contracts read are:

* tables.tex `tab:projected-grid`: a row assigned to center L_i and deficits d,a has v=L_i/(da) and projected points (z+aγ)/(L_i/d). The projected phase is aγ, not γ.
* `tab:first-currency`: the mask coefficient π_I(a), projected grid size and one numerator factor R reproduce r_iφ(v). The coefficient is not another free numerator-density budget.
* prescriptions.tex `pre:recognized-models`, `pre:low-hard-tests`: rational models ζ=n0/s of the projected phase forbid sz+n0=0 mod primes in the model's prescribed range. This is shift-adapted primitivity, not z=0 or final-numerator coprimality.
* `pre:hard-mean`: mean hard birth weight is bounded below by a fixed constant times one totient product. Its proof allows a second model only because the additional primes have a uniformly bounded reciprocal sum.
* `pre:soft-tests`: gcd(sz+n0,V) is bounded by a power of model height. The displayed `dir:soft-ratios` in direct.tex uses precisely this bound to control the number of exact-model partners. Ordinary gcd(z,V)=1 does not imply it.

### First attempted repair: use bad approximability to eliminate all rational models

For the true phase γ, a broad model with denominator s≤Q and error ≤Q^(-3) is impossible for Q>1/cγ, since |γ−n0/s|≥cγ/s²≥cγ/Q². This initially looked promising.

It does not survive the actual projection. From bad approximability one only gets

    |aγ−n0/s| ≥ cγ/(a s²).                        (B1)

The remaining deficit a is not uniformly bounded. More concretely, for the golden-ratio shift and a=F_j, the projected phase aγ differs from the integer F_(j−1) by γ^j. Set projected width ψ_proj=γ^j. The integer model then has height

    H=2+1+|aγ−F_(j−1)|/ψ_proj=4.

As j grows the projected width meets any fixed small-width threshold, while the model remains recognized at fixed height. This is an exact projected-phase arithmetic example. It is not claimed that every such a and width is an assigned good row in the source's complete center selection. It proves that the proposed uniform inference 'γ badly approximable ⇒ no projected rational models' is invalid, so that inference cannot close the construction.

### Second attempted repair: intersect source model restrictions with ordinary primitivity

At a prime p avoiding a n0 s, an eventual true point has z=ab, with final numerator b. A model exclusion sz+n0≠0 mod p becomes b≠−n0/(sa) mod p. Ordinary coprimality imposes b≠0 mod p. These are distinct residues. For a finite set P of such primes, CRT gives exact densities

    one exclusion:  ∏_(p∈P)(1−1/p),
    both exclusions:∏_(p∈P)(1−2/p).

The ratio is ∏_(p∈P)(1−1/(p−1)), which tends to0 as P exhausts the primes outside the fixed finite exceptional set. This is the precise first-mass loss: a second arbitrary primitive sieve is not free. At scalar-replacement primes, merely retaining the old scalar factor and adding an ordinary coprime test also introduces an extra totient factor. Replacing the scalar by a test would avoid that particular loss, but does not solve the distinct active-model exclusions.

Unlike the source's two-model argument, ordinary primitivity does not automatically restrict its extra exclusions to a prime range with bounded reciprocal sum. Dropping the model restrictions instead loses the soft gcd estimate and hence the paid exact-model partner bound. Thus neither simple intersection nor replacement has a verified first-mass/variance interface.

A possible repair would estimate the total deficit-law mass of projected rows whose active rational-model exclusions conflict with ordinary primitivity, showing their aggregate loss is small, or charge those conflicts within a new covariance budget. (B1) alone supplies no such bound uniformly over multiplicative deficit masks. This requires a weighted sparse rotation/prime-factor estimate not derived here. No counterexample to that repair or to T022BA43 is asserted.

## Outcome

Both routes were carried past statement screening: RouteA gives a full counterexample to the hoped-for pairwise bound and an aggregate dense-block calculation; RouteB traces the precise projected phase, reconstructs the model obstruction, and computes the independent-primitivity loss relative to the source's actual mass currency. The remaining bridge is a support-sensitive, totient-weighted aggregate estimate, not source factorization or an omitted routine parameter substitution.

These observations are method diagnostics, not substantial new results. No candidate for the20-result count is proposed. The original badly-approximable primitive limsup assertion remains unproved and unrefuted.
