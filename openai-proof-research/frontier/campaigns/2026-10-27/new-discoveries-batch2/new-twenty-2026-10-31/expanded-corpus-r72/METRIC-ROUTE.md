# MathDB 377505: ordinary counterexample route, not an accepted solution

Source read: Calcaterra–Boldt–Green–Bleecker, arXiv:math/0206253v1, Definition 1 (PDF p. 2), Definition 48 and Conjecture 49 (PDF p. 29). Check the PDF page rather than trusting extracted pagination. Definition 1 permits C anywhere in M, not merely in the neighborhood X. Definition 48 requires, for every point, a neighborhood coordinatized by a set of the given cardinality. No connectedness, manifold, or absence of isolated points hypothesis appears in either definition. A lipeomorphism is a bijective Lipschitz map with Lipschitz inverse (footnote 5). This route uses the exact all-metric-spaces scope, without changing an endpoint or a quantifier.

## Explicit pair of compact metric spaces

Let M consist of o and the pairs (n,b), n a nonnegative integer and b in {0,1}. Set r_n=4^{-n}, w(o)=0, w(n,b)=r_n, x(o)=0, and x(n,b)=(1+b)r_n. Define

* d_E(u,v)=|x(u)-x(v)|;
* d_U(u,u)=0, and d_U(u,v)=max(w(u),w(v)) for u different from v.

The map x is injective. Indeed, within one level the two coordinates differ by r_n>0. If m>n, then x(m,c)<=2r_m<=r_n/2<r_n<=x(n,b). Consequently d_E is a metric. For d_U, symmetry and positive definiteness are immediate; if u,v,z are distinct, max(w(u),w(v))<=max(max(w(u),w(z)),max(w(z),w(v))). If two coincide the triangle inequality also holds. Thus d_U is an ultrametric, in particular a metric.

For all u,v,

    d_U(u,v)/2 <= d_E(u,v) <= 2 d_U(u,v).

For equal points this is immediate. For o and a point at level n, d_E is r_n or 2r_n and d_U is r_n. For distinct points at the same level, both distances equal r_n. For levels n<m, d_U=r_n, and r_n/2<=r_n-2r_m<=x(n,b)-x(m,c)<=2r_n. These cases are exhaustive. The identity is therefore a lipeomorphism in both directions, with Lipschitz constants at most 2. The image x(M) is a compact subset of the real line: each nonzero point is isolated and every sequence whose levels tend to infinity converges to zero. The inequalities also give compactness for d_U.

## Exact source dimensions

For d_E, the single anchor a=(0,1), whose coordinate is 2, distinguishes every point globally: d_E(u,a)=2-x(u). Every point thus has a neighborhood metrically coordinatized by a singleton, in the precise sense of Definition 1. Dimension zero is impossible: every neighborhood of o contains o and a nonzero point, and the empty anchor set cannot distinguish them. Hence the source metric-coordinate dimension is exactly 1.

For d_U, let C be any finite set of anchors and X any neighborhood of o. Choose epsilon>0 with B_U(o,epsilon) contained in X. Choose n larger than the level of every nonzero member of C and large enough that r_n<epsilon. The two points u=(n,0), v=(n,1) lie in X and are distinct. For anchor o both distances equal r_n. For any other anchor c=(m,b) in C, m<n and both distances equal r_m. Thus C does not coordinatize X. This holds for every finite C, including the empty set. Conversely C=M is countably infinite and distinguishes every pair globally: anchor u distinguishes u from v by 0<d_U(u,v). The source dimension is exactly aleph_0.

Thus Conjecture 49 would identify 1 and aleph_0, a contradiction. The obstruction is the entire local dimension, not just failure of a particular chosen anchor under transport. In particular the freedom to choose anchors outside X has been handled.

## Validation and material limits

`outputs/metric-finite.json` checks exact rational inequalities on the first nine levels, and checks the twin obstruction against anchors through level four. These finite checks do not prove the infinite statement. The proof above supplies the required quantifiers.

No literal Lean endpoint, extracted replay, leanchecker certificate, or declaration audit has been completed. No discovery credit is requested. Formal obligations remaining: construct both actual metric structures; establish x injective and the uniform bounds; construct the lipeomorphism; translate Definition 48 to least cardinal of local resolving sets; prove the two exact cardinal values with actual metric neighborhoods and all possible anchors. Formalizing only the finite prefixes would not resolve this target.

Prior investigation so far: exact source body; ancestor campaign ID/title/source-string screen; live registry HEADs and complete current Omega D5/Problems path lists; arXiv API searches for the phrase "metric-coordinate dimension" and for "metric coordinate". The exact-phrase search returned no entries and the broader search located the original paper among irrelevant modern results. These are bounded non-findings, not novelty clearance. Publisher/citation bodies and alternative terminology (local resolving number, metric bases) remain a material novelty/significance gap. An elementary construction may still be a known routine example. Root adjudication and independent review are required.
