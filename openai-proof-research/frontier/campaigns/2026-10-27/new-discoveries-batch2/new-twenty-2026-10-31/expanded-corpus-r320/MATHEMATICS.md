# Ordinary mathematics and failed full-scope routes

All work is ordinary reasoning. There was no mathematical enumeration, solver, CAS, Lean execution or delegated execution. No result below is accepted or source-qualified as a discovery. The three sustained routes are 373062, 373193 and 372790.

## 373062: slope obstruction, its exact scope, and why it is not an eligible endpoint

Primary source: Molyneux, arXiv:2602.08748v1, Definitions 3.1–3.4, Section 3.2, Section 4 including Theorem 4.1, Lemma 4.5 and Conjecture 4.6. The abstract page lists only v1, February 9, 2026. The fetched unversioned and explicit v1 bodies have the same SHA. Actual Section 4 proof and Figure 10 caption were read; figure geometry was not visually inspected. No claim of complete companion/journal/correction clearance is made.

Let k>1 be an integer, a_i nonnegative integers, and P(X)=sum_i a_i X^(ki)-1. Assume the nontrivial case sum_i a_i>1. The positive root b satisfies 0<b<1: P(0)<0, P(1)>0 and strict monotonicity on positive numbers give uniqueness. The source's subdivision uses a_i legs of relative interval length b^(ki), in any allowed ordering.

Induction on the number of carets proves that every leaf interval of every such finite subdivision tree has length b^(km), m a nonnegative integer. Initially the root has length one. Adding a caret multiplies its leaf's length by b^(ki), which preserves this property. In a pair of trees with order-preserving leaf matching, the affine slope on every leaf interval is the ratio of two such lengths, hence is b^(kz), z an integer. This also holds after refinements and composition, since the slopes multiply and all exponents remain in k Z.

There is an explicit element of the full source group F_b whose slope on an interval is b. Choose a positive integer N with (1+b)b^N<1 and put t=b^N, c=(1+b)t. Define on [0,1]

f(x)=b x for 0<=x<=t;
f(x)=b t + b^(-1)(x-t) for t<=x<=c;
f(x)=x for c<=x<=1.

At t both formulas are b t. At c the middle formula equals b t+t=c, so f is continuous. All slopes are positive, endpoints are 0 and 1, and therefore this is an increasing PL homeomorphism. Its inverse has the reciprocal slopes and breakpoints b t,c, also in Z[b]. Its two original breakpoints t,c lie in Z[b]; its slopes b,b^-1,1 lie in <b>. Hence f belongs to Definition 3.2's F_b. Because b^r is injective in integer r for 0<b<1, b cannot equal b^(kz): that would require kz=1. Thus no polynomial-based tree pair of the described kind represents f.

This completes the obstruction for that precise tree system. A second attempt via ring independence Z[b^k] versus Z[b] is unnecessary and can fail if the root has smaller algebraic degree; the slope argument avoids that assumption. A third issue remains: the paper's final paragraph also discusses excluding different tree-pair representations. The leaf-depth invariant alone does NOT prohibit a system allowing extra carets with exponents not divisible by k, nor an abstract group encoding. The phrase “well-defined tree-pair representation” must be fixed before treating this as the full requested answer. The literal record also permits P=X^k-1: then b=1, the source's explicitly discarded trivial case, and the strict inequalities and bump construction do not apply. Treating that case as a refutation would be an endpoint correction, excluded by the task.

Scientific disposition: this scoped obstruction is a direct complete bridge from the source's stated leaf-depth construction and the classical definition of a PL group. It is useful review evidence, not a novel eligible theorem or a full literal answer. No dormant Pi implementation is warranted. Missing gate: prove that the exact intended semantics excludes all alternative tree systems and reconcile the trivial coefficients without replacing the problem; then perform full prior-art/significance and independent fidelity review. Nothing here licenses execution.

## 373193: exact Markov recurrence and two failed comparisons

Primary source: Geneson et al., arXiv:2602.16300v1 (February 18, 2026); abstract page has v1 only and explicit/unversioned HTML match. Actual incoming-neighbor rule, finiteness proof of Theorem 2.1, complete-bipartite proof of Theorem 3.7, Conjecture 3.12 and printed Table 2 were read. The table is already public evidence, not a new certificate.

Let A,B have sizes a>b>=1. In a state with i blue vertices of A and j blue vertices of B, every white vertex of A independently becomes blue with probability j/b, and every white vertex of B independently becomes blue with probability i/a, using the state before the simultaneous update. Therefore, conditional on the state, the increments U,V are independent Binomial(a-i,j/b) and Binomial(b-j,i/a). Let T(i,j) be expected remaining completion time. For the absorbing state T(a,b)=0. For any nonempty nonabsorbing state,

(1-P00) T(i,j) = 1 + sum_{(u,v)!=(0,0)} P(U=u)P(V=v) T(i+u,j+v).

Here P00=(1-j/b)^(a-i)(1-i/a)^(b-j), with the natural empty-product conventions. P00<1 because at least one part has a blue vertex and an uncolored opposite vertex, unless a part is already all blue, when the other finishes deterministically in the next round. More explicitly, from any nonempty state there is a uniformly positive chance (depending on finite a,b) to color the opposite part in one step and everything else in the next. This supplies a geometric two-round tail and finite expectations, so the recurrence is justified without solving or enumerating it. The exact conjecture is T(0,1)<T(1,0).

First attempted mechanism: standard monotone coupling. Give each white vertex a fresh independent uniform threshold; increasing either count increases all update probabilities. This proves attractiveness for coordinatewise ordered initial blue sets. It does not order (0,1) and (1,0). Comparing part fractions also fails at time zero, since one process has the larger fraction in A and the other in B. In particular, the first-step opposing infections have different Binomial(a,1/b) and Binomial(b,1/a) laws on different coordinates. A comparison of their means is not a hitting-time comparison.

Second mechanism: two-step coupling and ancestry. Realize the rule by each white vertex sampling one uniformly chosen opposite neighbor and copying blue if that neighbor is blue; blue persists. Backward possible ancestry expands through temporal parent choices with waiting from persistence. This representation is exact, but no injection was proved between the events that all vertices reach a fixed seed in the two different parts. Correlation between descendants prevents replacing it by independent geometric infection times. A two-step mean inequality would likewise fail to imply stochastic order of the maximum infection time.

At b=1 the source star case is immediate: seed in B finishes in one round; seed in A waits a geometric time of mean a for B to become blue, then one further deterministic round, so expectations are 1 and a+1. This is a parameter case, not a solution. For full a>b>1 the missing lemma is a strict inequality of the two absorbing-time distributions, or an expectation comparison proved from the exact recurrence for ALL a,b. No such lemma was established. No search or recurrence solver was run. No eligible certificate or Pi plan.

## 372790: a rigorous orthogonality reduction with a remaining ambient component

Primary source: Terwilliger–Williford, arXiv:2601.19163v1, January 27, 2026. Abstract page has only v1; explicit/unversioned bodies match. The source hypotheses include H_q(D,N-D), N>2D>=6, q!=2, E the second-eigenvalue idempotent, and vertices at distance 2<=k<=D-1. The literal record abbreviates these and cannot be treated as a theorem about arbitrary Norton algebras.

Source Definition 7.2 makes S the six-dimensional span of E O_i; Definition 10.7 makes U=Sym(S) the five-dimensional span of E O_i^vee and A=ASym(S)=span(a), where a=E xhat-E yhat. Proposition 10.9 proves the orthogonal decomposition S=U direct-sum A. Definition 11.1 gives u star v=E(u coordinatewise-times v); this algebra is commutative, but not associative. Lemma 11.2 proves the invariant pairing <u star v,w>=<u,v star w>. Proposition 11.14, via the explicit products in 11.13, proves U star A subset A.

For u,v in U, <u star v,a>=<u,v star a>=0, since v star a is in A and u is orthogonal to A. This is a complete deduction. Consequently projection of u star v to S lies in U. It DOES NOT show u star v itself lies in S: an arbitrary component in (S orthogonal) intersect EV has not been eliminated. Thus the involution/fixed-space intuition only places the product in a larger ambient symmetric space unless its equality with U is proved. Claiming symmetric closure at this point would be a mathematical error.

Second mechanism: Proposition 12.14 supplies a basis B, B star B, B star(B star B), B star(B star(B star B)) for U intersect omega-perp, B=E xhat+E yhat. Proposition 11.16 shows multiplication by B preserves U, and Lemma 12.13 shows preservation of the intersection. In an associative algebra this would imply closure of the generated power span. In a nonassociative algebra, products such as (B star B) star (B star B) cannot be reassociated into the known right-nested chain. Neither commutativity nor the invariant pairing supplies that reassociation. The paper itself distinguishes its span theorem from Conjecture 12.16 about the generated subalgebra.

The exact missing finite-dimensional identities are (I-P_S) E(u_i coordinatewise-times u_j)=0 for a genuine basis u_1,...,u_5 of U, universally in the source parameters. Bilinearity would then prove the exact closure, with the antisymmetric component already eliminated. This is a precise mathematical gap, not an instruction to enumerate finite graphs or execute symbolic algebra. No identities of this strength have been proved here; no valid counterexample has been supplied. Companion and journal/correction proof-body coverage is incomplete. Park with zero credit.

## Compact additional checks

Neumann 372942 is already subsumed positively by source Theorem 1.2 with the same primitive/non-regular hypotheses: its witness has fix(g)<=n^(1/3)<=sqrt(n). Section 3's actual reduction and diagonal/product proofs were read. The remaining long simple-group cases were not independently audited; that is unnecessary to see that a public claimed exact stronger positive result precludes presenting this as our discovery.

The braces records omit the source's no-nontrivial-tight-cut requirement. C6 supplies an exact refutation of the weakened definition: it is connected bipartite, every edge extends to a perfect matching, and its sole cycle is conformal. It is not K_2,2 or any complete bipartite graph. But the three consecutive vertices in C6 form a shore whose cut is met by every perfect matching exactly once, so C6 is not a source brace. This is only a definition correction. The cubic source result is not all regular degrees.

The Kimura source's false-conjecture paragraph refutes a fixed GROUP ORDER formula, not either assigned structural/prime-divisor statement. Its displayed orders cannot be repurposed as witnesses. The pattern source's nonunimodal partition example is in a different poset. Neither is a discovery.
