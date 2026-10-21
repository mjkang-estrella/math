# Strongest integrated reduction and exact remaining gap

PREFREEZE / no nominee. This is working mathematics, not a frozen theorem, conjecture nomination, correctness verdict, contribution grade, or a substitute for an old scope.

## Actual classical duality is available

The initial conditional normalization in note01 was subsequently compared with the actual Frank–Murota primary, arXiv:2007.03507v1. Theorem3.3 and its proof produce a compatible optimal dual for integer-valued separable convex costs on an integral box-TDI system; Section4.2 explicitly applies the framework and weight splitting to intersections of integral base polyhedra. The proof uses a box-TDI linear program, the unit-move optimality inequalities, and fitting subgradients. It is not legitimate to leave supporting-price existence wholly unpaid.

At its exact integer-cost interface, let Φ(x)=Σφ_e(x_e) and x* minimize Φ on Ω. The primary supplies a subgradient w and a dual y for Qx≥p such that

    φ_e(x*_e)−φ_e(x*_e−1) ≤ w_e ≤ φ_e(x*_e+1)−φ_e(x*_e),
    y≥0,  w=yQ,  y(Qx*−p)=0.

For each coordinate define q_e(t)=φ_e(t)−φ_e(x*_e)−w_e(t−x*_e). These q_e are nonnegative convex sequences, vanish at x*_e, and

    Φ(x)−Φ(x*) = Σ_e q_e(x_e) + y(Qx−p).                 (D)

All terms on the right are nonnegative on Ω. This equality follows directly, not from an unproved Gibbs comparison. Weight splitting supplies w=w1+w2 with x* minimizing wi·x on B(ri). Hence another exact form is

    Φ(x)−Φ(x*) = Σ_e q_e(x_e)+ℓ1(x)+ℓ2(x),
    ℓi(x)=wi·(x−x*) ≥0 on B(ri).                        (S)

Take Ai(x)=exp(−ℓi(x)−(1/2)Σ_e q_e(x_e)) on B(ri). Each is a modular tilt times unary log-concave weights, normalized to1 at x*. The compatible signatures and root-direction proof in note01 apply to this split. On Ω, A1(x)A2(x)=exp(−Φ(x)+Φ(x*)). Thus the strongest reduction keeps both the classical dual and the actual source weighted algebra, rather than testing an incompatible product of separate minimizers.

The split Ai≤1 is established on the corresponding hard base sets. It does not supply a uniform bound on every point of a softened auxiliary box; such off-constraint values also need control in a complete counter.

There is a crucial accounting distinction: the rank-slack term y(Qx−p) in(D) is generally NOT constant on Ω. It cannot be discarded as if every active rank inequality were a network conservation equality. The table argument in r57 has a special reduced-cost decomposition into physical box losses. Its conclusion remains credited at its whole original scope, but(D) does not automatically give the identical box-only decomposition for arbitrary ranks.

For B≥|Ω|, low-loss truncation at K≥log B+log(1/δ) is compatible with(D): points with Φ(x)−Φ(x*)>K have normalized mass at mostδ. Intersecting each condition q_e≤K and each positive dual-slack contribution≤K keeps that low-loss set, keeps x*, and has excluded mass at mostδ. The normalized partition is ≥1. For integer data the dual may be chosen integral and sparse (the primary gives at most2n−1 positive multipliers for an appropriate box-TDI description). Uncrossing in the pinned source supplies chains for nonnegative combinations of tight rank normals. This gives finite chain/coordinate information, but does not by itself prove that every resulting positive near-tight slab restriction is a single base polytope or that its weighted count has a polynomial-capacity representation.

The exact arithmetic integer-cost interface above is stronger than an abstract suggestion. The primary read does not alone implement approximate-log oracles, cost rationalization, all bit budgets, or a counter. Those algorithmic representations remain unspecified because no full theorem was frozen. The remaining mathematical issue below persists even granting a supplied exact optimizer and dual; it is not being attributed merely to missing optimization literature.

## Why arbitrary extra slices cannot be silently absorbed

Let M be the rank2 partition matroid with blocks{1,2} and{3,4}. Its bases are13,14,23,24. Restrict to |B∩{1,3}|≤1. The surviving bases are14,23,24. They are not the bases of a matroid: from14 toward23, exchanging the element4 for2 gives12, and exchanging it for3 gives13; both are forbidden. The equality slice |B∩{1,3}|=1 consists of14,23 and also fails exchange. This is an exact small check of one proposed representation, not a hardness theorem.

A face imposed by tight rank equations is different and has the classical minor/direct-sum structure. The source's polyhedral-controls lemma explicitly covers two base systems with coordinate bounds, OR one base system with partition equalities; it does not grant a third arbitrary partition family on top of two systems. Its geometry proof deliberately subdivides the two systems separately and compares their paired sums. Any use of near-optimal cost levels as new ports must preserve that compatible construction, rather than applying the counter to unsupported conditional slices. The r141 projection representation remains available at its actual projection hypotheses; it does not itself erase an extra arbitrary constraint.

For integer q_e, the set q_e=0 is an interval. Away from a zero interval, nonzero integer slopes have magnitude at least1, so q_e≤K adds at most floor(K) positions at either end (within the original domain). This pays unary tail localization even if the zero interval is exponentially long. The long flat directions and the two systems' near-tight rank totals still need a joint counting model. Merely enumerating all boundary/flat choices uses exponentially many regimes; it is not a polynomial algorithm. This observation is a direct convexity deduction, not a result nomination.

## An exact diagnostic for the proposed integral shortcut

For u∈R^3 let F(u)=2^{−(u1−u2)^2}. Its logarithm is a concave quadratic, so it is a positive log-concave weight on every box. It is also a single univariate log-concave weight composed with a signed linear form, of the type that must be treated carefully after a tree-coordinate map. No claim is made that this three-variable toy is a complete feasible instance of the source's normalized port model.

Restrict to the integer slice u1+u2+u3=2 in[0,2]^3. At the box-valid addition display0, its signature matrix is

    Q = [[1/16, 1,    1/2],
         [1,    1/16, 1/2],
         [1/2,  1/2,  1  ]].

On span{(1,1,0),(0,0,1)} its Gram matrix is [[17/8,1],[1,1]], with determinant9/8>0, so it has two positive directions. The orthogonal antisymmetric direction(1,−1,0) has value−15/8. Thus ordinary log-concavity does not imply this integer addition signature. This is separate from I29's hard-intersection log-concavity failure and does not contradict any pinned proof.

The failure cannot be repaired by an arbitrarily small pointwise perturbation on this same slice. If every entry is changed by at most10% relatively, the symmetric two-dimensional restriction has first diagonal≥(17/8)(9/10), second diagonal≥9/10, and cross entry≤11/10. Its determinant is at least

    (17/8)(9/10)^2−(11/10)^2 = 409/800 >0.

This also allows nonsymmetric dependence on u1,u2: the restriction uses Q11+Q22+2Q12, Q13+Q23, Q33, so each displayed bound remains valid. A common positive normalization is irrelevant to inertia. Consequently no coefficientwise10%-accurate replacement of this toy's weights can have the required signature on the same domain.

For the particular source-like isotropic correction Fα(u)=F(u)exp(−α||u||²/2), put t=exp(−α)∈(0,1]. The two-dimensional determinant equals

    t²(t²/8+2t−1).

Having at most one positive direction therefore requires t²/16+t≤1/2, equivalently t≤6√2−8<1/2. The correction changes the relative factor between diagonal configurations2e_i and off-diagonal configurations e_i+e_j by t, more than a factor2. No common normalization makes all six masses relatively ε-close for ε≤1/3. The exact check uses t=1,1/2,12/25; it requires no floating eigensolver.

This diagnoses a SPECIFIC proposed generic input to the port smoothing step. The actual source succeeds because its integrated weights have the much smaller quantitative derivative bounds proved in ports.tex. Its small added curvature absorbs finite-difference errors uniformly at all powers without materially changing the balanced mass. Those operations are fully credited. The toy does not rule out re-encoding, a different auxiliary domain, controlling only the balanced sum, retained discrete elimination, or another compatible construction.

## What is still unpaid

The strongest integrated route now consists of:

1. Actual convex-cost duality and weight splitting at their stated integer-cost interface;
2. normalized unary-plus-rank losses, with elementary exponential tail clipping;
3. positive rank-factor signatures with the unary block corrections, and balanced-summation/root-direction log-concavity;
4. the source/classical factorial lifts, two-weight transport, observable variance and trace machinery, whenever a polynomial-size positive model and an efficient evaluator are supplied.

For arbitrary binary-capacity common integer bases with genuinely varying separable log-concave weights, this round has NOT constructed a polynomial-size model whose balanced mass approximates the ORIGINAL weighted normalizer, whose full-domain weight powers obey both signatures, and whose individual evaluations have bounded oracle and bit complexity. In particular, no compatible uniform quadrature/smoothing comparison has been proved for the new weighted block integrals, and no exact discrete evaluator avoiding exponential hidden ranges has been supplied. Ordinary log-concavity and existence of a convex optimizer do not supply those obligations. Conversely, their failure in one attempted representation is not evidence that classical composition cannot eventually pay them.

No importance, difficulty, large parameters, binary hypothesis removal, or completion of an older quantifier is offered as evidence of substantial contribution. The exact diagnostic is supporting research, not a substitute nominee. All old W152/I29/projection/full-target scopes and dispositions remain untouched. There is no new-to-literature, latest-record, priority, exhaustion, or current-openness claim.
