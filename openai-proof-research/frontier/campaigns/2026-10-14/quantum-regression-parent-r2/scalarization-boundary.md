# Scalar moments and the quantum projection estimate

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Parent author research, 2026-10-18. This note preserves the full provisional Q140 target in structural r56 and supplies no nomination, independent gate or count credit.

## The exact cost of forgetting the geometric structure

Let (X,μ) be a probability space, D≥2 and q≥1 an integer. For a measurable positive semidefinite D-by-D complex matrix F(x), define

    K = sup_{||u||=1} (∫(u*F(x)u)^q dμ(x))^(1/q).

Then the best universal conversion from this scalar bound is

    (∫Tr(F(x)^q)dμ(x))^(1/q)
       ≤ [D(D+1)…(D+q−1)/q!]^(1/q) K.                 (1)

This constant is attained. For q≥2 the factor cannot generally be replaced by D^(1/q), even allowing a constant depending on q alone.

To prove (1), let v be uniform on the unit sphere in C^D, independently of x. The squared moduli of its coordinates are uniform on the simplex. One way to see this is to normalize D independent standard complex Gaussian coordinates: their squared moduli are independent exponential random variables, and the change of variables into their sum and normalized proportions has density proportional to exp(−sum) times sum^(D−1). Thus the proportions have constant density on the simplex. For a multi-index α with Σα_i=q, its moment is

    E ∏|v_i|^(2α_i) = (D−1)! ∏α_i!/(D+q−1)!.

Diagonalizing a fixed positive F with eigenvalues λ_i and expanding the q-th power gives

    E_v (v*Fv)^q = q!/(D)_q · h_q(λ),
    h_q(λ) = Σ_{α_i≥0, Σα_i=q} ∏λ_i^(α_i),
    (D)_q = D(D+1)…(D+q−1).

Every summand is nonnegative, and h_q(λ)≥Σλ_i^q=Tr(F^q). Tonelli and the definition of K prove (1), including possibly infinite quantities before imposing K<∞.

For equality, take X to be the complex unit sphere with uniform probability and F(v)=D vv*. For each fixed unit u, unitary invariance yields

    ∫(u*F(v)u)^q dv = D^q q!/(D)_q,
    ∫Tr(F(v)^q)dv = D^q.

Only one eigenvalue is nonzero, so every preceding inequality is an equality. The scalar q-th moment is at most q!, whereas the trace moment is D^q. Relative to the desired D^(1/q)K bound, the loss is exactly

    [(D+1)…(D+q−1)/q!]^(1/q).

For q≥2 and D=exp(Θ(d²)), q=Θ(d), its logarithm is Θ(d²), not O(d). A factorial or polynomial-in-q allowance cannot absorb this. This is an elementary optimal conversion identity, not a substantial new theorem or a priority claim.

## Consequence for the open proof route

The scalar source projection theorem can be applied separately to the measures u*Ωu under the operator ball-growth bound. The resulting uniform scalar moment estimates cannot alone give the desired dimension-linear Schatten moment. One must also exploit the common spatial measure and the random Gaussian projection, or establish another operator estimate. The example above is an abstract matrix-valued random variable. It is not constructed as the Gaussian pushforward of a Frostman operator measure and therefore does not refute the proposed projection estimate or Q140.

The required matrix estimate also need not be uniform in D. Write a proposed norm estimate as the source scale times D^(1/q)L(d,D), where q and the ball-growth exponent are proportional to d. In the regime D≤2^(A d²), it suffices that log L(d,D)≤C_A d. A fixed power of log(D+1), or a polynomial in d and q, would satisfy this. A fixed positive power of D would not. This identifies the tolerated dimension loss without changing the full quantum-learning target.

## A primary comparison and the remaining operation

Nazarov–Treil–Volberg, *Counterexample to the infinite dimensional Carleson embedding theorem*, Theorem 1.1, bounds a dyadic vector-valued embedding norm by C log D times the operator measure's Carleson intensity. Theorem 1.2 gives a growing lower bound. Their upper-bound sketch uses resolvents, a Bellman inequality and complex interpolation of a scalar analytic function. These are examples of logarithmic dimension loss under operator testing; they are not Gaussian-projection moment estimates. [Author-hosted primary PDF](https://www.math.brown.edu/~treil/papers/carl/carl-cr3.pdf).

No reduction from the present Gaussian pushforward to that dyadic embedding has been established. In particular the output route may depend on the full exact (A,y), and ball growth alone has not been converted into the required Carleson testing condition on an appropriate filtration. Citing the embedding theorem without that reduction would leave the main obligation unpaid.

Reading limits: this parent read the cited PDF's theorem statements on pp1–2 and upper-bound sketch on pp5–6 through the primary PDF text. Its lower-bound construction was not needed and is not claimed as fully checked. A separate primary Culiuc–Treil theorem statement was screened on the publisher page; its displayed dimension-squared constant does not supply the desired loss, and it is not a dependency. Other returned search hits were discovery pointers only. This note adds no new semantic reading of the six family140 source companions and makes no literature-wide search claim. The elementary calculation above is re-derived here rather than inferred from any search result.
