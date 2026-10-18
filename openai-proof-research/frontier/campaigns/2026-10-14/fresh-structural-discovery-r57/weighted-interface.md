# Quantitative weighted interface for the unchanged W152 target

Author-side technical deduction, conditional only on the stipulated source115 results and standard polynomial-bit minimum-cost flow. This document supplies the parameter and numerical interface; it does not claim a new mixing theorem or an independent review. Read limits are recorded separately. All logarithms carrying subscript 2 have base two; `ln` is natural logarithm.

## 1. Rational logarithms and exact optimization

Let the feasible set be Ω={x∈Z^E: Bx=b, 0≤x≤u}, represented as a bipartite flow fiber. Write U=Σu_e, N₀=∏(u_e+1). Feasibility is polynomial-bit integral flow. If infeasible return the exact empty flag. A feasible table can always be retained as a fallback.

For η∈(0,1), approximate c_e=−log₂θ_e by rational ĉ_e with absolute error at most η/(1+U). This stronger convenient bound implies

    |ln w(x) − ln ŵ(x)| ≤ η,       ŵ(x)=2^(−ĉ·x).

Here ln2<1 and Σx_e≤U. Precision requires O(log(1+U)+log(1/η)) fractional bits, not U operations. An explicit rational logarithm routine is as follows. Write a positive rational t as 2^k y with 1≤y<2 using integer comparisons; |k| is bounded by the bit length of t. For z=(y−1)/(y+1)∈[0,1/3), use

    ln y = 2Σ_{j=0}^{M−1} z^(2j+1)/(2j+1) + remainder,
    0≤remainder≤ 2 z^(2M+1)/((2M+1)(1−z²)).

Compute ln2 by the same series at z=1/3, and divide certified rational intervals to obtain ln y/ln2. The denominator is bounded away from zero (ln2>1/2). Add k exactly. M polynomial in the requested accuracy bits suffices; sums and powers have polynomial bit lengths even with unreduced product denominators. Thus no huge exponential is formed.

Normalize the two laws separately. Since e^(−η)≤w/ŵ≤e^η, their partition functions obey the same inequalities and their normalized likelihood ratio lies in [e^(−2η),e^(2η)]. Consequently TV≤(e^(2η)−1)/2. These errors are charged separately from truncation and from the eventual sampler.

Minimize the rational objective ĉ·x. A polynomial-bit min-cost flow algorithm gives an integral optimum x*. Rational costs may first be scaled to integers by a common denominator of polynomial bit length. Exact dual potentials π can also be obtained after optimization by shortest paths in the residual graph, which has no negative cycle; add a new zero-length source to all vertices. With a consistent incidence sign convention these yield reduced costs r=ĉ−Bᵀπ satisfying complementary slackness. In particular x*_e=0 when r_e>0 and x*_e=u_e when r_e<0. Equivalently, primal-dual equality gives

    C*=ĉ·x*=π·b+Σ_{r_e<0}r_eu_e,
    ĉ·x−C* = Σ_{r_e>0}r_ex_e + Σ_{r_e<0}(−r_e)(u_e−x_e) = g(x)

for every feasible x. Each term q_e in the final sum is nonnegative on the whole physical box. This is standard reduced-cost optimality, not a new operation credited to this packet.

## 2. Localization without an incompatible endpoint choice

For δ∈(0,1), choose an integer

    K≥log₂N₀+log₂(1/δ)+1.

Ceilings can be computed by integer comparisons. Restrict x_e≤floor(K/r_e) for r_e>0, and u_e−x_e≤floor(K/(−r_e)) for r_e<0, intersecting with the original bounds. A zero reduced cost imposes no restriction. The resulting box contains x*, simultaneously for all cells. It also contains every feasible x with g(x)≤K. Thus its excluded ŵ-mass is at most N₀2^(−C*−K)≤δ2^(−C*)≤δ Ẑ. Conditional restriction changes the ŵ-law by at most δ in TV and its normalizer by a relative factor between 1−δ and 1.

Every nonzero coefficient and every floor comparison is exact rational arithmetic. If K/|r_e| exceeds u_e, leave the original bound. Tiny r_e cannot increase encoding length beyond polynomial: numerators and denominators of all reduced costs and of K/|r_e| have polynomial bit lengths. No approximate zero test or comparison of transcendental costs is used.

Tighten the restricted box again by computing each feasible cell minimum and maximum, then translate by the minima as in source115 `scales.tex`. All restricted feasible tables are preserved. Write b_e for the positive translated widths and retain constants in q_e. Then

    0≤q_e≤K on its physical interval,    |r_e|b_e≤K.

The optimum x* survives, so min g=0 on the resulting feasible fiber. Its gap partition function Z_g=Σfeasible2^(−g) is at least one. The normalizer of the localized ŵ-law is 2^(−C*)Z_g.

## 3. Uniform bounds on all source profiles

Use d=mn+m+n+2. On small cells evaluate q_e at the row physical value, even for an unbalanced two-view profile. On free and tree cells use their common physical value. This choice agrees with g on feasible tables and multiplies the source finite laminar model by unary exponential factors in row coordinates; it does not introduce a nonlaminar interaction.

For each tree cell the source forest bound gives translated values in [−10db_t,10db_t], including the extended continuous free box. Since |r_t|b_t≤K, each corresponding q_t is between −10dK and (10d+1)K. Small coordinates stay physical. A free coordinate in [0,b_e+1] has |q_e|≤2K because b_e≥1. Therefore the integer

    G=32d²K

bounds |g| on every profile and free assignment used by the oracle. No feasibility or balance assumption on the small profile is used in this bound. In normalized free coordinates u_e=z_e/(b_e+1), the source forest cut identity and |r_e|b_e≤K give

    |g(u)−g(u′)| ≤ (2d²+2d)K ||u−u′||∞.

All translation constants are retained exactly. In particular the weight is not inadvertently multiplied by a different constant at each small profile.

## 4. Noncircular annealing parameters

Let L be a polynomial bound on the new encoded instance, including its rational reduced costs; it also bounds log₂ of the product of its physical widths plus one. Choose ε∈(0,1), and set

    T=ceil(20(L+d+2G+log₂(1/ε)+1)),
    γ=ε/(512dT),  A=ceil(4T/γ),
    B_bin=32d²(A+K),  W=100dB_bin,
    H_D=10Ad²(W+1),  H′=H_D+2G.

Use W for the source small/large division and maximum-capacity forest, and its penalty D with coefficient A. Define

    P=D+g+G.

Then 0≤P≤H′ on all required profiles, P is convex as a function of free variables, and in cube coordinates v∈[0,B_bin]^e its Lipschitz constant is at most

    [2Ad²+(2d²+2d)K]/B_bin ≤ 1/8.

All parameters have polynomial numerical size in L, ε⁻¹ and K; G is independent of W and of the annealing length. Thus there is no circular requirement to make the bin scale larger than its own objective range.

Set h_j=Σfreeinteger2^(−jP/H′), j=0,…,H′. At j=0 this is exactly the source constant M_f. The source factorial lifts, initial defect totals and initial sampler are unchanged. Additional unary geometric factors are log-concave, so `integer-signatures.tex` gives both full-domain signature properties and log-concave tree marginals. Their proofs permit arbitrary positive unary factors, not just bounded-range coefficients. The two factorial lifts still agree on transversals and differ by at most W² on actual defect states.

The source `evaluation.tex` uses only the displayed convexity, range, and bin Lipschitz estimates. With P replacing D and H′ replacing H, its dyadic floor weights, population correction, conductance, finite walk caps and unconditional rational output bounds all apply. Rational denominators now include the reduced-cost denominators, which have polynomial total bit length. The final correction still has exponent in [−2,2]. In particular it never evaluates a huge 2^(−C*) as an ordinary rational.

The source transport lemmas use only the two signatures, positivity and the W² lift comparison. They retain their same polynomial constants in p≤dW. Adjacent h_j ratios remain in [1/2,1], and the minimum transversal mass is at least 2^(−H′−p−T). Thus the capped warm-trace annealing proof and fair-bit coupling in `algorithm.tex` carry over with H′,T. This is application of those stipulated source lemmas, not a reproof or claimed semantic reading of every transport proof line.

## 5. Weighted contamination, with the offset canceled

For analysis cancel the common 2^(−G) factor at the final parameter. The softened total is C_g=Σassignments2^(−D−g), and its feasible part is Z_g≥1. There are at most 2^L assignments, each mass at most 2^G. A far violation has D≥Aγ≥4T; hence its total mass is at most 2^(L+G−4T)≤ε/128, also a bound on its fraction of C_g.

Every tree marginal a_t remains log-concave. It satisfies a_t(k)≤2^(L+G) and a_t(0),a_t(b_t)≥2^(−G), because tightened endpoints are attained by actual feasible tables with D=0 and g≤G. Thus for every positive exterior marginal value, its ratio to the opposite attained endpoint is at most 2^(L+2G)≤2^T. Interpolating over the first floor((b_t−k)/T)+1 integers toward that endpoint gives a_t(k)/C_g≤2T/b_t, exactly as in the source. Fewer than γb_t integers occur in each near exterior strip. Summing over both sides and at most d tree cells gives near contamination at most 4dγT=ε/128. Consequently

    Z_g≤C_g≤(1+ε/32)Z_g.

The source counter estimates C(P-final)=2^(−G)C_g. Multiplying by 2^G has polynomial bit cost since G itself is polynomial. Its usual ε-budget and median amplification therefore give a relative approximation of Z_g, with polynomial work on every execution. The source all-small, p=0, p=1 and no-free-coordinate cases persist; if no positive-width cell survives, Z_g=1 directly.

## 6. Compact output and weighted sampling

For a requested additive error a in log₂Z, allocate η, δ and the relative error of the preceding gap counter smaller than fixed constant multiples of min(a,1). The estimates in §§1–2 and §5 then bound the accumulated log₂ error by a. Output

    −C* + log₂(estimated Z_g)

as a rational additive-log approximation, using the certified logarithm routine from §1. C* can have exponentially large numerical magnitude but polynomial binary length; its rational representation is never expanded as a power of two. The estimate of Z_g has ordinary polynomial bit length. A zero counter output on a failed run is replaced by any fixed finite log value; its probability is already part of the counter failure event. Amplification gives any confidence 1−ζ in time polynomial in log(1/ζ). A compact binary exponent and polynomial-length mantissa may equivalently be recovered from the log estimate. Choosing a proportional to the requested relative error supplies that interpretation. Empty instances retain an exact empty flag.

Sampling uses the source binary interval self-reduction on the ORIGINAL weighted fiber. At each node, both children are tested for feasibility exactly. A single feasible child is chosen deterministically. Otherwise estimate each child's original log normalizer independently to additive accuracy α and failure probability β. A child interval [a_e,d_e] is translated by x_e=a_e+y_e. Retain the scalar log-weight Σa_e log₂θ_e; do not form ∏θ_e^(a_e) as an ordinary rational. The logarithm approximations use the original upper-bound sum U (or separately allocate the same precision to this shift), so the combined error on the shift and residual objective remains within the requested budget. Equivalently carry the rational constant ĉ·a throughout minimum-cost localization, with C* now including that constant. All original lower endpoints are bounded by the original capacities and therefore have polynomial bit length. This makes each child call an estimate of its ORIGINAL weight, rather than of an inconsistently renormalized shifted fiber.

The approximate branch probability is the logistic function of the two log-normalizer difference. Approximation error in each natural log at most α gives probability error at most 2α (a loose bound). Differences larger than log(1/χ) in absolute value may be clamped to the corresponding endpoint with probability error at most χ; all remaining exponentials have polynomial magnitude and can be evaluated by bounded rational-series arithmetic. For example range-reduce exp(t) to t/2^s of absolute value at most one, approximate there by its Taylor series with the factorial remainder bound, and square s times with sufficiently many guard bits; s and all needed precision bits are polynomial in the log-input lengths and log(1/χ). Round the branch probability dyadically to accuracy χ using a fixed number of bits. On failed log evaluations still choose one of the two feasible children.

A path has at most D₀=Σceil(log₂(u_e+1)) decisions. Choose α,β,χ≤τ/[100max(1,D₀)]. Fresh randomness and the conditional per-node failure bound give a coupling error at most D₀(2α+2β+2χ)≤τ. This includes both perturbation and truncation inside each child-normalizer call because the log oracle estimates the ORIGINAL child's normalizer with those errors already budgeted. There is no additional uncharged global truncation in this sampler. Every output is feasible and every loop is deterministically polynomially capped. This is weighted Jerrum–Valiant–Vazirani self-reduction, already operationally present in source115 `flows.tex`; no new sampling mechanism is claimed.

## 7. Contribution and limits

The numerical large-cell obstruction in I152 is repaired by localizing the near-optimal reduced-cost box before applying equal bins. The proof preserves full binary W152 and does not rely on unary expansion. However, minimum-cost duality, elementary exponential tail truncation, adding affine tilts to a log-concave density, source signature closure/transport/annealing, and weighted self-reduction are established operations. This author regards the assembled deduction as TECHNICAL, not a substantial campaign nominee. This is neither an exact-literature-duplicate claim nor an independent contribution gate. Finite diagnostics, if supplied, check only algebraic interfaces, not the entire sampler.
