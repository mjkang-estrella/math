# Parent calculation for the proposed SK replacement argument

2026-10-17, Myeongjin Kang, original prose CC BY 4.0. This note responds to analytic r28's **pre-freeze** feasibility calculation. It is not a frozen candidate, independent proof review, contribution verdict or acceptance. The author must check it independently and compare actual antecedents before selecting a target. No source theorem is being audited.

Consider the zero-field partition function

    F(J)=log Σ_(σ∈{−1,1}^n) exp[(β/√n) Σ_(i<j) J_ij σ_iσ_j].

Here β is fixed. Original coordinates ξ_e are independent, centered, variance one, with sup_e E|ξ_e|^4≤K. They may be nonidentical and depend on n. Let g_e be independent standard Gaussians. Set a0=|β|/√n. Constants below depend on β,K and a fixed derivative order, but not n or the particular hybrid array. External fields are excluded: the vertex-gauge argument uses zero field.

The agent's proposed mean/test-function argument compares a deleted-edge third derivative with its reflected-star version. This note supplies a way to avoid requiring a fifth moment when extending that argument to variance. It does not assert the replacement mechanism is new to the literature.

## Finite hybrid family and gauge step

Let H be the finite collection of product laws choosing independently for each coordinate one of ξ_e, −ξ_e or g_e. Define

    c=E F(g), V=Var F(g),
    M=max_(ν∈H) E_ν[(F−c)^2].

M is finite: F is bounded in absolute value by n log2+a0 Σ_e |J_e|, and these variables have finite second moments. The finite hybrid family is closed under coordinatewise Lindeberg replacement and reflection of any star. There is no need to include arrays with arbitrary sets of deleted edges.

Every mixed derivative of F of total order k≥1 is bounded uniformly in the couplings by C_k a0^k. Indeed the derivatives are joint cumulants of k variables σ_iσ_j, each bounded by1; the finite partition formula for cumulants bounds their absolute values. This also bounds repeated-coordinate derivatives.

Fix an edge e=(i,j), set J_e=0 and let S be the other edges incident to i. Flipping spin σ_i proves F(J)=F(T_iJ), where T_i negates the whole star. Differentiating three times with respect to J_e before evaluating at0 shows that ∂_e^3 Ψ(F) is odd under reflection of S, for any scalar function Ψ. This applies to Ψ(F)=F, a smooth test function of F, and (F−c)^2.

Conditional on non-star coordinates, the S coordinates remain independent. A second-order Taylor comparison between each star-coordinate law and its reflection cancels orders0,1,2. For Ψ(F)=F, the third derivative of the compared expression is a mixed derivative of F of total order6. Consequently

    |E ∂_e^3 F |_(J_e=0)| ≤ C |S| a0^6 sup_f E|J_f|^3.

The factor1/2 from oddness is absorbed in C. Ordinary fourth-order outer remainders then yield |E_ν F−c|≤C for all ν∈H: there are O(n²) outer edges and O(n) coordinates in each star, so both n²a0^4 and n³a0^6 are bounded. No sixth moment is used; order6 refers to a derivative, not to a random-variable moment.

## Fourth-order outer remainder without a fifth moment

Hold all but one coordinate fixed, write H(z)=F(z)−c=H0+u(z), where u(0)=0 and |u^(k)(z)|≤C_k a0^k for k≥1. Let c1=u'(0), c2=u''(0). The exact identity

    u(z)^2−c1²z²−c1c2z³
      =2c1z[u(z)−c1z−(c2/2)z²]+[u(z)−c1z]²

and ordinary Taylor bounds of orders2 and3 imply an O(a0^4|z|^4) remainder. Expanding H(z)^2=H0²+2H0u(z)+u(z)^2 through degree3 therefore gives

    |remainder| ≤ C a0^4 |z|^4 (|H0|+1).                 (A)

H0 is independent of the replaced coordinate under each product law. Hence taking expectation in (A) requires only its fourth moment. A crude bound on the fourth derivative of H(z)^2 at an interpolation point would instead introduce an unnecessary |z|^5 term.

## Inner reflected-star comparison for the square

At J_e=0 put B=∂_e^3[(F−c)^2]. The product rule gives

    B=2(F−c) ∂_e^3F+6(∂_eF)(∂_e^2F).

For another star coordinate f and arbitrary real z=J_f, the mixed derivative bounds imply

    |∂_f^3 B(z)| ≤ C a0^6 (|F(z)−c|+1)
                  ≤ C a0^6 (|F(0)−c|+1+a0|z|).

The second-order Taylor remainder of B(z) is thus bounded by

    C a0^6 [(|F(0)−c|+1)|z|^3+a0|z|^4].               (B)

Here both e and f are zero in F(0). Restore them with independent variables from a compatible hybrid law. The deterministic coordinate Lipschitz bound and Cauchy–Schwarz show

    E|F(e=f=0)−c| ≤ sqrt(M)+2a0 sup_h E|J_h|.

The same estimate with one deleted coordinate controls H0 in (A). Thus (B) is integrable under the finite-fourth-moment assumption and each star replacement costs at most C a0^6(sqrt(M)+1). Independence separates the deleted-coordinate base value from the replaced variable. Oddness of B under the whole star flip gives

    |E B| ≤ C n a0^6 (sqrt(M)+1).

## Bootstrap and centering

For each ν∈H, telescope the square observable to the Gaussian law. Its outer cubic term is bounded by the preceding star estimate times the uniformly bounded third-moment difference. Its fourth-order remainders obey (A). Summing gives

    |E_ν[(F−c)^2]−V| ≤ C (sqrt(M)+1).

Taking the maximum first yields M≤V+C sqrt(M)+C. Solving the quadratic inequality in sqrt(M) gives sqrt(M)≤sqrt(V)+C', and substituting back yields

    |E_ν[(F−c)^2]−V| ≤ C'(sqrt(V)+1).

The earlier O(1) mean comparison implies (E_ν F−c)^2=O(1). Therefore the same order of error holds for the variances centered at their own expectations:

    |Var_ν F−Var_g F| ≤ C''(sqrt(Var_g F)+1).

In particular this would preserve a diverging Gaussian variance asymptotic, if all hypotheses and the preceding replacement estimates are checked. It does not establish variance universality at a bounded fluctuation scale. Smooth-test comparison at a diverging scale remains the agent's separate proposed argument; this note neither supplies a full source-limit theorem nor settles its contribution status.
