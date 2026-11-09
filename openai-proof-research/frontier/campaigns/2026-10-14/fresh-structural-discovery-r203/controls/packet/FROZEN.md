# Frozen r203 statement: finite Markov witnesses from approximate James arrays

Frozen after the full canonical source, specified primary proof sections, and guarded original-history work recorded in NOTES.md. This is a research author-proof target, not an assigned correctness/contribution/acceptance verdict. The entire scope below is fixed; if any obligation fails, these bytes are to remain unchanged.

## Explicit integers

For integers c≥2 and s≥k≥1, define recursively

    R_1(s,c) = c(s−1)+1,
    t = R_{k−1}(s,c)+1,
    R_k(s,c) = (t+1)c^(t^k)                 (k≥2).

For h≥a≥1, define S(a,h,c) by b_a=h and b_{k−1}=R_k(b_k,c), k=a,a−1,…,1, and set S(a,h,c)=b_0.

Given a real p>1, an integer n≥1, and 0<θ≤1, define

    L = 8(n+1),
    m = 8L + (L+4n+1) sum_{j=0}^n 4^j,
    r_0 = 4^m,
    c_0 = (40 n r_0 + 2)^(r_0),
    B = S(m,m,c_0),
    A = B^m,
    C(n) = A(8nA^2+1)^(2A^2),
    σ = θ/(4L),
    ξ = θ/(4096BL),
    η = (ξ/24)^2,
    Q = ceil(16/ξ),
    T = ceil((16/ξ)^p),
    H = B Q^T,
    J = ceil(4H/η),
    c_1 = (ceil(2H/η)+2)^((2J+1)^H),
    M(p,n,θ) = S(H,H,c_1).

All these are finite, explicit functions of the displayed parameters; no numerical evaluation of the huge integers is asserted or needed.

## Theorem A — finite witness in the original norm

Let X be any real normed vector space, including incomplete, finite-dimensional, zero, or nonseparable spaces. Suppose there are vectors y_1,…,y_M in its closed unit ball and bounded real linear functionals f_1,…,f_M in the closed dual unit ball, where M=M(p,n,θ), such that

    |f_i(y_j) − θ 1_{i≤j}| ≤ σ          for all 1≤i,j≤M.

Then there are a finite state set S with |S|≤C(n), a transition matrix P on S, a probability law π satisfying π_i P_ij=π_j P_ji, and a map F:S→span_R{y_1,…,y_M}⊂X such that the chain starts in π and

    E ||F(Z_1)−F(Z_0)||_X^p = 1,
    E ||F(Z_n)−F(Z_0)||_X^p ≥ (3/40)(n/96)^p.

No irreducibility, uniform stationary law, bounded degree, or restriction on the positive stationary masses is claimed. The map and chain can depend on the array and displayed parameters. Every norm in these inequalities is the original norm of X. No equivalent norm or metric substitution occurs.

## Corollary B — explicit J-convexity data from Markov type

Let p>1 and K≥1. Suppose the original norm of a real normed space X satisfies

    E ||h(Z_t)−h(Z_0)||_X^p ≤ K^p t E ||h(Z_1)−h(Z_0)||_X^p

for every finite stationary reversible chain, every map h into X, and every integer t≥1. Put

    n_* = ceil(((40/3)(96K)^p)^(1/(p−1)))+1,
    L_* = 8(n_*+1),
    M_* = M(p,n_*,1),
    ε_* = 1/(4L_*).

Then every x_1,…,x_{M_*} in the closed unit ball of X satisfies

    min_{0≤j≤M_*} ||sum_{i≤j}x_i − sum_{i>j}x_i||_X ≤ M_*−ε_*.

Thus the normalized J-convexity deficit is at least ε_*/M_* at the explicit order M_*.

## Boundaries of the frozen scope

The theorem is conditional only on its displayed finite-array hypothesis and the stipulated operative Source327 chart/action constructions at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its proof must supply the stated Ramsey, finite-averaging, merging, probability, finite-lift, coordinate-extraction, and J-convexity steps. It asserts neither an optimal bound nor any uniform convexity/smoothness exponent, renorming distortion, martingale-type exponent, metric-cotype parameter, Markov-convexity parameter, or new-to-literature priority. It does not rename or restrict any prior closed target. No formalization is claimed.
