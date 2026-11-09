# Body-adapted spectral exclusion and a high-order line-incidence estimate

These are original author deductions within the unchanged full thin-covering attempt, not a narrower candidate. They address two concrete parts of the remaining incidence problem. They do not establish the full high-load tail or exact coverage.

## 1. A coordinate-free exclusion with small probability cost

Let S be ANY nonempty subset of F_p^n, let alpha=|S|/p^n, and let U be uniform of dimension r. Put mu=alpha p^r and

 c(xi)=|S|^(-1) sum_(z in S) exp(2 pi i xi.z/p).

Parseval says sum_xi |c(xi)|^2=alpha^(-1). Define the genuinely body-dependent large spectrum

 B_tau={xi!=0: |c(xi)|>tau},
 E_tau={U^perp intersect B_tau is empty}.

With theta=(p^(n-r)-1)/(p^n-1)<=2p^(-r), a union bound gives

 P(E_tau^c)<=theta |B_tau|<=2/(mu tau^2).

This exclusion is covariant under every invertible linear change of coordinates, unlike sparse support. Taking tau=mu^(-1/4) gives P(E_tau)>=1-2mu^(-1/2). On E_tau every nonconstant Fourier coefficient of the normalized overlap function is at most tau in magnitude. No independence or convexity is needed for this statement.

For any nonnegative random quantity Z, E[Z|E_tau]<=E Z/P(E_tau). Consequently a separately proved annealed hole or incidence upper bound for this SAME lattice law survives this conditioning up to1+o(1). No assertion is made that the source horizontal-hole theorem has already supplied such a bound for this particular finite ensemble.

Small Fourier coefficients alone do not bound maximum multiplicity. In particular this is not a substitute for the high-order incidence calculation below or for its missing higher-dimensional version.

## 2. Exact high-order progression count in a convex box

Return to S={1,...,l}^n with l<p/4 and mu=l^n p^(r-n). For an integer k>=2, count ordered nonconstant arithmetic progressions

 z,z+v,...,z+(k-1)v in S,

where addition is in F_p^n and v!=0. There is NO modular wrap ambiguity. In each coordinate, differences of two consecutive representatives lie in[-(l-1),l-1]. All these differences are congruent modulo p; since2(l-1)<p they are identical as integers. Thus any such progression is an actual integer progression inside the box. Conversely every integer progression is a modular one. In particular its k entries are distinct.

Let t=k-1 and

 B_k=l+2 sum_(h=1)^floor((l-1)/t) (l-t h).

The exact number of ordered progressions is B_k^n-l^n: independently choose each coordinate's integer step h, then l-t|h| starting positions. The subtraction removes the globally constant progression v=0. Since the function(l-t x)_+ is decreasing for x>=0,

 sum_(h>=1)(l-t h)_+ <= integral_0^infinity(l-t x)_+ dx=l^2/(2t),

so B_k<=l+l^2/t.

For a fixed nonconstant progression, simultaneous inclusion in the random affine flat X+U is exactly the rank-one event

 p^(r-n)(p^r-1)/(p^n-1)<=2p^(2(r-n)).

Hence if A_k is its random count inside S intersect(X+U),

 E A_k <=2mu^2(1/(k-1)+1/l)^n.

This bound retains the full dependence of all k sites; no independent-site estimate has been used. For k=floor(l/2)+1 and l>=4, k-1>=l/4, giving

 P(A_k>0)<=E A_k<=2mu^2(5/l)^n.

In the current scale l~n/R and mu=Theta_R(n log n), the right side is exp(-n log n+O_R(n)). It survives the body-dependent exclusion E_tau from section1 by division by P(E_tau)=1-o(1).

Thus a specific family of arbitrarily high-order dependent incidences DOES have the superexponential bound needed by completion, with a direct convex-box calculation. The earlier statement that all dependent tuples are necessarily uncontrolled would be too strong: long consecutive collinear clusters are now controlled.

## 3. Why this does not yet bound high load

A set of H~n log n points in an affine flat can be distributed among many short line segments; high cardinality does not by itself imply a progression of length comparable to l. Convexity of the AMBIENT box does not say that its intersection with a finite-field affine flat is convex in integer coordinates, because the flat has modular identifications. The missing statement is a structural alternative: either high load produces one of a quantitatively summable set of convex-section incidence configurations, or it produces another body-dependent spectral alignment that can be excluded at small cost. No such alternative is proved here. In particular this note does not extend the cube-specific count to arbitrary convex K or complete the full frozen target.

No additional primary theorem or body read is claimed. Existing source and primary identities/reading ranges remain in their receipts. These calculations are finite-group and integer-counting deductions.

## 4. Higher-rank filled boxes: an additional summable incidence class

Fix d>=2 independently of n, and let2<=k<p. Consider ordered affine boxes

 {z+j_1 v_1+...+j_d v_d: 0<=j_i<k}

with v_1,...,v_d linearly independent over F_p, all lying in S. They have k^d distinct entries. The same no-wrap argument applies to every adjacent edge: the unique integer representative of each coordinate difference is independent of the base point. Thus every coordinate of the integer lift is an affine function of(j_1,...,j_d). Writing t=k-1, its total oscillation is t sum_i |v_i|<=l-1.

For an upper bound, each integer step has at most2l/t+1 possible values, and the starting coordinate at most l choices. Therefore the number of ordered boxes is at most

 [l(2l/t+1)^d]^n.

Discarding linearly dependent generator choices only lowers this bound. Each remaining box has affine rank d and inclusion probability

 p^(r-n) product_(i=0)^(d-1)(p^r-p^i)/(p^n-p^i)
 <=2p^((d+1)(r-n))

for all sufficiently large n (d fixed). The expected number of these filled boxes inside S intersect(X+U) is consequently at most

 2mu^(d+1)(2/t+1/l)^(dn).

For d=2, choose k=ceil(sqrt(H)) with H=Cmu and fixed C>0. Then k^2>=H, k=o(l), and the bound is

 exp(-n log H+O_(C,R)(n))
 =exp(-n log n-n log log n+O_(C,R)(n)).

Again conditioning on E_tau only divides by1-o(1). Thus filled rank-two grids of high-load size, as well as long rank-one progressions, are controlled at a sufficient scale. This does not count arbitrary rank-two affine-flat intersections: they need not contain a filled box of comparable cardinality. More generally, cardinality alone does not guarantee one of the structured configurations counted here. An inverse theorem with quantitative losses small enough for the displayed exponent remains unpaid; no such theorem is imported or assumed.

## 5. A precise obstruction to a cardinality-only inverse step

The missing structural alternative cannot simply assert that a high-load CONVEX lattice section contains a long arithmetic progression or a large filled grid. Here is an exact counterexample at the target density scale.

Let rho=n log n, a=rho^(1/n), Gamma=Z^n and K=[0,a]^n. For all sufficiently large n,1<a<2. The normalized volume is exactly rho and K+Gamma already covers all space. Every translate of K meets Gamma in a subset of a product of n two-element sets of consecutive integers. Hence NO such section contains a nonconstant three-term arithmetic progression: one coordinate of its nonzero step would require three distinct integer values in an interval of length a<2. It consequently contains no filled k-by-k grid with k>=3.

Nevertheless, on the open coarse-torus box (0,a-1)^n the overlap count is2^n, exceeding every fixed C rho for large n. Its measure is (a-1)^n=exp(-n log n+n log log n+O(n)). This is a lower bound for high-overlap volume, not an equality; other translates also have high overlap. Thus even exact coverage, the target-order mean, convexity, and complete absence of all the long progression/grid configurations counted above do NOT bound maximum multiplicity.

This example is not claimed to belong to the body-spectral-conditioned Construction-A law. It prevents a geometry-only inference from the positive incidence estimates. A successful inverse alternative must include a different branch, such as an appropriate body-dependent spectral alignment or a configuration with many short binary directions. The cube itself has an obvious tiling lattice; the full existential target is not refuted.
