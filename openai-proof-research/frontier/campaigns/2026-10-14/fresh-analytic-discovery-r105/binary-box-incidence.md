# Independent binary boxes have a summable incidence bound

Author proof within the unchanged full r105 target. This controls a genuine binary-direction configuration in the original prime-field ensemble; it does not assert that all high-load convex sections contain that configuration.

Use p=n, l~n/R, mu=l^n p^(r-n)=Theta_R(n log n), r~n log R/log n, and S={1,...,l}^n from the earlier notes. Let lambda=p^(r-n). For an integer d<=r, count ordered affine binary boxes

 {z+sum_(i=1)^d epsilon_i v_i: epsilon_i in{0,1}},

whose generators are linearly independent over F_p and whose2^d vertices all lie in S.

## 1. Exact convex coordinate constraint

Represent each vertex in [1,l]^n. For each edge in generator direction i, every coordinate difference lies in[-(l-1),l-1] and is congruent modulo p to the corresponding coordinate of v_i. Because2(l-1)<p, the integer difference is unique and hence independent of the other binary coordinates. Therefore every coordinate of every vertex has an ordinary integer affine lift

 z_j+sum_i epsilon_i h_ij.

All binary choices remain in[1,l] if and only if sum_i |h_ij|<=l-1 and z_j lies in an integer interval of length l-sum_i|h_ij|. This is the convex-section constraint that a crude independent-generator count loses.

For one coordinate the number of choices of the steps and the base is

 B_d=sum_(h in Z^d, ||h||_1<=l-1)(l-||h||_1)
 <=2^d sum_(a in Z_+^d, sum a<=l-1)(l-sum a)
 =2^d binom(l+d,d+1).

The equality follows by counting an additional nonnegative slack coordinate and summing the usual stars-and-bars identity; the sign bound overcounts zero steps harmlessly. Thus there are at most B_d^n ordered boxes before imposing generator independence. Dropping dependent ones only lowers this number.

## 2. Their true joint inclusion probability

Each retained box has affine rank d, regardless of its2^d vertices. Its probability of lying in the random affine flat X+U is exactly

 lambda product_(i=0)^(d-1)(p^r-p^i)/(p^n-p^i).

For d=O(log n) this is at most2 lambda^(d+1) for sufficiently large n: take out the powers of p, bound the numerator factors by1, and use product_(i<d)(1-p^(i-n))>=1/2. No site independence is used.

The expected number Z_d of these ordered boxes therefore satisfies

 E Z_d <=2mu^(d+1) [ (2^d/(d+1)!)(1+d/l)^(d+1) ]^n.

This remains an upper bound after conditioning on the body-spectral exclusion E_tau, up to division by P(E_tau). For tau=mu^(-1/4), that denominator is1-o(1), by the preceding Parseval union bound.

## 3. Quantitative scale relevant to high overlap

Fix C>0 and take d=ceil(log_2(Cmu)). Then2^d>=Cmu, d=O(log n)<r, and

 log E Z_d
 <=log2+(d+1)log mu
   +n[d log2-log((d+1)!)+(d+1)log(1+d/l)]
 =-(1/log2+o(1)) n log n log log n.

Here Stirling's elementary factorial bound is enough; the first term is O(log^2 n), and n(d+1)log(1+d/l)=O_R(log^2 n). In particular the bound is smaller than exp(-n log n-An) for every fixed A and sufficiently large n. Markov's inequality gives the same upper bound for the probability that even one such binary box occurs.

This directly controls the large binary grids that were absent from the long-progression estimate. It is not a Chernoff calculation, and it retains every generator dependency.

## 4. Exact remaining obligation

A section of cardinality Cmu need not be a filled binary box, and nothing here proves it contains a linearly independent binary box with comparable cardinality. The body-spectral counterexample in the other note shows that exclusion of one large coefficient is not by itself the missing deterministic alternative. One still needs a structural incidence decomposition of general high-load convex sections (with sufficiently small losses), or a different joint upper-tail/coverage argument. No such decomposition or full construction is claimed. This cube calculation is supporting research, not a restriction or replacement of the frozen arbitrary-body target.
