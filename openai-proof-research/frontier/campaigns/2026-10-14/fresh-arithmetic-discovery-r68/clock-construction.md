# Exact augmented construction; original full operation not solved

This is an exploratory supporting deduction, not a candidate or a full-preservation theorem. Classical unary reduction, control layers, Sidon difference coding, prime cyclic quotients, and classical interval closure must receive credit. No claim that this construction is new to the literature.

Let A be a nonempty finite set and f_1,...,f_t total selfmaps. Write L=Con(A;f_1,...,f_t), choose a0 in A, and put n=|A|. We construct two maps c,e with Con(c,e) exactly L with one new greatest element. The first map is a permutation of prime order, the second idempotent. This does NOT solve the original full-L operation.

Choose s=1+t+2(n-1). Take R={0,1,3,...,3^(s-2)} when s>=2, and R={0} when s=1. Choose a prime p>2 max(R) with p>=2. Ordered nonzero differences of R are distinct modulo p. Indeed positive integer differences between nonzero powers of3 have a unique 3-adic valuation and residual factor 3^k-1; differences from0 have residual factor1, so cannot coincide with those. Equality of positive and negative differences modulo p is excluded by p>2 max(R).

Assign slot0 the map g_0=id_A, t distinct remaining slots the operations f_i, and two remaining slots for each a!=a0 the constant map with value a. All slots outside R carry the constant map with value a0. Define X=A x Z_p,

c(a,i)=(a,i+1),        e(a,i)=(g_i(a),0).

Then c has order p and e^2=e. Let eta be equality of the layer index.

## Congruences below eta
For each theta in L, theta^# relates (a,i),(b,j) exactly when i=j and a theta b. This is a congruence: c shifts layers; e preserves the original operations, identity, and constants. Conversely, if alpha is a congruence contained in eta, c and its positive-word inverse c^(p-1) force identical equivalence relations theta on every layer. Applying e to layer i shows theta is g_i-invariant and hence f_i-invariant. Thus [0,eta] is exactly the lifted copy of L.

## Every cross-layer identification forces top
Suppose (x,i) alpha (y,j), with d=j-i nonzero modulo p. By powers of c, for every k,

(x,k) alpha (y,k+d).

For any fixed a!=a0 there are two distinct slots k carrying the constant a. At most one of these has k+d in R: otherwise two ordered differences of R equal d. Select the other slot. Applying e yields (a,0) alpha (a0,0), independently of x,y. Thus the whole base layer is one alpha-class; rotation gives eta<=alpha. This also holds when n=1, because eta is then equality.

On X/eta, c is the prime p-cycle and e is constant. A c-invariant equivalence relation on Z_p is a block system for the regular cyclic group; its classes are cosets of a subgroup. A nonzero identified difference generates Z_p, so alpha/eta is universal. Therefore alpha=1_X.

All congruences are now classified: {theta^#:theta in L} together with the new top 1_X. eta is strictly below top since p>=2. The construction is effective (prime search terminates) but no optimized size bound is claimed.

## Consequence at the stipulated source interface
Let L^+ denote the order table of L with one new top. The following equivalence holds:

L has a finite-algebra representation iff L^+ is the full congruence lattice of some finite two-unary algebra whose first operation is a prime-order permutation and whose second is idempotent.

Forward: classical basic-translation reduction, then the construction above. Reverse: any such algebra is a finite algebra, and L is an interval in L^+; finite representability is closed under intervals by the Kurzweil–Netter duality theorem and quotient construction, as actually proved in DeMeo2012 pp10–13. Thus source206 m:main(ii) transfers undecidability to that restricted two-unary recognition problem. The input transformation adds one row/column to a finite lattice order table; it does not compute source206's unresolved one-lattice-per-circuit map MRC.

This consequence is not nominated. It is a signature/control-layer transfer with a short finite compatibility argument, and may be technical or already classical. A proof of this consequence is not evidence of substantiality.

## Two precise failures for the original full operation
1. With disjoint layers, a rotation c and any decoder e that sends every layer to the base always preserve eta. If all original congruences are lifted faithfully below eta, the additional universal congruence gives at least |L|+1 congruences. Sidon guards remove other unwanted congruences but cannot remove this eta/top distinction.
2. Glue copies at one common point a, and let the rotation permute copies fixing that point. If e on copy i simulates f_i and e on the base is identity, well-definedness at the common point forces f_i(a)=a for every i. The unary polynomial closure contains constant maps to every element; for |A|>1 these have no common fixed point. Thus this particular overlapping-copy repair is unavailable for the full class. This does not prove that every two-unary full-preservation construction is impossible.
