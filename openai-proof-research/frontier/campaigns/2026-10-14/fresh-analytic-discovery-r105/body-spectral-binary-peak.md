# A binary peak invisible to large-coefficient body-spectral exclusion

Author proof, not an independent gate. The unchanged full arbitrary-convex-body single-lattice existence target remains open. This gives a precise counterexample to a deterministic structural implication proposed during this attempt. It does NOT estimate the probability of the counterexample in the fixed prime-field random-r-subspace ensemble.

## Statement and scope

There are convex parallelotopes K, genuine lattices Lambda containing Z^n, and arbitrarily fine finite-quotient realizations U of Lambda, with:

* mean overlap mu asymptotic to n log n;
* exact coverage K+Lambda=R^n and essential peak2^n;
* every nonconstant normalized body Fourier coefficient on U^perp below mu^(-1/4), so E_tau from the preceding note holds;
* high-overlap volume at least (1/2)(a-1)^n, where a=(n log n)^(1/n).

The last quantity is exp(-n log n+n log log n+O(n)), larger than exp(-n log n-An) for every fixed A and all sufficiently large n. Thus E_tau alone does not even imply the outer bad-volume bound used in two-sided completion. The counterexample consists entirely of short binary directions, not long progressions. It is valid for general finite abelian quotients of a lattice; the quotient modulus below is highly refinable and is NOT asserted prime or of size comparable to n.

## 1. Physical lattice and geometric promises

Fix an integer R>=6. Let P be the cyclic coordinate-permutation matrix and B=R I-P. Set D=det B=R^n-1, Lambda=B^(-1)Z^n, rho=n log n, a=rho^(1/n), and K=B^(-1)[0,a]^n. For sufficiently large n,1<a<2.

B is an invertible integer matrix, so Lambda contains Z^n, has determinant1/D, and its quotient modulo Z^n has D elements. The inverse B^(-1)=sum_(j>=0)R^(-j-1)P^j has nonnegative entries and every row sum1/(R-1). Therefore K is contained in [0,b]^n with b=a/(R-1)<1/2. Its volume is a^n/D and its normalized lattice density exactly rho.

For the centered version of K, coarse Z^n packing holds: for every nonzero integer z,

 ||Bz||_infinity >=(R-1)||z||_infinity >=R-1>a.

Rounding an arbitrary point to the nearest integer vector gives coarse covering dilation at most(R+1)/a. The packing supremum is at least(R-1)/a, so their ratio is at most(R+1)/(R-1). Similarly the fine grid Q^(-1)Z^n covers sK for s=(R+1)/(aQ), with the harmless centering translation understood. These estimates are explicit and do not use a Euclidean-roundness assumption.

In Lambda coordinates K is simply [0,a]^n, so it covers exactly and has peak2^n. The peak occurs on a nonempty open set; on the Lambda torus its measure is exactly(a-1)^n. Its coarse-torus measure is the same because multiplicity is Lambda-periodic. Every section K intersect(x+Lambda) has at most two values in each Lambda coordinate. It contains no nonconstant three-term integer arithmetic progression.

## 2. All physical dual coefficients are small

The physical dual lattice is Lambda^*=B^T Z^n. For xi=B^T m, m in Z^n, the normalized Fourier transform of K is a product of the one-dimensional normalized interval transforms at integers m_j. If m_j!=0,

 |(1/a) integral_0^a exp(2 pi i m_j t)dt|
 = |(1/a) integral_0^(a-1) exp(2 pi i m_j t)dt|
 <=(a-1)/a.

All other factors have modulus at most1. Therefore every nonzero xi in Lambda^* satisfies

 |hat(1_K)(xi)|/vol K <=(a-1)/a=O(log n/n).

This is much smaller than rho^(-1/4). Yet the peak is2^n. This already disproves the naked continuous-frequency implication; the next section makes the same exclusion exact in a finite quotient.

## 3. Exact finite-quotient realization and uniform spectral passage

Take Q through positive multiples of D. Then Q Lambda is contained in Z^n. Define

 U=Q Lambda mod Q Z^n subset (Z/QZ)^n,
 S_Q={z mod Q: z/Q in K}.

Since K is contained in [0,b]^n with b<1/2, its representatives are unambiguous. U is a subgroup of size D and corresponds exactly to Lambda; no independent coset list is used. Its annihilator consists of integer frequencies xi in Lambda^*, modulo QZ^n. This follows directly from exp(2 pi i xi.lambda)=1 for all lambda in Lambda. Also QZ^n is contained in Lambda^*, so every representative of a character in U^perp remains a physical dual vector.

Write

 c_Q(xi)=|S_Q|^(-1) sum_(z in S_Q) exp(2 pi i xi.z/Q),
 mu_Q=|S_Q|D/Q^n.

Riemann convergence gives mu_Q->rho and, for every fixed frequency, c_Q(xi)->hat(1_K)(-xi)/vol K. To make this uniform over ALL quotient frequencies, use a separate discrete boundary estimate rather than an unjustified finite-frequency limit.

Along each coordinate fiber, S_Q is an integer interval, by convexity. Translating by one unit changes at most two endpoints per nonempty fiber. Thus

 |S_Q symmetric-difference (S_Q+e_j)|<=2(Q+1)^(n-1).

For all sufficiently large Q, |S_Q|>=(vol K)Q^n/2. Consequently the ratio of this symmetric difference to |S_Q| is at most C_n/Q, for example C_n=2^(n+1)/vol K. Fourier differencing gives

 |1-exp(2 pi i xi_j/Q)| |c_Q(xi)|<=C_n/Q.

Choose representatives with |xi_j|<=Q/2. Since the left multiplier is at least4|xi_j|/Q,

 |c_Q(xi)|<=C_n/(4||xi||_infinity)  for xi!=0.

Let tau_n=rho^(-1/4). For large n, (a-1)/a<tau_n/8. Fix T> C_n/tau_n. Frequencies with norm>T have coefficient<tau_n/4, uniformly for all sufficiently large Q. There are finitely many integer frequencies of norm<=T; on the nonzero ones in Lambda^*, choose Q sufficiently large that the Riemann error is<tau_n/8. Their coefficients are then<tau_n/4 as well. Finally choose Q large enough that rho/2<mu_Q<2rho. It follows that ALL nonzero xi in U^perp satisfy

 |c_Q(xi)|<tau_n/4<mu_Q^(-1/4).

Hence the finite exclusion event E_tau holds exactly for this subgroup and this convex-body discretization. Q may be chosen arbitrarily large among the admissible multiples, making the fine covering radius arbitrarily small.

## 4. Finite high-load volume and why this matters

For uniform X in (Z/QZ)^n, |S_Q intersect(X+U)| counts the Lambda coset points in K at coarse translate X/Q. The peak set has boundary measure zero and coarse-torus measure(a-1)^n. Riemann sampling therefore makes its discrete proportion at least(1/2)(a-1)^n once Q is sufficiently large. On this set the count is exactly2^n. For any fixed C, this exceeds C mu_Q for large n.

Since a-1=(log rho)/n times(1+o(1)),

 log((a-1)^n)=-n log n+n log log n+O(n).

This proves the stated bad-volume lower bound simultaneously with E_tau. It shows that absence of large individual Fourier coefficients cannot serve as the missing binary-direction alternative. Many individually small dual coefficients can combine to produce a peak. Neither long-grid incidence exclusion nor E_tau alone identifies that combination.

The remaining probabilistic possibility is substantial: a specified prime-field rank-r law could make such coherent binary configurations sufficiently rare, even when E_tau holds. No probability bound for them is proved here. The counterexample also has an obvious alternative tiling lattice a Lambda, so it does not contradict the full existential thin-covering target. Source-paid completion, all earlier obstructions, and reading limits remain unchanged.
