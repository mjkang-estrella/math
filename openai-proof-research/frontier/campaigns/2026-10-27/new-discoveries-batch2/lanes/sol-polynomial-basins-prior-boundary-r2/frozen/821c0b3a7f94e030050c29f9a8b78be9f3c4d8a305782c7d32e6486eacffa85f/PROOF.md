# A universal obstruction to Borisov Question 10

Status: ordinary proof proposed for root's independent review, not accepted, counted, formalized, or literature-cleared. Source: Alexander Borisov, *Iterations of Integer Polynomial Maps Modulo Primes*, JIS16 (2013), Article13.8.3, Question10, printed p4. Received May4, revised Aug4/Sept1, published Oct12 2013. Exact frozen original and text bindings are in source-bindings.json; live original retrieved Oct30 2026.

## Precise result

There is no integer-polynomial self-map F of any finite-dimensional affine space such that, for every prime p, all points whose initial first coordinate is zero eventually reach a fixed point A_p and all points whose initial first coordinate is nonzero eventually reach a different fixed point B_p. This remains impossible if finitely many primes are excepted, and even if the two fixed points may depend arbitrarily on p. Thus the obstruction covers the requested two fixed points distinct modulo every prime, including2. It does not concern a weaker reading permitting both initial classes to reach the same point.

The source says “two different fixed points ... modulo every prime ... any initial point ... depending on whether or not the initial first coordinate is zero”. It puts no dimension bound, dominance requirement, common iteration time across primes, or prescribed choice of zero/nonzero branch. Over a fixed finite field, point-dependent absorption times can be replaced by their finite maximum. Swapping A_p and B_p has no effect on this proof.

## Lemma 1 (elementary Schur argument)

For any nonconstant f in Z[t], infinitely many primes divide a nonzero value f(m), m an integer. Suppose instead these primes form a finite set S. Choose t0 with A=f(t0) nonzero and let M be the product of primes in S (empty product1). The polynomial g(t)=f(t0+A M t)/A has integer coefficients, constant term1, and all its other coefficients divisible by M. It is nonconstant, so some integer t satisfies |g(t)|>1. A prime divisor r of g(t) cannot divide M, since g(t)=1 modulo every prime dividing M. But r divides the nonzero integer f(t0+A M t), contradicting the definition of S. In particular, roots of f modulo primes occur outside any prescribed finite exceptional set.

## Lemma 2 (uniform preservation of the coordinate hyperplane)

Let P in Z[x,y1,...,ym] satisfy, outside a finite set E of primes,

    P(a,b)=0 in F_p if and only if a=0,

for all a,b over F_p. Then P=c x^k for a nonzero integer c and k>=1. All prime divisors of c belong to E.

For each integer tuple b, P(0,b) is divisible by infinitely many primes and hence zero. A polynomial over Q vanishing on the integer lattice is zero (induct on variables using the univariate root bound). Thus x divides P. P is not zero, since its value at x=1 must be nonzero modulo every prime outside E. Write P=x^k H, k>=1 maximal; thus H(0,y) is a nonzero polynomial.

If H depends on some y_i, its leading coefficient in y_i is a nonzero polynomial in x and the remaining y variables. Choose integer values for these variables with x=a!=0 and that leading coefficient nonzero. Such values exist by the same integer-lattice argument, also after excluding x=0. The resulting polynomial f(y_i) is nonconstant. Lemma1 supplies a prime outside E and outside the prime divisors of a, and an integer y_i with f(y_i)=0 modulo that prime. This gives a forbidden zero of P with x nonzero. Consequently H=h(x) is univariate. If h were nonconstant, maximality of k gives h(0)!=0. Lemma1 supplies a prime outside E and outside the divisors of h(0), at which h has a root; that root is nonzero. Again this contradicts the hypothesis on P. Therefore H=c is a nonzero constant. If a prime p outside E divided c, P(1,0)=0 modulo p, also impossible.

## Lemma 3 (a suitable prime)

For every integer k>=1 and finite set E, there are an odd prime q not dividing k and a prime p outside E with q dividing p-1. Choose any odd prime q not dividing k and put N=q times the product of primes in E. The positive integer S=1+N+...+N^(q-1)>1 has a prime divisor p. Since S=1 modulo each prime dividing N, p is neither q nor a member of E. Modulo p, N^q=1. If N=1 modulo p then S=q modulo p, forcing p=q, impossible. Thus N has multiplicative order q modulo p; Lagrange's theorem gives q dividing p-1. The only standard group fact additionally needed below is that F_p^* is cyclic, or equivalently Cauchy's theorem supplies an element of order q.

## Proof of the obstruction

Suppose F exists and let P be its first coordinate. Membership in the basin of a fixed point is unchanged by applying F once. Since A_p and B_p are distinct, the stipulated basin partition therefore forces

    P(x,y)=0 iff x=0

at every allowed prime. (Otherwise the same orbit would eventually equal both distinct fixed points.) Lemma2 yields P=c x^k. Include prime divisors of c in E and choose q,p by Lemma3. Choose z in F_p^* of order q and any two initial points having first coordinates1 and z; their other coordinates may both be zero. At time t their first coordinates u_t,v_t remain nonzero and satisfy

    v_t/u_t = z^(k^t).

This follows by induction from u_(t+1)=c u_t^k and v_(t+1)=c v_t^k. Since q does not divide k, this ratio never equals1. But both starting points have nonzero first coordinate, so both must eventually equal B_p. At a time after both absorption times, their first coordinates agree, a contradiction. This completes the proof in every finite dimension.

## Comparison and limitations

The actual two-page precursor *Some Interesting Integer Polynomial Maps*, arXiv:1301.0517v1, already states the same unnumbered question on p2, Jan3 2013. Thus Oct12 is the journal publication date, not the question's first public date. Its proof bodies are the same additive/multiplicative/power trap mechanisms. Actual later *Geometrically Nilpotent Subvarieties*, arXiv:1505.03237v1, May13 2015, Theorems5/7/9 use homogeneous traps contracting subvarieties to one point; their proofs allow geometric points over extensions. Its Q12 asks about several image fixed points for a geometrically irreducible subvariety, without prescribing our coordinate basin partition. The obstruction here does not resolve that separate question. Both bodies were frozen/read, not inferred from abstracts.

Borisov Theorem2's actual proof uses v/u=y/x+1 for the additive trap (x²y,x²y+xy²), and then collapses both coordinates to zero when the translated ratio reaches zero. Its first output x²y vanishes also at x!=0,y=0; it violates exactly the necessary hyperplane preservation in Lemma2. Adding coordinates cannot repair this failure while keeping the literal basin partition. Theorems4 and6 have multiplicative/order restrictions and the same coordinate-collapse issue; their proofs do not supply a two-basin map. Theorem8 takes direct products and intersects nilpotency loci, with no branch-preserving assertion.

This is an obstruction mechanism, not finite-prime interpolation and not merely failure of one proposed construction. Lemma2 and the ratio-cycle argument are complementary parts of a single family, with no extra credit. A direct indicator polynomial uniform over all primes also fails: a polynomial equal0 on x=0 and1 on all x!=0 would have to be identically1 by evaluating integer nonzero x and using infinitely many primes, contradicting its value at0. The two mechanisms therefore close the branch-preserving polynomial and indicator approaches; no construction is claimed.

Priority and eligibility remain bounded: actual source proof bodies were compared; existing lane/report aliases and live lawful title/registry access are recorded separately. No inaccessible historical interval is deemed cleared. Root must adversarially check the reduction from the exact question to the two distinct basins and the elementary polynomial-specialization argument before any further work. No Lean or manuscript work was performed.
