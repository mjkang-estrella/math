# W031 continuation review: normalized public-prime screen

Disposition: **accept the extraction and restricted coverage argument, subject to the qualifications below; revise the stated 37-cofactor example and keep raw-jet acquisition distinct from the cost of its normalization.** Verified complete factoring improvement: **NONE**. This is a symbolic review; no numerical factoring run, solver change, or Lean claim is supplied.

The audited continuation is the frozen 129-line `W031-higher-precision-prime-screen.md`, SHA-256 `dc166685395850db6bfe421202181497895bd1dcfe930cf4f3f4f4e9018872f4`. The complete brief, governing documents, accepted comparator inputs, source evidence, and precise read scope are in `W031-normalized-prime-screen-review-evidence/`. The parent remains principal researcher.

The original matrix identity, coefficient identity, and raw semiprime onset are **provisional imported interfaces**, owned by the separate `factoring-w031-reversed-jet-review-r1` task. I did not reread or re-audit W031.md B/C/D or that task's report. W031 A's chart count is excluded. Everything below relating the original circuit to A_j is conditional on the imported identity. The coefficient-screen counting argument itself follows directly from the displayed definition of A_j.

## Exact extraction: the exponents are correct

Write b=bitlen(N), n=(N-1)/2, U=(-4)^n, and

    D_j = 4^j (2j+1)!,
    E_j(Y) = product_(i=1..j) ((2i-1)^2-Y),
    A_j(Y) = E_j(Y)/D_j = sum_(h=0..j) c_(j,h)Y^h.

Assume N odd, 0<=j<=n, 0<=r<=j, and gcd(D_j,N)=1. The condition 2j+1<leastprime(N) suffices, but is an analysis of the checked-unit branch, not factor advice available to the algorithm.

Import a_j=N U A_j(N^2). Let a_bar be its canonical residue modulo N^(2r+2). Since D_j is a unit modulo N and a_j is an integer, N divides a_j, hence N divides a_bar. Therefore

    a_bar/N = U A_j(N^2)  (mod N^(2r+1)).

Multiplication by U^(-1) in this quotient ring is legal because N is odd. With x its resulting residue, subtract the rational residues of the lower terms at the same precision:

    s = sum_(h<r) c_(j,h) N^(2h)  (mod N^(2r+1)),
    delta = (x-s) mod N^(2r+1).

Then delta is an integer multiple of N^(2r), and

    delta/N^(2r) = c_(j,r)  (mod N).

Indeed, after division the next term has a factor N^2. Changing representatives before either exact division changes the quotient only by a multiple of its claimed modulus. There is no inverse of N and no off-by-one error. The modulus N^(2r+2) is a sufficient generic precision: exact division by N loses one N-adic digit, and the second division loses 2r more. This is not a minimum-information theorem for this particular public coefficient family, which can be generated directly.

**The necessary precision of a lower coefficient is material:** to extract depth r, c_(j,h) must be known modulo N^(2(r-h)+1), for each h<r. Knowing only the previously extracted residues modulo N does not supply those lifts. At r=1, replacing c_(j,0) by an arbitrary representative modulo N generally changes the remainder by a multiple of N rather than N^2, spoiling the second exact division. The continuation's instruction to acquire and charge lower coefficients is correct; it must retain this precision requirement.

For c=u/v in lowest terms with gcd(v,N)=1, its computed residue is u v^(-1) modulo N, so gcd(N,residue)=gcd(N,u). Reduction to lowest terms is a mathematical description of the screen, not a required expensive integer computation in the modular implementation.

## The 37 example needs one qualification

The displayed expansion and rational reduction are correct:

    E_3(Y)=225-259Y+35Y^2-Y^3,
    c_(3,1)=-259/322560=-37/46080,
    c_(3,0)=5/7168.

Thus the **direct** rational coefficient test returns 37 for N=37q, q>1, gcd(q,2*3*5*37)=1. But the preceding **staged matrix extraction** additionally needs the denominator of c_(3,0) to be a unit; 7168=7*1024. Its unreduced D_3 also contains 7. The stated cofactor condition permits q=7, where that extraction cannot be performed as written.

This is an exact symbolic counterexample to the extraction's claimed example range. For N=7*37, each factor 1-N^2, 9-N^2, 25-N^2 is nonzero modulo 7, and v_7(D_3)=1. The imported identity gives v_7(a_3)=v_7(N)-v_7(D_3)=0. The initial division of a_3's residue by N is therefore not exact. A checked-denominator exit instead finds 7. There is no contradiction with the correct direct gcd(N,37) test.

A sufficient repair for the staged example is q>1 and gcd(q,2*3*5*7*37)=1. The continuation's specific q=41 example already satisfies it, with j=3 below the imported raw onset 18. If the comparison is specifically to a squarefree semiprime with least factor 37, state that q is a prime greater than 37. No hidden-factor oracle is involved: 37 is explicitly exposed by the public coefficient, and direct gcd(N,37) is cheaper than recovering it via matrix arithmetic.

## Executability and complete operand costs

Unknown least factors need not be supplied. An elementary legal preprocessing branch tests gcd(t,N) for 2<=t<=min(2K+1,floor(sqrt(N))). For a promised composite N each tested t<N, so a nontrivial gcd is proper. If this finishes without a factor, all relevant D_j are units. If the upper endpoint was floor(sqrt(N)), no-factor completion contradicts the composite promise. This takes O(K) gcds on O(b)-bit operands; the already accepted small-factor block-product interface can instead implement the factor-or-unit-certification step in soft O(sqrt(K)*poly(b)). Neither method constructs the enormous integer factorial or receives a least-prime bound as advice. Even inputs exit immediately. No squarefree assumption is needed for the unit-branch arithmetic.

A failed denominator inversion must return a proper gcd or localize a full gcd N among its known small factors. A full gcd is not itself a factor. Using the integer precheck just described supplies this localization and avoids silently cancelling nonunits.

For the literal dense matrix acquisition, put Q=N^(2R+2) and B=bitlen(Q)=Theta((R+1)b). The claimed truncation z^(2K+3) is sufficient: the imported trace formula requires the coefficient of z^(2j+1); even z^(2K+2) would suffice. Keeping one extra coefficient is harmless. Matrix multiplication uses polynomial multiplication and addition over Z/QZ, with O(log N) powering stages. Fast integer-convolution arithmetic gives soft O((K+1)(B+log(K+1))*b) bit work for this acquisition, including convolution temporary widths. Since K<=n, this is soft O((K+1)(R+1)*poly(b)). It requires Theta((K+1)(R+1)b) bits for the explicitly stored full-width dense raw jet, up to constants and workspace factors. Precision is not a unit-cost scalar.

Building Q and its powers, obtaining the unit inverse of -4, binary powering to U^(-1), normalizing the K+1 raw coefficients, and dividing the residues all involve at most O((R+1)b)-bit operands. They fit the raw-jet scale with fast arithmetic. Each final gcd uses O(b)-bit residues. Rational lower-term acquisition and assembly are an additional obligation; they are not proved to fit that scale merely by the matrix-power argument.

For example, generating every lower c_(j,h) by the recurrence below modulo N^(2R+1), at full precision, costs soft O((K+1)(R+1)^2*poly(b)). Shared partial sums of c_(j,h)N^(2h) and streamed exact divisions stay within that conservative bound; independently recomputing each lower-term sum would be wasteful. Explicitly materializing all lower lifts at their necessary precisions also has an extra factor of order R in its precision volume when R grows. This is an available upper bound, **not** a lower bound on all implementations. Lines 51-57 correctly price the raw dense matrix operations; they should not be promoted to a proved end-to-end bound for literal staged extraction without an additional normalization algorithm or accounting argument.

There is, however, a simple fully paid generator for the **same separate-gcd screen** at the stated soft-linear index-volume scale. Put s_j=(2j-1)^2 and d_j=4(2j)(2j+1). The defining product directly yields

    c_(0,0)=1,
    c_(j,r) = (s_j*c_(j-1,r)-c_(j-1,r-1))/d_j,

with unavailable indices zero. On the checked-unit branch, reduce this recurrence modulo N and invert d_j once per row. Update r in descending order to stream a row of R+1 residues. Truncation at R loses no lower-degree coefficients. There are O((K+1)(R+1)) modular operations and gcd tests, O(K) unit inversions, and only O(b)-bit operands because j<=n. Thus total bit cost is soft O((K+1)(R+1)*poly(b)), including setup and factor validation; streaming working storage is O((R+1)b), or O((K+1)(R+1)b) if all residues are retained. The exact rational numerators need never be expanded or factored. This recurrence is a concrete cost completion for the public screen, not an implementation of the staged N-adic extraction and not an escape from its prime-coverage bound. No claim that it is the fastest generator is made.

## Coverage proof and the two-prime obstruction

Use natural logarithms here; changing the log base changes only a constant. Let u_(j,r) be the reduced integer numerator of c_(j,r), for the prescribed triangular index set 0<=j<=K, 0<=r<=min(j,R), K>=1, 0<=R<=K. Write s_i=(2i-1)^2>0. The unreduced coefficient is (-1)^r e_(j-r)(s_1,...,s_j), a nonzero integer. Hence no u_(j,r) is zero, including u_(0,0)=1. Moreover

    |u_(j,r)| <= e_(j-r)(s_1,...,s_j)
               <= product_(i=1..j)(1+s_i)
               <= (1+4j^2)^j.

Rational reduction cannot increase the numerator magnitude. For the total log height H=sum_(j,r) ln|u_(j,r)| this gives the explicit bound

    H <= (R+1)*K*(K+1)/2 * ln(1+4K^2)
      = O((R+1)*K^2*ln(K+1)).

Let U be the union of prime divisors of these numerators, restricted to (P,2P]. The product of the distinct primes in U divides the product of the absolute numerators, so

    |U| <= H/ln P.

No factorization of the numerators is being supplied as algorithmic advice: U is a proof device. If P>2K+1, the denominator exits contain no prime in this interval.

The narrowly checked primary source is Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), printed page 69, Corollary 3, equation (3.8):

    M(P):=pi(2P)-pi(P) > 3P/(5 ln P),  for P>=20.5.

See the [primary paper scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf) and [publisher record](https://doi.org/10.1215/ijm/1255631807). The scan and a visually checked image of page 69 are frozen. No broader prior-art survey or new prime-count theorem is claimed.

Covering every prime in that interval therefore requires H>3P/5 and consequently (R+1)K^2 ln(K+1)=Omega(P). A universal **semiprime splitting** guarantee need not cover literally every prime: it must at least avoid leaving two outside. Its necessary condition is |U|>=M(P)-1, hence H>3P/5-ln P, which yields the same asymptotic bound. These are necessary conditions only; coverage does not ensure that a tested numerator separates two covered primes rather than vanishing at both.

Here is the exact missed-input statement. Fix uniform caps K(P),R(P) applying to every allowed branch of the screen on every N in [P^2,4P^2]. Suppose P>2K(P)+1 and

    H/ln P < M(P)-1.

Then choose two distinct primes p,q in (P,2P] outside U. Their product N=pq lies in [P^2,4P^2]. Every denominator is a unit and every separate numerator gcd equals 1. Thus this screen fails to split that N. For an asymptotic counterfamily it suffices that (R+1)K^2 ln(K+1)=o(P) along unbounded ranges. There are then many uncovered primes, not just an unproved single exception. The proof does not require the public algorithm to know p or q. Adaptive or randomized choice within the same capped index set cannot enlarge U; the statement does not apply if other gcd expressions, larger indices, or unrestricted consumers are allowed.

For fixed R, necessity gives K=Omega(sqrt(P/ln P)) when P>2K+1; this implies the continuation's weaker square-root-up-to-logs phrasing. For V=(K+1)(R+1),

    (R+1)K^2 <= V^2,

so universal coverage or universal success of this separate-gcd screen requires V=Omega(sqrt(P/ln P)). This is a capacity requirement on these parameters. It becomes a work/storage comparison only for the explicitly dense full-width matrix representation that really materializes Theta(Vb) bits. It does not prove a runtime lower bound for every generator, sparse representation, or implicit consumer. Within that literal dense route, it precludes a fixed-power improvement over the accepted soft sqrt(P) small-factor product scale. It does not prove factoring hard or establish a general factoring lower bound.

## Random evaluation and the scope of a possible escape

A new input-dependent combination or evaluation point changes the tested integers, so it is outside the preceding finite-union theorem. The report is right to exclude even arbitrary new fixed combinations unless they are separately incorporated and bounded. The direct recurrence above stays entirely inside the theorem.

For a polynomial whose reduction f_p is nonzero and of degree at most d, a fresh uniform x in F_p satisfies Pr[f_p(x)=0]<=min(1,d/p). This elementary field-root bound is valid conditionally on the chosen polynomial when the fresh point remains uniform. Uniform sampling from Z/NZ has uniform projection to F_p. Sampling only units instead gives the corresponding bound d/(p-1); sampling from 1,...,N-1 also needs its small distribution correction. An input-dependent or adaptively conditioned point is not automatically uniform.

If the polynomial is identically zero modulo p, check its cleared, legally scaled coefficient content: gcd(N,b_0,...,b_d) returns a proper factor when all coefficients vanish at one semiprime component and not the other. If they vanish at both, that gcd is N, not a split; any division or higher-precision regularization is a new paid operation. For A_j itself on the unit branch the leading coefficient is (-1)^j/D_j, a unit, so this degeneracy does not occur. For squarefree N=pq with both component polynomials nonzero, the probability of a proper split from a uniform evaluation is at most d/p+d/q by a union bound; a simultaneous zero gives gcd N. This remains only an upper bound for that experiment, not an impossibility theorem for selectors or compact high-degree circuits.

The continuation supplies no improved nonuniform point selector or complete factoring success law. The concrete next obligation for such an escape is an executable N-only rule producing different tested integers, with charged construction and a proved separating probability or deterministic cover. Repeating favorable primes in the fixed coefficient table cannot discharge it.

## Acceptance record

Accept provisionally: exact N-adic precision and legal divisions with sufficiently lifted lower coefficients; the corrected degree-three demonstration; the raw dense matrix cost at its stated scope; the public-coefficient interpretation; and the height, dyadic-prime capacity, and uniformly capped two-prime failure proofs. The direct recurrence supplies an independent complete cost bound for the same screen.

Required wording repairs: add the missing 7-unit condition to the staged 37 example, and explicitly label the displayed matrix cost as raw acquisition unless normalization is separately costed. State lower-coefficient lift precision, proper/full denominator-gcd handling, and the two-outside-prime condition if turning coverage into a semiprime claim. None changes the accepted restricted asymptotic obstruction. Final acceptance of the connection to J_N remains with the parent after the separate original-identity audit.

No recursive delegation, installations, commits, shared solver/Lean edits, STATE writes, or task-file edits were performed. No benchmark or factoring experiment was run. Evidence validation consists of symbolic arguments, inspection of one primary-source page, input snapshot/hash checks, and delivery-manifest verification. A hash manifest authenticates the delivered bytes relative to its terminal anchor; it does not formally verify the mathematics.
