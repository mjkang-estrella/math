# W032 lift-control: independent symbolic review

**Disposition: accept the additional affine-lift identity and its scoped public-argument simulation, conditional on the imported scalar diagonal.** The larger inputs, exact normalization, tail truncation, canonical carries, and boundary R=2 are legal. No squarefree or field hypothesis is needed for the affine identity. The semiprime probability is correct. The cost claim uses the fast-arithmetic assumptions of the original construction and charges R, base acquisition, materialized inputs, and batch consumption separately.

**Verified complete factoring improvement: NONE.** This is a symbolic review, not a numerical experiment, formal verification, hardness theorem, or novelty claim. Other canonical-input selection remains open and was not reviewed here.

The reviewed parent is the [frozen lift note](W032-lift-control-review-evidence/inputs/research/findings/W032-lift-control.md), read with the [frozen original construction](W032-lift-control-review-evidence/inputs/research/hypotheses/W032.md). The [brief](W032-lift-control-review-evidence/brief.txt) and [input manifest](W032-lift-control-review-evidence/input-manifest.json) freeze the scope and source bytes. The live scalar/carry audit and finite assay were not consumed, duplicated, or altered.

## 1. Premises and precise acceptance boundary

Let N=2n+1>=3, R>=2, and

    D = 4^R (2R+1)!,       gcd(D,N)=1,
    M = N^(2R+1),          M_big = N^(2R+3).

The gcd condition is the checkable version of leastprime(N)>2R+1. It implies that 12 and 24 are units modulo every power of N. Choose 1<=a0<N with gcd(a0,N)=1. This canonical choice of the base representative is part of the width bound below; merely specifying an arbitrarily long integer representative of a unit would not bound its input length.

The W031 trace identity is accepted in the [frozen parent disposition](W032-lift-control-review-evidence/inputs/research/findings/W031-jet-parent-disposition.md). Write its integer polynomial as

    J_N(X) = sum_(j=0..n) b_j X^j,       b_0=N*(-4)^n.

The following scalar diagonal, its coefficient construction and denominator claim are **imported provisionally**, as directed by the brief:

    V_R(a) = sum_(k=0..R) N^(2k) G_k(a^2) mod M,
    G_0=1,       G_1(x)=x/24,       G_k in Z[1/D][x].       (I)

Here the import is a formal polynomial congruence obtained by the stated coefficient truncation, not an interpolation inferred from checking 0<=a<N. This distinction is necessary to substitute the larger a below. Section 2 verifies that substitution preserves the normalization and omitted-tail argument; it does not re-audit the G_k coefficients, canonical d1/d2 formulas, higher floors, or root counts. If the separate scalar review changes (I), its denominator guard, or G_1, this acceptance must be reconsidered.

## 2. Larger a: normalization, tail, and input width

For any integer a with gcd(a,N)=1, evaluate z=N*a and Delta=z^2-4 in the quadratic algebra at modulus M_big. Multiplication of coefficient pairs is a ring operation, so reducing z and Delta before binary powering gives the reduction of the exact integer coefficient A_exact. The accepted identity yields

    A_exact = N*a*J_N(N^2*a^2).

The constant term contributes N^2*a*(-4)^n. Each j>=1 term contributes N^(2j+1)*b_j*a^(2j+1), which is divisible by N^2. Thus N^2 divides A_exact for every such a, independently of its magnitude. Its canonical residue A_can modulo M_big also is divisible by N^2, and

    A_can/N^2 = A_exact/N^2 mod M.

Changing the lift of A by M_big changes that quotient by exactly M. The inverse of a*(-4)^n modulo M exists because a and N are coprime and N is odd. This gives the same normalized V_R as the definition in the original construction; neither N nor z is inverted.

After canceling a in this integer identity, the exact normalized expression is the following polynomial over Z[1/2]:

    1 + sum_(j=1..n) N^(2j-1)*b_j*(-4)^(-n)*a^(2j).     (4)

For every j>R, the exponent 2j-1 is at least 2R+1. Each omitted term is therefore zero modulo M, regardless of the size of a and without requiring N|b_j. For the remaining terms the imported formal coefficient collection occurs over Z[1/D]. Its discarded powers of N are already in the ideal (M) before evaluating a. Evaluation at any integer preserves that ideal. Larger a cannot undo divisibility by a power of N, and no nonunit denominator is introduced. This establishes the required extension of the imported diagonal to the lifted inputs. A statement only about finitely many canonical evaluations would not, by itself, justify this step.

Set

    H=N^(2R-2),       a_t=a0+H*t,       0<=t<N.

Since H is divisible by N, gcd(a_t,N)=gcd(a0,N)=1. With the specified canonical a0,

    0<a_t <= (N-1)+H*(N-1) < N^(2R-1).

Consequently a_t has O(R log N) bits, z has O(R log N) bits, and working residues modulo M_big have O(R log N) bits. Computing Delta and all later products with modular reductions stays at this width up to constant factors. Forming an exact A_exact as an ordinary integer is unnecessary and is not covered by this small-width claim.

Reducing a_t all the way modulo N before evaluation would discard the deliberately selected lift and change the experiment. One may reduce z modulo M_big and a modulo the normalization modulus as appropriate; one may not replace a_t by a0 merely because they are congruent modulo N.

## 3. Affine response in a ring, including R=2

All divisibility statements in this section take place in S=Z[1/D]. Since D is coprime to N, reduction of S modulo M is well-defined. We never pass to a field or assume N squarefree.

For any polynomial F over S, the identity

    F(a+h)-F(a) = h*Q(a,h),       Q in S[a,h],

follows term by term from X^j-Y^j being divisible by X-Y. Apply it to F_k(a)=G_k(a^2) and h=H*t. For k>=2,

    N^(2k)*(F_k(a0+H*t)-F_k(a0))
        belongs to N^(2k+2R-2)*S.

The exponent is at least 2R+2, so all these differences vanish modulo M. No Taylor-series convergence, derivative division, or prime-characteristic argument is required.

The constant term has zero difference. The k=1 term is exactly

    N^2*((a0+H*t)^2-a0^2)/24
      = N^(2R)*(a0/12)*t + N^(4R-2)*t^2/24.

Because

    (4R-2)-(2R+1)=2R-3>=1,

the last term vanishes modulo M. Thus

    V_R(a_t)-V_R(a0) = N^(2R)*(a0/12)*t mod N^(2R+1).  (5)

The expression on the right requires a0/12 only modulo N; different lifts of that coefficient change (5) by a multiple of M. Let

    u = a0*12^(-1) mod N.

Then u is a unit, with inverse 12*a0^(-1) modulo N.

At R=2 the working output modulus is N^5. The k=1 difference is N^4*a0*t/12 + N^6*t^2/24, and every k>=2 difference has an N^6 factor. This checks the smallest allowed R directly and symbolically. It uses no canonical-a d2 formula. R=1 is outside the result: the quadratic remainder would no longer vanish by this argument, and the proposed shift need not preserve the unit branch.

## 4. Canonical representatives and all lower carries

Let b=d_R(a0) and write the actual canonical normalized value as

    V_R(a0)=L+N^(2R)*b,
    0<=L<N^(2R),       0<=b<N.

Equation (5) implies the following equality of canonical integers, not merely of rational formal expressions:

    V_R(a_t)=L+N^(2R)*((b+u*t) mod N).                  (6)

Indeed the right side lies in [0,M) and has the required residue modulo M, so it is the unique canonical representative. Therefore

    d_R(a_t)=(b+u*t) mod N.                            (7)

Every lower base-N digit, including the odd-index digits retained for carry propagation, is unchanged. A wrap at the top subtracts a multiple of M, changing the quotient by a multiple of N and leaving (7) intact. This deals with all carries without extending a formula whose proof used a<N. It also shows that, after retaining V_R(a0), the entire normalized scalar output at this precision is reconstructible, not only its top digit.

## 5. Exact distribution, targets, and composite moduli

Because u is a unit in Z/NZ, t -> b+u*t is a bijection of all N residue classes. For each c modulo N there is exactly one solution

    t=(c-b)*u^(-1)=(c-b)*12*a0^(-1) mod N.             (8)

This requires only N, the supplied unit a0, the acquired b, and modular arithmetic. The gcd of c with N need not be known before choosing c. Taking c=0 gives gcd=N, never a proper factor. Taking a c having a proper gcd preserves that same gcd; the lift has not created an additional separating condition.

Uniform t over all residues therefore gives an exactly uniform output c. This is a finite bijection statement, conditional on any fixed acquired base value; it needs no heuristic independence of prime components. Sampling t only from units or from a selected subset does not justify the uniform law. For an arbitrary probability law mu on t, the output law is exactly

    Pr[c]=mu(u^(-1)*(c-b)).

For N=pq with distinct primes, the nonzero multiples of p number q-1 and the nonzero multiples of q number p-1. These sets are disjoint modulo pq and are precisely the residues having proper gcd. Hence

    Pr[1<gcd(d_R(a_t),N)<N]=(p+q-2)/(pq).             (9)

The zero residue has probability 1/N and yields the full gcd. Equation (9) is not asserted for repeated-prime or other composite inputs. More generally, defining phi(N) as the number of unit residue classes, the same counting argument gives

    Pr[proper gcd]=(N-phi(N)-1)/N.

For N=p^e this becomes 1/p-1/p^e; for prime N it is zero. These are counting identities, not instructions to compute phi(N) or discover the factors. The affine theorem and canonical identity (6) remain valid over prime-power and general composite rings under the stated unit checks.

Exact uniform sampling is a distributional premise. It must be implemented and charged if used: rejection from uniformly sampled bit strings below a power of two is exact and has acceptance probability greater than one half, but an uncapped rejection loop has no finite worst-case iteration limit. Nothing here upgrades this probability calculation to a bounded-time factoring guarantee.

## 6. Adaptive and batched use: exact simulation and its limits

Fix N,R,a0 and an acquired base b. A public arithmetic simulator answers any requested t by (7) and any requested gcd by computing gcd((b+u*t) mod N,N). If the consumer sees the full normalized scalar, retain L from the same base acquisition and use (6).

For an adaptive randomized consumer, fix its random tape. Induct on its query transcript: identical earlier answers and gcds cause the same next choice of t, and the affine simulator gives the same next answer. This preserves the transcript, stopping decision, and final factor output. Thus the result covers adaptive choices, not just a prespecified list of individually tested t. Conversely, (8) maps any chosen public gcd argument c into this lifted family once b is supplied. These translations have the per-query costs in section 7.

This statement has concrete limits:

- **Base acquisition is not erased.** The offset b is computed by the scalar procedure. It may itself have useful arithmetic properties. The reduction retains both that paid value and all decisions based on it; it does not prove that acquiring b is useless or cheap independently of R. An algorithm receiving the full base value retains that too.
- **Products can share work.** For m chosen indices, put s=b*u^(-1) mod N. Then

      product_i (b+u*t_i) = u^m * product_i (s+t_i) mod N.

  Since u^m is a unit, the two product gcds are identical. Consecutive t give a product of consecutive shifted public arguments. A product tree, implicit product routine, or localization method can be applied to these same arguments. The algebraic translation is not a lower bound on the cost of any such consumer.
- **A full product gcd is not just a zero leaf.** For a semiprime, a product may be divisible by both p and q because different leaves contain the two factors, even when no leaf is zero modulo N. A batched algorithm must retain and price whatever descent/localization it uses in this case. The affine simulation preserves those leaves and this complication exactly.
- **Differences also carry no new lift-dependent condition.** For any t,v,

      gcd(d_R(a_t)-d_R(a_v),N)=gcd(t-v,N).

  This follows from the unit multiplier u; canonical subtraction changes a residue only by a multiple of N. Nonuniform sampling, repeats, and adaptive correlations therefore remain the same public arithmetic correlations. They are not covered by an independent-uniform-trials success formula unless that sampling law is actually used.
- **A compact family is not all of its outputs.** The pair (b,u) specifies N answers with O(log N) bits of affine data, but materializing all N canonical residues has Theta(N log N) output bits. This is a bound on explicit output, not on an implicit batched consumer. Multiplying the complete family modulo N gives zero because it contains the residue zero; one gcd of that complete product gives N.
- **Changing the observation or base changes the question.** New choices of canonical a0, precision R, other lift depths, or additional information from the quadratic pair beyond the reconstructed normalized value are not disposed of by this fixed-family theorem. New base values require their own acquisition accounting. No claim about their yield is made here.

Accordingly, the parent's phrase “no factor-dependent structure remains in this family” should be read as “no additional top-digit response beyond the acquired base and the explicit unit-affine map.” Calling b public after it has been computed is not a proof that every computation producing or using it is unhelpful. Likewise, simulating outputs does not forbid a faster method for selecting or batching public gcd arguments. This review proves an explicit translation, not a general lower bound on algorithms or factoring.

## 7. Acquisition, affine choices, and materialization costs

Let ell=bitlen(N) and W=(2R+3)*ell. Use F(b) to denote a charged bit-cost upper bound for the chosen b-bit modular multiplication/reduction, integer quotient, gcd and inversion routines, including their ordinary arithmetic overhead. Expressing the cost through F avoids treating an unbounded arithmetic operation as constant time.

A direct branch check can multiply 1,...,2R+1 modulo N and take a gcd, or check their gcds individually, at O(R*F(ell)) cost. It does not require an oracle for leastprime(N), an enormous unreduced factorial, or factors supplied as input. A failed guard exits this theorem's branch; any factor found there is an ordinary preprocessing factor, not a lift success. The a0 unit check is paid separately within the same bound.

Construct the working moduli by powering, execute O(ell) constant-size quadratic-pair multiplication stages, compute (-4)^n modulo M by binary powering, form the unit inverse, divide A_can exactly by N^2, and extract b. This gives the conservative primitive-cost bound

    O((ell+log(R+1))*F(W) + R*F(ell))                  (10)

for one checked base acquisition. Formula (10) includes constructing the modulus, normalization, quotient extraction, and operand widths. There is no need to generate the G_k in this actual computation.

Under the fast-arithmetic model already stipulated in the frozen W032 construction, F(W) is near-linear in W up to logarithmic factors. On the accepted branch R<N, so log W=O(ell). Specializing (10) gives O(R*poly(ell)), with logarithmic factors absorbed into the unspecified polynomial in ell. This is the qualified meaning of the proposed O(R polylog N) claim. Without those arithmetic assumptions, retain (10); an arbitrary multiplication implementation does not imply linear dependence on R. No arithmetic implementation or external complexity theorem is newly certified here. If R is not polynomially bounded in ell, even the stated acquisition bound need not be polynomial in the original input length.

After acquisition and once u and its inverse are available, each supplied t -> c, target c -> t, and individual gcd costs poly(ell) using ordinary finite-width integer algorithms. Computing the residue does not require materializing a_t or recomputing the scalar power. Returning the compact description (a0,R,t) has O(ell+log R) bits. If the consumer requires a_t explicitly, generating and writing its O(R*ell)-bit value is a separate cost. Likewise reconstructing or emitting the full V_R(a_t) from (6) has O(R*ell)-bit output width, even though its top digit has only O(ell) bits.

For m explicit top-digit queries, this is one paid base acquisition plus m*poly(ell) work, plus the actual strategy and batching costs. If explicit lifted inputs are required, charge their generation and output as well. Additional space used by the chosen arithmetic and product routines is not hidden in the constant number of W-bit scalar registers. Neither the probability calculation nor the sharing of acquisition proves a complete successful factoring-time bound.

## 8. Parent disposition and evidence integrity

No algebraic correction is required for (5), (7), (8), or (9) under the imported premises. The parent should retain the following qualifications when accepting the note:

1. Keep the scalar diagonal provisional until its separate audit is accepted; the large-input extension is a formal polynomial substitution, not a consequence of canonical testing.
2. Interpret “the entire family” as a compact affine representation or paid queries, not N outputs in polylogarithmic total time.
3. Retain base acquisition and arbitrary strategy/batch-consumer costs; a full batch gcd may require localization even without a zero leaf.
4. Scope the equivalence to the fixed-base normalized observations at this precision. Preserve the possibility of progress through other canonical-input selection or a different paid consumer; this review settles neither.

The unsupported improvement premise rejected here is that free control of the high input digit, by itself, gives an additional factor-selective output law. It instead gives the exact affine law. A next proof that could change a broader algorithmic conclusion would have to supply useful, paid base acquisition/selection or a genuinely faster public-argument consumer with its own success and total-cost analysis. Developing either is outside this review; neither is a claimed survivor or demonstrated improvement.

All work was confined to this report and its named evidence directory. There were no numerical trials, solver/certificate programs, installs, delegation, commits, shared code or Lean edits, STATE or registry writes. Project code checks were not run because no implementation changed. Administrative filesystem copies, JSON construction and SHA-256 verification are evidence operations, not factoring experiments. No outside technical sources were used and no prior-art or novelty claim is made.

The [read-scope record](W032-lift-control-review-evidence/read-scope.json) distinguishes the complete reviewed inputs from context excerpts and the untouched live sibling scopes. The [integrity preflight](W032-lift-control-review-evidence/integrity-preflight.json) verifies the frozen input bytes and records any later live-source drift without changing the frozen review target.

The [delivery manifest](W032-lift-control-review-evidence/delivery-manifest.json) hashes this report and every evidence payload except the manifest itself and its terminal hash file. The [terminal anchor](W032-lift-control-review-evidence/terminal-manifest.sha256) hashes the exact manifest bytes. The same hash is returned in the external terminal handoff. No report or payload is amended after sealing the manifest.
