**W034 independent review — input-dependent order annihilators**

**Disposition: revised research question; accept the stated semiprime success law and the conditional algorithm, with no general gain established. Verified complete factoring improvement: NONE.** The exponent is constructible in polynomial bit time for a uniformly computable polynomially bounded k. Its usefulness depends on the fraction of each local group actually annihilated. Large prime factors of p−1 are not by themselves an obstruction: their cross-orders and valuations are decisive. Conversely, no proved law here makes those conditions frequent or guarantees them on all inputs.

This is the fresh Codex review round. The failed Opus 5.5 round supplied no mathematical findings and contributes no premises. The [complete brief](W034-input-annihilator-review-evidence/task-brief.md), [frozen input manifest](W034-input-annihilator-review-evidence/input-manifest.json), and [exact read scope](W034-input-annihilator-review-evidence/method-and-read-scope.json) delimit the review. W034 was read in full and frozen at SHA256 `99724b08c90b166d0e736a5a155349416f5f53e07708f6e6032896d5ec8f27a2`. The completed W020 report and both W001 comparator reports were read in full. STATE was consulted only for operating context, not adopted as a different task. W032 evidence, solver code, Lean code, and registries were not read or changed.

**The exact theorem.** Let N=pq with distinct odd primes p,q, let E>0 be an even integer chosen independently of the sampled base, and write E=2^v u with u odd. Sample a uniformly from the original unit group modulo N. For every i=0,…,v inspect

    x_i = a^(u*2^i) mod N,    gcd(x_i−1,N).

Return only a validated proper divisor. Define d_p=gcd(E,p−1), h_p=d_p/(p−1), s_p=v2(d_p), and the analogous q quantities. The exact probability of obtaining a factor is

    P = h_p + h_q − h_p*h_q*(1+C(s_p,s_q)),
    C(s,t) = (4^min(s,t)+2)/(3*2^(s+t)).

This part of W034 needs no correction. Its guarantee can usefully be strengthened: full annihilation of one component is sufficient but not necessary. For any such E,

    (1/2)*max(h_p,h_q) <= P <= h_p+h_q <= 2*max(h_p,h_q).

Thus, for a polynomial-cost exponent family, inverse-polynomial unit success is equivalent, up to constants, to at least one uncovered index `(p−1)/gcd(E,p−1)` or `(q−1)/gcd(E,q−1)` being polynomially bounded. This is an exact per-input diagnostic, not information supplied to the algorithm. Initial nonunit successes are additional and are accounted for below.

**Proof of the probability law.** CRT makes the two original components independent and uniform in cyclic groups. The E-th roots of 1 form subgroups R_p,R_q of sizes d_p,d_q. If a component reaches 1 at any inspected stage, its order divides E, so it belongs to R. Consequently neither-root trials cannot split, and exactly-one-root trials necessarily split at the final stage.

Conditional on membership in R_p, let J_p be the 2-adic valuation of the element's order. The odd part of that order divides u. The first stage at which the p-component equals 1 is exactly i=J_p. A uniform element of the cyclic subgroup of order d_p has

    Pr(J_p=0 | R_p) = 2^(−s_p),
    Pr(J_p=j | R_p) = 2^(j−1−s_p),    1<=j<=s_p.

Conditioning on both root events preserves independence because they constrain separate CRT components. On this branch the chain splits exactly when J_p differs from J_q. For m=min(s,t), its failure probability is

    2^(−s−t) * (1 + sum_(j=1..m) 4^(j−1))
      = (4^m+2)/(3*2^(s+t)).

Adding the two exactly-one-root cases and the both-root success case proves P. Since E is even, s,t>=1. Every atom in either displayed distribution is at most 1/2, so C<=1/2. Conditional on R_p, success has probability `1−h_q*C>=1/2`; the same holds with p,q reversed. This proves the lower bound, while success implies R_p or R_q and gives the upper bound. In particular, h_p=1 gives `P=1−h_q*C>=1/2`; h_p=h_q=1 gives `P=1−C`, not failure.

The initial gcd at a^u is essential: J=0 is a real case. Checking only a^E, or only a^(E/2), does not implement this theorem. A full final gcd is not a failure certificate. Once all preceding gcds have been inspected, stopping at the first global identity is safe. This is the same established recovery principle accepted in W020; no novelty is claimed. W034 uses a base-independent E, so its exact conditional subgroup calculation is simpler than W020's adaptive-collision failure-set argument. It does not authorize resampling from a prefiltered or powered-image distribution.

**Paid sampling and repetition.** One precise N-only interface draws uniformly from `{1,…,N−1}` and first checks gcd(a,N). Every nonunit in this range yields a proper factor for N=pq; none is discarded as a cost-free rejected sample. Put

    rho = (p−1)(q−1)/(N−1).
    P_raw = (1−rho) + rho*P,
    1−rho = (p+q−2)/(pq−1).

This is the exact success probability per raw in-range draw. Drawing n random bits and rejecting values outside that range gives exact uniformity at fewer than two n-bit blocks in expectation. All rejected blocks, gcds, and witness checks are charged. Cached exponent construction is paid once; independent attempts cost at most `T_build + T_trial/P_raw` in expectation, for an upper bound T_trial on an in-range trial's expected paid work. If one component is wholly annihilated, P_raw>=1/2 and at most two raw attempts are needed on average.

For a bounded-time version, use a fixed number of n-bit blocks and count an out-of-range block as a failed attempt. Each block has success probability `(N−1)P_raw/2^n>=P_raw/2`. Under full annihilation, four blocks already give failure at most `(3/4)^4<1/3`; for a weaker success guarantee choose the corresponding paid repetition count. This separates expected rejection sampling from the specification's bounded random-tape claim. It remains a promised-semiprime result, not an all-composite splitter.

**Construction, powering, and space.** For W034 let `F_k(X)=product_(j=1..k)(X^j−1)`, D=k(k+1)/2, n=bitlength(N), and L=bitlength(E_k(N)). Since each N^j−1 has at most jn bits,

    L <= 1 + D*n = O(k^2*n).

Let M(b) bound b-bit multiplication, including same-scale modular multiplication/reduction when used at n bits, and let G(b) bound gcd. With the usual nondecreasing, superadditive multiplication cost, successive construction of N^j and a balanced integer product tree give the safe bounds

    T_build = O(k*M(kn) + M(k^2*n)*log(2k) + k^2*n*log(2k)),
    T_trial = O(L*M(n) + (v+1)*G(n) + L + n),
    storage = O(L*log(2k) + n + k*log(2k)) bits

when the product tree is retained. Discarding completed levels reduces its storage. A final divisibility/witness check has polynomial n-bit cost and is included. Binary powering of a^u and v successive squarings use O(L) modular multiplications; chain gcds number v+1, in addition to the initial raw-sample gcd. Scanning E to obtain u,v is O(L). Output and index bookkeeping are also polynomial. Even schoolbook multiplication and a deliberately loose elementary `G(n)=O(n^3)` yield a total polynomial bound, for example `O(k^4*n^2*log(2k)+k^2*n^4)` including construction and one chain.

There is also an exact formula for the number of squarings, with b=floor(k/2):

    v2(E_k(N)) = k*v2(N−1) + b*v2(N+1) + v2(b!).

It follows by separating odd j from j=2i and summing
`v2(N^(2i)−1)=v2(N−1)+v2(N+1)+v2(i)`. It is valid also for k=1, with 0!=1. The coarser v<L bound already suffices. No integer factorization of E is required. Replacing E by E mod N would be invalid for powering. Likewise, a short expression for `N^lcm(1,…,k)−1` does not give a short binary exponent: its bit length is on the scale of `n*lcm(1,…,k)`, not `n*log(lcm(1,…,k))`.

These costs validate W034's stated modular-work term while making its additive obligations explicit. They establish polynomial cost only for a public k with a uniform polynomial bound in n, not for an unrestricted integer supplied in binary. They do not establish a lower bound on P.

**Exact cross-order and prime-power conditions.** Since p≡1 modulo p−1, N≡q modulo p−1. Therefore

    gcd(E_k(N),p−1) = gcd(F_k(q),p−1).

This proves the proposed full-annihilation equivalence. More precisely, for every prime power ell^e exactly dividing p−1,

    v_ell(d_p) = min(e, v_ell(F_k(q))).

Only these truncated valuations are identified by the congruence: untruncated valuations of F_k(N) and F_k(q) need not agree.

For odd ell, if ell divides q, every q^j−1 is −1 modulo ell and the valuation is zero. Otherwise set r=ord_ell(q) and m=floor(k/r). Then exactly

    V_ell := v_ell(F_k(q))
      = m*v_ell(q^r−1) + v_ell(m!).

The formula includes m=0. Indeed, only exponents j divisible by r contribute. Writing j=ri, the odd-prime lifting identity gives `v_ell(q^(ri)−1)=v_ell(q^r−1)+v_ell(i)`; summing proves the claim. The lifting identity itself follows by factoring out the part of i coprime to ell and applying the binomial theorem at successive ell-th powers. Thus it is an elementary symbolic calculation, not an order-finding oracle.

For ell=2, q is odd and the same odd/even split gives

    V_2 = k*v2(q−1) + floor(k/2)*v2(q+1) + v2(floor(k/2)!).

Full p-component annihilation requires V_ell>=e for every ell^e exactly dividing p−1, including ell=2. If ell>k, the odd-prime formula simplifies to `V_ell=m*v_ell(q^r−1)` because m<ell. A large rough prime is covered when its cross-order is short; a rough prime power also needs enough repeated occurrences or a higher lift at q^r−1. Merely knowing the radical is covered is insufficient.

These conditions give quantitative counterconditions without an input-distribution assumption. Define

    U_p = (p−1)/d_p
        = product_(ell^e || p−1) ell^max(0,e−V_ell).

Then h_p=1/U_p. If both sides retain deficits at least A and B, respectively, `P<=1/A+1/B` and `P_raw<=(p+q−2)/(pq−1)+1/A+1/B`. In particular r>k on a divisor ell^e of p−1 leaves that whole power uncovered. One uncovered side alone does not imply small P: the other component may be fully annihilated.

**Root counting has a local scope.** In F_ell^*, the exact number of residues covered by some X^j−1 with 1<=j<=k is

    R_ell(k) = sum_(d | ell−1, d<=k) phi(d)
              <= min(ell−1, k(k+1)/2).

The equality counts elements by their exact multiplicative orders; the inequality also follows by the degree bound and a union bound. The residue zero is never covered. For a hypothetical uniform unit residue the fraction is R_ell(k)/(ell−1); for a hypothetical uniform field residue it is R_ell(k)/ell. Neither is automatically the probability for prime q in a prescribed size range. No prime equidistribution, independence across divisors of p−1, or density estimate for balanced semiprimes is proved here.

For any fixed integer polynomial F with nonzero reduction modulo ell, at most deg(F) residue classes can satisfy F(q)=0 modulo ell. This observation applies to that specified polynomial only; if ell divides its entire content the bound is inapplicable. An arbitrary algorithmically chosen exponent, or an N-dependent rule choosing the coefficients, is not covered by this fixed-polynomial statement. Failure of F_k gives no lower bound on arbitrary input-dependent exponents or factoring.

**Two symbolic input families and their limits.** First take k=1. Then

    d_p = d_q = gcd(p−1,q−1) = g,
    h_p = g/(p−1),    h_q = g/(q−1),
    s_p = s_q = v2(g).

This follows from N−1≡q−1 modulo p−1 and its counterpart modulo q−1. If `q=1+t(p−1)` is prime with t>=2, the p-component is wholly annihilated by N−1 irrespective of how rough p−1 is. The N-only exponent and its chain have polynomial bit cost. This is a conditional nonsmooth-order example; smoothness is not logically necessary for the generalized p−1 consumer. No free generation of such prime pairs or useful density is asserted.

The simple balanced subfamily offers no new factoring advantage. Under a public promise t<=T with T polynomial in n, enumerate t and test the integer discriminant

    Delta_t = (t−1)^2 + 4*t*N.
    p = (t−1+sqrt(Delta_t))/(2*t).

An exact square, integrality, and divisibility check give a deterministic `T*poly(n+log T)` splitter for this family. Its derivation is just `N=t*p^2−(t−1)*p`. A constant bound on q/p bounds t. When t is large and unknown, this enumeration cannot be treated as cheap. The point is a paid comparator for the small-ratio examples, not a claim that every higher-k cross-order family reduces to this quadratic calculation. Both components cannot be fully annihilated at k=1 for distinct p,q, because mutual divisibility of p−1 and q−1 would force p=q.

For an exact negative control, take distinct safe primes `p=2r+1`, `q=2s+1`, with r,s distinct odd primes. At k=1, g=2, hence

    P = 1/r + 1/s − 3/(2*r*s).

This is small when both r,s are large, although E has only O(n) bits. It is a symbolic identity for every prime pair satisfying the hypothesis; no search, sample, or infinitude claim was used. For arbitrary k the same law holds if each rough prime is either a divisor of the opposite prime or has cross-order greater than k. More generally use the exact deficits above. These conditions do not prove an infinite bad family for every growing k(n), and therefore do not prove that W034 can never give a general gain.

**Primary prior art and what it establishes.** Pollard's original §4 constructs an exponent from small prime powers, applies binary powering and gcd, and adds a one-large-prime second stage. The read pages also handle full gcds by reducing the smoothness bound. His §3 already relates divisibility by multiples of N−1 to equations between the two prime factors. This supports classifying the consumer as generalized p−1 and recognizing the elementary small-ratio family; it does not identify W034's exact product as previously published. [Pollard, 1974, printed pp. 525–527](https://cr.yp.to/bib/1974/pollard.html), [publisher record](https://doi.org/10.1017/S0305004100049252).

Bach–Shallit's Theorem 4 takes a supplied multiple of Phi_k(p) and, under ERH, splits an input that is not a prime power in randomized polynomial time. Its algebra uses extension-field multiplicative groups and Galois actions. W034 instead powers in the ordinary unit group modulo N and seeks multiples of p−1 from F_k(N). The formal factorization `F_k(X)=product_(d=1..k) Phi_d(X)^floor(k/d)` does not equate the two algorithms. Theorem 5's smoothness construction and Theorem 4 were checked through indexed primary text; direct PDF retrieval was blocked. This is not a full-paper proof audit. [Bach–Shallit, 1989, §9, printed p. 214 onward](https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf). The author's errata were also consulted; their coefficient-gcd correction is relevant to implementations of that paper, not used in W034's scalar proof. [Bach, errata](https://pages.cs.wisc.edu/~bach/errata.pdf).

Generalized RSA cycling attacks already inspect `gcd(C^(e^j)−C,N)`, as described in Rivest–Silverman §9. For a unit C this has the same gcd as `C^(e^j−1)−1`. This is a close exponent-family precedent. Substituting e=N gives W034's individual factors in the exponent, but combining all j by multiplying the exponents can accumulate prime-power coverage, so the cited cycling loop is not declared identical. No RSA requirement that e be coprime to phi(N) is needed for W034's positive modular powers. Distributional conclusions about a randomly chosen encryption exponent cannot be transferred to e=N. [Rivest–Silverman, November 1999 version, §9, printed pp. 17–18](https://people.csail.mit.edu/rivest/pubs/RS01.version-1999-11-22.pdf).

This bounded primary search establishes known recovery machinery and close precedents, not novelty or the absence of prior art for the precise product. The [primary-source ledger](W034-input-annihilator-review-evidence/sources/source-ledger.json) records exact source access, read ranges, retrieval hashes, and limitations. The earlier W001 reports supply comparison scope, not a license to claim GNFS, ECM, or an all-input deterministic improvement. No such comparison has been won here.

**A concrete next computation, not an order oracle.** The smallest useful extension to examine symbolically is the explicitly constructible hybrid

    H_B = lcm(1,…,B),    E_hyb(N;B,k) = H_B*F_k(N),

with public positive polynomial bounds B,k, followed by precisely the same original-base chain. Starting with H=1, compute H_B by the recurrence `H <- (H/gcd(H,i))*i` for i=2,…,B; this avoids requiring a prime enumeration primitive. Its elementary size bound is W=O(B log(2B)) bits, or O(B) with the standard lcm estimate. With elementary arithmetic, a safe bound for construction and one trial is `T_build + O(B*W^3 + (W+L)^2 + (W+L)*n^3)`: it charges the gcds/divisions, integer multiplication by F_k(N), and the longer modular exponent. Storage remains polynomial in W,L,n. No knowledge of p,q or their orders enters construction.

For each diagnostic ell^e exactly dividing p−1 the hybrid's exact criterion is

    v_ell(H_B) + V_ell >= e,

where `v_ell(H_B)=max{a:ell^a<=B}` and V_ell is the proved formula above. This isolates the constructive question: can a public low-degree exponent provide a rough factor while H_B supplies the other missing prime powers? A promised `p−1=m*R` with m dividing H_B and R dividing F_k(q) is sufficient, including overlapping prime supports, since their valuations add.

The next proof should exhibit such a family with a polynomially bounded uncovered index, establish which coverage is absent from H_B alone and F_k alone, and compare against a pure smooth exponent at the same **total bit-work** budget and against the quadratic family test above. If only the already-covered smooth portion improves, reject a claimed nonsmooth advantage. For large ell>k the decisive symbolic check is `floor(k/ord_ell(q))*v_ell(q^ord_ell(q)−1)` after deducting H_B's contribution. Those hidden quantities are proof diagnostics; the proposed executable computation is H_B*F_k(N), not a request to obtain them in the solver.

For this comparison, note that `log H_B` grows on the scale of B, while W034 spends O(k^2*n) exponent bits. Merely avoiding a sieve is not an asymptotic win: an equal-budget smooth exponent may cover far more small primes. The only plausible new benefit is cheaply acquired rough coverage, or a materially different paid exponent rule with a better useful-input theorem. Any later finite screen requires a new preregistration; none is proposed as already authorized or run here.

**Delivery and limits.** The symbolic theorem, valuation identities, root bound, family identities, and cost bounds are the evidence for the conditional mechanism. The missing per-input or distributional success guarantee and the known competitors prevent promotion to a complete factoring improvement. No numerical experiment, factor search, symbolic-computation program, solver execution, Lean build, installation, commit, or delegation was performed. Python was used only for copying, document retrieval, provenance, and integrity bookkeeping. Only this report and the assigned evidence directory were written. The [integrity record](W034-input-annihilator-review-evidence/verification.json) and [complete delivery manifest](W034-input-annihilator-review-evidence/delivery-manifest.json) accompany the report; the manifest's SHA256 is anchored outside the files in the handoff message.
