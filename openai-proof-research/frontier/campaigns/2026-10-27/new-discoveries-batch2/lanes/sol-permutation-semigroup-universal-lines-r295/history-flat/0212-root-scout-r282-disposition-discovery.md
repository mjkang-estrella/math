# Sustained survivor: harmonic denominator cancellation

Literal target: van Doorn, *On the non-monotonicity of the denominator of generalized harmonic sums*, https://arxiv.org/pdf/2411.03073v2 (23 July 2025), printed p54, last question. Write H_n=u_n/v_n in lowest terms, v_n>0. Is it true, for every integer n>=2, that v_n<v_(n-1) if and only if n does not divide v_n? n=1 requires a convention for v_0, so we explicitly retain n>=2; no claim based on that boundary convention is made.

The closest inspected primary proof is the same paper's p54 reduction to prime-leading-digit harmonic congruences, together with Sun 1210.1562v2 pp2–7 for the unrelated second hold. For this target the actual new calculation is below; no claim that the paper's several earlier theorems already prove it. Cached SunCircularPrimitivePermutationRefutation and GiacomelliLogConcaveConeNonconvex were read completely and do not concern harmonic denominators.

## Mechanism 1: exact gcd reduction (proved helper only)

For any reduced rational u/v, v>0, and n>=1, set

    h=gcd(n,v), r=n/h, s=v/h, g=gcd(r*u+s,h).

Then gcd(r,s)=1, and gcd(r*u+s,r*s)=1: modulo a prime dividing r use coprimality with s; modulo a prime dividing s use coprimality of u with v and r with s. Hence the denominator of u/v+1/n is exactly

    w=h*r*s/g.

Consequently n divides w iff g divides s iff g=1, and w<v iff g>r. This uses ordinary integer divisibility, not a numerical approximation. Applied to u/v=H_(n-1), the full source question is precisely

    for every n>=2, g>1 implies g>r.

The converse g>r implies g>1 is automatic. If n divides v_(n-1), then r=1 and the equivalence is proved. This restriction is not the full source endpoint and earns no nomination.

The exact remaining quantifier is: rule out an integer n>=2 with H_(n-1)=u/v reduced, h=gcd(n,v), r=n/h>1 and 1<gcd(r*u+v/h,h)<=r. Since gcd(g,r)=1, equality g=r>1 is impossible, so the genuine obstruction is 1<g<r.

## Mechanism 2: prime-adic separation (distinct structural route)

Let a=ord_p(n), b=ord_p(v). If a>b, then ord_p(H_(n-1)+1/n)=-a. If b>a, that valuation is -b. Cancellation is possible only when a=b>0. Thus the conjecture is not merely that cancellation occurs; it says any cancellation overcomes every newly introduced prime-power denominator factor r.

If n=p^a is a prime power, every summand of H_(n-1) has p-denominator exponent at most a-1. Its reduced denominator therefore also has b<=a-1. Adding 1/n produces p-exponent exactly a without cancellation, and introduces a factor p^(a-b). All other prime valuations remain unchanged. Thus v_n>v_(n-1) and n divides v_n. The equivalence holds for all prime powers. More generally g=1 whenever every prime dividing h also divides r, since g is coprime to r.

The dyadic valuation gives an additional restriction: in H_m the unique summand with maximal 2-denominator exponent is 1/2^floor(log2 m), so ord_2(v_m)=floor(log2 m). For non-powers of two n, ord_2(n)<floor(log2(n-1)) whenever n is even; for odd n it is zero. Thus 2 never supplies cancellation in the mixed obstruction. Any troublesome g is odd. This observation does not control odd-prime cancellations.

The abstract rational analogue is false: u/v=1/2, n=6 gives h=2,r=3,s=1,g=2,w=3. Here n does not divide w, but w>v. So generic denominator arithmetic cannot close the harmonic-specific bridge. A new harmonic congruence or product bound on cancellation primes is required. This is a method obstruction, not a counterexample to van Doorn.

## Decisive next calculation and eligibility objection

Establish a harmonic-specific lower bound g>n/gcd(n,v_(n-1)) whenever g>1, or exhibit a mixed-prime cancellation violating it. Prime-leading-digit residue constraints on p-adic blocks are the next structural input. Extending the n<=200 diagnostic would not establish this inequality; no expanded census is recommended.

Source version is dated 2025; present access was 30 October 2026 UTC. Current public-registry head remains inaccessible under the inherited parked-route restrictions. No claim of current openness, independent priority, universal newness or acceptance readiness is made. The two proved restricted cases and cancellation characterization are elementary helpers and are retained without nomination. There is no PROOF.md because no full eligible source endpoint is being submitted.

## Second survivor: cumulative finite-field counts

For every prime power q>1 let I_j(q)=j^(-1) sum_(d|j) mu(d)q^(j/d), M_n(q)=sum_(j=1)^n I_j(q). Sun 1208.2683v9 p8 Conjecture 2.17 asserts three strict ratio/root inequalities outside the explicitly listed exceptions (SCOUTING.md). The PDF itself alternates Mn(q) and Mq(n); this note consistently uses cumulative M_n(q).

Mechanism A: the exact-degree Möbius remainder from 1210.1562v2 Lemma 2.1 can be summed, but the resulting error must be propagated through logarithms and discrete second differences. Exact-degree log-convexity alone is not a complete cumulative bridge.

Mechanism B: as a formal power series, sum_(n>=1) M_n(q) z^n = -(1-z)^(-1) sum_(d>=1) mu(d)/d * log(1-q*z^d). The dominant singularity at z=1/q suggests M_n(q)~q^(n+1)/((q-1)n); a universal result with the source's small thresholds needs explicit signed second-difference control, not just this asymptotic. Neither route was completed. This survivor remains below the harmonic-denominator hold because all-q, all-n error control and complete prior-art checking remain substantial.
