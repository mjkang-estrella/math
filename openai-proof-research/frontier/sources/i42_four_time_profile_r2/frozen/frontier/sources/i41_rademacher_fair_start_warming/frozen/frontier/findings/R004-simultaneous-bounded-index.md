# R004 — Simultaneous bounded residual index on a positive proportion of primes

Date: 2026-10-08. **Status: validated deduction under the user's accepted-corpus premise; literature priority unproved.** This is a substantive arithmetic consequence, but its synthesis of established mechanisms has not met the frontier's separate nonroutine-novelty gate. It is not a resolution of Artin's conjecture or Arnold's problem over integer moduli.

This corrected record supersedes Route B of [the discovery report](../iterations/i02-arithmetic.md). The [independent audit](../reviews/i02-arithmetic-r2.md) supplies detailed field, smoothing, quantifier, and prior-art checks. The immutable upstream revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Statement

For a prime p not dividing a, set i_p(a)=(p−1)/ord_p(a). Put δ=10⁻⁶ and c*=−log(1−δ)>10⁻⁶. Assume the two accepted corpus inputs below.

**Theorem.** For every finite set A of integers with |a|≥2 and every η>0, there exist positive integers B=B(A,η) and a real x₀=x₀(A,η) such that for every real x≥x₀,

    #{x<p≤2x : p∤∏(a∈A)a, and i_p(a) divides B for every a∈A}
       ≥ (c*−η)(π(2x)−π(x)).

In particular, all these indices are at most B. The assertion includes negative bases and perfect powers. It does not assert a natural density, or one B attaining c*. Taking η=c*/2 gives an absolute positive relative lower density with B depending only on A. No effective value of x₀ is furnished.

**Corollary.** For every fixed integer |a|≥2,

    ∑(p≤X, p∤a) ord_p(a) ≍_a X²/log X,
    liminf(X→∞) [1/π(X)] ∑(p≤X, p∤a) ord_p(a)/(p−1) > 0.

These concern prime moduli only and give an order of magnitude, not an asymptotic constant.

## Exact accepted inputs

1. **PD:** *The Poisson–Dirichlet Law for Prime Predecessors*, `build/sections/01-introduction.tex`, Theorem `thm:main`, and `08-poisson-dirichlet.tex`, equation `pd:dyad-law`. The ranked logarithmic prime factors of p−1, with multiplicity, converge under ordinary prime counting to PD(1). The conclusion holds at all real endpoints. [Pinned statement](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex).
2. **HZ and splitting:** *Primitive roots for every admissible integer base*, `build/sections/01-introduction.tex`, Theorem `thm:hecke-zero-free`, gives a common zero-free width δ for finite-order Hecke L-functions over all cyclotomic fields containing μ₁₂. In `07-splitting.tex`, Lemmas `spl:field-bounds` and `spl:smooth-estimate` imply (S) below for all sufficiently large prime q, without an upper bound on q. [Pinned splitting section](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/07-splitting.tex).

Specifically, for each fixed |a|≥2 there are q₀(a), C_a such that for every prime q≥q₀(a) and every x≥2, with K_q=Q(μ_q,a^(1/q)),

    N_a,q(x) := #{x<p≤2x : p splits completely in K_q}
      ≤ C_a [x/(q(q−1)log x) + x^(1−δ)log(2q)/log x].       (S)

This estimate is already displayed before the source's final specialization to a shorter q range; it is not a new analytic estimate invented here. The larger range follows from the exact lemma contracts, not from applying the narrower final proposition outside its hypotheses.

For completeness, choose a rational prime ℓ dividing |a| and take q>max(ℓ,v_ℓ(|a|),3). The valuation of a over ℓ in Q(μ_q) is not divisible by q, so [K_q:Q]=q(q−1). The power-basis discriminant gives (log D_q+[K_q:Q])/[K_q:Q]≪_a log(2q). To descend HZ, adjoin μ₁₂q: both the extension over that cyclotomic field and the extension over K_q are abelian. The first zeta factorization is zero-free by HZ; the quotient in the second consists of entire nonprincipal Hecke functions, so zeros of ζ_Kq cannot be canceled. Choose one nonnegative smooth f≥1 on [1,2]. The accepted smooth estimate is field-uniform, with error x^(1−δ)(log D_q+[K_q:Q]). Every completely split prime supplies [K_q:Q] terms of weight at least log x in its nonnegative prime-ideal sum. Division proves (S). This also explains why perfect powers and negative a cause no gap: exceptional small q are excluded by q₀(a).

## Proof

Write N(x)=π(2x)−π(x)∼x/log x. The empty set A is immediate with B=1. For η≥c* the asserted lower bound is nonpositive, also immediate. Assume k=|A|≥1 and 0<η<c*.

Choose 0<θ<δ with c(θ):=−log(1−θ)>c*−η/4. Set C=max(a∈A)C_a. Choose an integer Y≥max(2,max(a∈A)q₀(a)) so large that 2kC/Y<η/8. For each prime q≤Y choose an integer k_q≥2, sufficiently large that

    ∑(q≤Y) 1/φ(q^k_q) < η/8.

Define B=∏(q≤Y)q^(k_q−1). All these choices precede x→∞; only finitely many fixed moduli are used.

**Reservoir.** Let G(x)={x<p≤2x : P⁺(p−1)>x^(1−θ)}. PD and the continuity of its largest-factor distribution give

    #G(x)/N(x) → c(θ).

Indeed log(p−1)/log x=1+O(1/log x) uniformly on a dyad; sandwich the threshold by fixed thresholds 1−θ±ε. The largest PD(1) factor has density 1/t on (1/2,1), yielding the integral −log(1−θ). One may use the source's dyadic law directly, or subtract its two convergent cumulative averages; this does not subtract mere lower bounds.

For p∈G write p−1=mQ, where Q=P⁺(p−1) and m<2x^θ. For large x, Q>m, so Q has exponent one. Every prime divisor of i_p(a) either equals Q or divides m.

**Large divisor exception.** If Q|i_p(a), then ord_p(a)|m. Such a prime divides the nonzero integer ∏(1≤j≤J)|a^j−1|, with J=⌈2x^θ⌉. Since |a^j−1|≤(|a|+1)^j, the number of these prime divisors exceeding x is O_a(J²/log x)=o(N(x)). Sum over the fixed finite set A. Primes dividing ∏a also contribute o(N(x)).

**Middle divisor exception.** If a prime Y<q<2x^θ divides i_p(a), cyclicity of F_p* implies p≡1 mod q and a^((p−1)/q)≡1 mod p. The source's Lemma `alg:splitting-test` says p splits completely in K_q. Here q<p because q|p−1; there is no p=q exception. Sum (S) over q and a. The main term is at most

    kC x/log x · ∑(n>Y)1/[n(n−1)] = (kC/Y)x/log x.

The summed error is O_A(x^(1−δ+θ))=o(N(x)), because θ<δ. Hence this exception has size <ηN(x)/4 for all sufficiently large x.

**Small prime-power exception.** Fixed-modulus prime number theorems and the union bound give

    #{x<p≤2x : q^k_q | p−1 for some prime q≤Y}/N(x)
      ≤ ∑(q≤Y)1/φ(q^k_q)+o(1) < η/4

eventually. This is an upper bound, not an equality: intersections of progression conditions can have positive density.

Outside these exceptions every index has prime factors ≤Y and q-adic valuations ≤k_q−1, so i_p(a)|B simultaneously for all a. For sufficiently large x, the reservoir has size at least (c(θ)−η/8)N(x), the large-divisor and excluded-base-prime exceptions have size <ηN(x)/8, and the other two exceptions have size <ηN(x)/4 each. The surviving proportion exceeds

    c(θ)−3η/4 > c*−η.

This proves the theorem, including the strict error margin.

For the corollary fix η=c*/2 and apply the theorem on (X/2,X]. Each good prime contributes ord_p(a)≥(X/2−1)/B and ord_p(a)/(p−1)≥1/B. The first sum is ≫_a X²/log X, while its upper bound follows from ord_p(a)≤p−1. The normalized second sum has liminf at least c*/(4B)>0. This proves both assertions.

## What remains open

The theorem permits small prime factors in the residual index; it does not give index one. Marginal PD convergence cannot be conditioned on a progression without a new argument. The original report's attempt using complete splitting in K_q(μ_M) also selects residue 1 modulo M, not an arbitrary required residue.

The audit gives a repaired conditional route: full PD convergence in every fixed reduced progression would suffice for the single-base positive-density primitive-root claim. A union of small-prime avoiding classes has mass comparable to 1/log Y, which can beat the global 1/Y tail. Mere unspecified positive mass in each class does not close that budget. The progression extension is a new research task, not a premise silently added to this theorem.

## Prior art, significance, and validation

The target is related to Artin's primitive-root conjecture, [MathDB #316116](https://mathdb.com/p/316116), retained in the earlier scout as “celebrated”; this is historical project evidence, not a newly verified importance score. Bounded index is a weaker conclusion than a primitive root.

[Kurlberg–Pomerance (2013), Theorem 2](https://msp.org/ant/2013/7-4/ant-v7-n4-p08-p.pdf) gives a stronger prime-average asymptotic under GRH. [Their period paper, Lemmas 19–20](https://math.dartmouth.edu/~carlp/PDF/par11.pdf), already gives order >p^0.677 on a positive proportion for a fixed positive base, and uses the short-product exception above. [Goldmakher–Martin–Péringuey, §8](https://arxiv.org/html/2502.19601v1) gives unconditional upper bounds for small index-factor statistics, not this positive lower density. No exact duplicate was located in this targeted primary-source screen. That is not a certification of worldwide priority or a nonroutine new mechanism. The advance over the cited bounds is bounded index on a positive proportion, under the two accepted corpus inputs.

The parent read the actual source contracts and full independent review, verified 60 manuscript blobs against the pinned preprint tree and four literature hashes, and reran the checks. The nonvacuous finite test uses B=12, 18 signed/perfect-power bases and three dyads: 86,232 surviving base–prime instances, zero violations; 2,430 orders were separately checked by repeated multiplication. It also exhibits the CRT union correction 7/12 versus the erroneous sum 2/3. The test exponent is 7/20, not the theorem's tiny exponent. None of these experiments verifies PD, HZ, asymptotic density, or novelty. Full evidence: [review manifest](../sources/i02_arithmetic_r2/manifest.json), [parent verification](../sources/i02_arithmetic_r2/parent-verification.json), and [finite output](../experiments/i02_arithmetic_r2/results.json).
