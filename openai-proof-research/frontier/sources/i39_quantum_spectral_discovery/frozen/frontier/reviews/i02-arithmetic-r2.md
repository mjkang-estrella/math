# Independent review of arithmetic round 1

Date: 2026-10-08. Reviewer is not the author. Scope: deductions from accepted statements, not their truth. Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Read `AGENTS.md`, `sources/upstream.json`, the relevant entries of `sources/CONTENTS.md`, `frontier/iterations/README.md`, and all of `frontier/iterations/i02-arithmetic.md`. No further agents, staging, commits, or shared-report/index edits.

## Verdict

**Theorem B as formally quantified in §4.1 and Corollary B1 are correct deductions from the pinned corpus after the elementary repairs below.** I found no fatal field-degree, zero-free-descent, discriminant, smoothing, or growing-q error in (S). In particular, the uniform estimate really extends to prime q up to `2 x^theta`, for any fixed `theta < 10^-6`, and covers positive perfect powers and negative bases.

**The report as a whole should not be accepted unchanged.** Its opening summary overstates the density quantifier; the E3 equality is false; the error budget needs its positive margin made explicit; and §4.4's progression-only Artin reduction is not justified as written. The latter can be repaired under full PD convergence in every fixed reduced progression, without Chebotarev-conditioned PD, by using a union of classes. Mere unspecified positivity in each progression is insufficient for the displayed argument. This defect does not enter Theorem B.

**Novelty:** targeted primary literature supports a real improvement over the cited known results, but does not prove worldwide novelty. **Significance:** an absolute positive proportion with simultaneously bounded residual indices, and the correct prime-average order of magnitude for every fixed base, are substantial consequences. The new argument uses established index-divisor and union-bound mechanisms; I do not certify that it meets the project's separate demand for a *nonroutine* new theorem. Parent acceptance must distinguish that criterion from proof correctness.

## 1. Exact source contracts and integrity

I independently recomputed Git blob hashes against `sources/preprints-tree.json`, not just the author's `ok` flags: all 59 arithmetic-cache files and the QRH file matched. Full paths, SHA-256 hashes, sizes, original input hashes, and literature download hashes are in `frontier/sources/i02_arithmetic_r2/manifest.json`; reproduction is `verify_and_fetch.py` in that directory. These are integrity checks, not proof checks. Existing cached manuscripts were read directly; no moving-branch manuscript was used.

The following prefixes abbreviate exact paths at the pin:

- P = `preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`
- D = `preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`
- T = `preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/`
- S = `preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`

Exact files and Git blob hashes:

- P`sections/01-introduction.tex`: `d3ed0c86e7524058a601145a4863acdb89d576e7`. Theorem `thm:hecke-zero-free`: all finite-order Hecke characters of every cyclotomic field containing μ12 have no zeros in `Re s > 1−10^-6`. Principal poles at one are allowed. There is no conductor, height, or field-degree cutoff. The theorem's global conclusion, not uniformity of auxiliary estimates inside its proof, is what is used. Theorem `thm:primitive-root`/`thm:main` gives `≫_a x/log²x` primitive-root primes per dyad for an admissible base, not positive relative density.
- P`sections/07-splitting.tex`: `ee9b3eac0decd351991b6b3f8d2b237b5df2970d`. Lemmas `spl:field-bounds`, `spl:smooth-estimate`; equations `spl:degree-discriminant`, `spl:kummer-zero-free`, `spl:smooth-explicit-formula`, `spl:unit-zero-count`. Both lemmas have broader contracts than Proposition `prop:splitting` as ultimately stated. The displayed penultimate estimate in the proposition's proof is precisely (S).
- P`sections/01a-reduction.tex`: `260e5612b0f4e3b70a870d7dc28001abb24a16ee`. Lemmas `alg:splitting-test`, `alg:quadratic-progression`; Proposition `prop:controlled`/`prop:prime-reservoir`. I read the full reduction and the quadratic-progression proof, including its negative-square and odd-perfect-power cases.
- D`sections/01-introduction.tex`: `79950676c100e2d2d9252cc5465707a0d8f6c891`. Theorem `thm:main`, equation `eq:main-law`, is ordinary equally weighted convergence for all real endpoints, with factors counted with multiplicity and denominator `log(p−1)`.
- D`sections/08-poisson-dirichlet.tex`: `43e3be6367fec010268d296d81f28be22c303efb`. Equation `pd:dyad-law` already states dyadic convergence for every real x. No arithmetic-progression or Chebotarev conditioning appears in this conclusion.
- T`sections/01-introduction.tex`: `437e7a0c606b619d2ad33e5d2998514c8bc8c996`; T`sections/03-splitting.tex`: `a4fa53f648a9f53ba0fd1e97731c03d72c86b90f`. Theorem `thm:main` is conditional on four explicitly listed companion inputs and gives `≫ x/log²x` simultaneous primitive roots for distinct positive prime bases. Equations `eq:abelian-zeta-factorizations`, `eq:smooth-prime-ideal-formula`, and `eq:complete-splitting-bound` confirm the same field-uniform mechanism. This is not a duplicate of B.
- S`sections/00-introduction.tex`: `3d9d4c55c1f30d7736e7c7427b97cb0461f06040`. Theorems `thm:smooth` and `thm:totient` concern smooth predecessors and totient fibers, not bounded indices. I also read the parity companion's actual `thm:main` in `preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/main.tex`, blob `837740bf086f56d9c20fba6b3c7ff20ff53b581d`; it supplies an infinitude statement about squarefree predecessors with even Ω, not B.

For the core two source files, SHA-256 values are:

- P`sections/07-splitting.tex`: `b8dc6a9385c2bf695544b5b81e8460dd053083f2346dc6a1d8a81f6dfc084a94`.
- D`sections/01-introduction.tex`: `ae0c15651b162958c193f0ad32078146e17fb1f566d47c14be9df9cb6accb1ca`.

## 2. Audit of the crucial estimate (S)

Write δ = 10^-6. Fix an integer a with |a|≥2. Choose a rational prime ℓ dividing |a| and let e=v_ℓ(|a|)>0. For every prime q exceeding max(ℓ,e,3), ℓ is unramified in E=Q(μ_q), and every valuation of a over ℓ equals e, which is not divisible by q. Thus a is not a qth power in E. Since E contains μ_q, adjoining a qth root gives a cyclic extension of degree q. Consequently

`[Q(μ_q,a^(1/q)):Q] = q(q−1) = n_q`.

This argument uses |a| only for the finite valuation and so includes a<0. If a is a perfect power, finitely many small q can have smaller degree; the chosen q0(a) removes them. One must not claim this degree formula for every q: for example a=8, q=3 gives K_q=Q(μ3), of degree 2. Such q are placed below Y in the proof and handled by the fixed prime-power exclusions. The value q0 need not be uniform in a.

The root is integral. The power-basis discriminant and the tower formula give

`D_q ≤ q^[q(q−2)] (q^q |a|^(q−1))^(q−1)`.

In particular

`(log D_q+n_q)/n_q ≤ 2 log q + log|a| + 1 ≪_a log(2q)`.

There are no ramified rational primes outside aq. The logarithmic discriminant, rather than D_q itself, enters the smoothed estimate; division by n_q is essential. No unnoticed q² factor survives.

For descent, put F=Q(μ_(12q)) and L=K_q F. The extensions L/F and L/K_q are both abelian: the first is Kummer cyclic, and the second has Galois group embedded in Gal(F/Q). Abelian factorization yields

`ζ_L = ∏_χ L_F(s,χ)`, and `ζ_L/ζ_Kq = ∏_(ψ≠1) L_Kq(s,ψ)`.

The first product is covered by the exact accepted HZ contract, since F is cyclotomic and contains μ12. Every factor in the second product is an entire nonprincipal finite-order Hecke function. Therefore a zero of ζ_Kq away from one in the given half-plane cannot be canceled by a pole of the quotient; it would force a zero upstairs. At one ζ_Kq has its usual pole. No zero-free assertion over the noncyclotomic field K_q is being assumed without this argument. Exact primitive Hecke/Artin factorizations include ramified factors, so omitted Euler factors do not create a pole-cancellation loophole.

Choose one nonnegative `f∈C_c^∞((0,∞))` with f≥1 on [1,2], independent of q,a,x. Lemma `spl:smooth-estimate` gives, for every x≥2,

`Θ_K,f(x) ≪_f x + x^(1−δ)(log D_K+[K:Q])`.

Its explicit formula has main term xΦ(1), an absolutely convergent zero sum, a residue at zero of size O_f(n), and a fixed-line integral O_f(x^-1/2(log D+n)). The unit-height count is O(log D+n log(2+|T|)). Rapid Mellin decay therefore bounds the zero sum by O_f(x^(1−δ)(log D+n)); a zero on Re s=1−δ is allowed and has exactly the stated bound. The fixed left contour is Re s=−1/2, away from trivial zeros. Thus neither an ε loss in the exponent nor an extra log x is required. Constants of intermediate horizontal-contour choices may depend on K, but those integrals vanish for each K; the final bound is from the fixed contour and the uniform zero count. This is sufficient for a bound simultaneously valid for all fields and all x≥2.

Each unramified completely split rational prime in (x,2x] gives n_q prime ideals of norm p. Their first-power terms contribute at least n_q log x. All other prime-ideal/power contributions are nonnegative. Hence there is no subtraction of higher-degree ideals, no need to estimate prime powers separately, and no field-dependent smoothing choice. Dividing gives

`N_a,q(x) ≤ C_a [ x/(q(q−1)log x) + x^(1−δ)log(2q)/log x ]`.  **(S)**

This proves the advertised contract: one C_a and q0(a), all primes q≥q0(a), all x≥2. The restriction q≤exp((log x)^0.3) is used only in the source's last simplification after this estimate. Applying the lemmas directly is a valid new deduction even though applying the proposition's narrow statement alone would not be.

For q<2x^θ, the error sum is at most

`(C_a x^(1−δ)/log x) (2x^θ) log(4x^θ) = O_a(x^(1−δ+θ))`.

For fixed θ<δ this is o(x/log x). The harmless factor 2 in the q range does not affect the exponent. At θ=δ this reasoning fails, which matters for the endpoint density quantifier.

## 3. Repaired full proof of Theorem B

Let N(x)=π(2x)−π(x). For empty A use B=1: every prime qualifies. For η≥c* the lower bound is nonpositive and is automatic with B=1. It remains to treat k=|A|≥1 and 0<η<c*, where c*=−log(1−δ).

First choose fixed 0<θ<δ so that c(θ):=−log(1−θ)>c*−η/4. Put C=max_(a∈A) C_a, with constants from (S). Choose an **integer** Y≥max(2,max_a q0(a)) so large that `2kC/Y < η/8`. For each prime q≤Y choose an integer k_q≥2 such that

`Σ_(q≤Y) 1/φ(q^k_q) < η/8`.

This is possible because there are finitely many q and each summand tends to zero as k_q grows. Define the fixed integer `B=∏_(q≤Y) q^(k_q−1)`. All choices precede x→∞; no theorem uniform in growing fixed moduli is being invoked.

### The PD reservoir

Set G(x)={x<p≤2x : P⁺(p−1)>x^(1−θ)}. The dyadic PD law gives

`#G(x)/N(x) → c(θ)`.

Indeed, uniformly in the dyad, log(p−1)/log x=1+O(1/log x). The defining threshold for V1 is therefore 1−θ+O(1/log x). Sandwich it between fixed thresholds 1−θ±ε and then let ε↓0. The largest PD(1) component has continuous density 1/t for 1/2<t<1, giving tail integral −log(1−θ). This applies since θ<10^-6. The slight possibility p−1<x for a real x causes no problem with this uniform logarithmic comparison.

Alternatively, write the cumulative continuous-test sum as E[F]π(t)+o(π(t)), subtract at 2x and x, and use π(x)/N(x)→1, π(2x)/N(x)→2. Both cumulative errors remain o(N(x)). There is no illegal subtraction of two mere lower bounds. The source also supplies this exact dyadic law as `pd:dyad-law`.

### Structure and exceptional primes

For p∈G(x), put Q=P⁺(p−1) and m=(p−1)/Q. Then m<2x^θ. Once x is large, Q>x^(1−θ)>2x^θ>m, since θ<1/2. Thus Q appears to exponent one. Any prime divisor q of i_p(a) either equals Q or divides m.

If Q divides i_p(a), then ord_p(a) divides m. With J=ceil(2x^θ), all such p>x divide the nonzero integer

`∏_(1≤j≤J) |a^j−1|`.

For both signs of a, |a^j−1|≤(|a|+1)^j, and no factor vanishes. Taking logarithms and counting distinct prime divisors greater than x bounds this exception by O_a(J²/log x)=O_a(x^(2θ)/log x)=o(N(x)). Multiple divisibility only overcounts, which is harmless. This is also valid when a is a perfect power. Sum over the fixed finite A.

If q divides i_p(a) and Y<q<2x^θ, the group-order identity gives p≡1 mod q and a^((p−1)/q)≡1 mod p. The exact splitting-test lemma applies after removing the finitely many p|a. There is **no additional q=p exception**: q|p−1 already implies q<p. Also 2x^θ<x for large x. The report's phrase about primes dividing q is unnecessary.

Summing (S) first over q and then over bases gives an exception of size at most

`kC x/log x Σ_(n>Y)1/[n(n−1)] + O_A(x^(1−δ+θ))`

`= (kC/Y) x/log x + o(N(x))`.

The integer sum telescopes exactly for integral Y; the report's looser 2/Y is also valid. Since N(x)∼x/log x, our choice makes the whole middle-range exception less than ηN(x)/4 for all sufficiently large x.

For E3, consisting of primes with q^k_q|p−1 for some q≤Y, fixed-modulus PNT and the union bound give

`#E3/N(x) ≤ Σ_(q≤Y)1/φ(q^k_q) + o(1) < η/4`

eventually. **The original equality is false.** Intersections have positive density, not o(1). For instance, conditions p≡1 mod4 or p≡1 mod9 have union density 1/2+1/6−1/12=7/12, whereas the proposed sum is 2/3. Replacing equality by ≤ suffices. One can compute the exact finite union by CRT, but it is not needed.

Outside all these exceptions and p|∏a, every index has only prime factors q≤Y and valuations at most k_q−1. Thus **i_p(a) divides B**, simultaneously for all a, which is stronger than the stated numerical bound.

For sufficiently large x, use the four explicit budgets:

- #G/N≥c(θ)−η/8;
- the sum of the product-divisor exceptions plus p|∏a has relative size <η/8;
- the middle-range exception has relative size <η/4;
- E3 has relative size <η/4.

The resulting good fraction is at least c(θ)−3η/4>c*−η. All convergence errors have been absorbed with a positive margin. This proves the formal theorem for every sufficiently large **real** x. The author's original strict parameter inequalities could also supply a margin; they should have been displayed explicitly rather than leaving the last `−o(1)` unexplained.

### What density and dependence have actually been proved

The conclusion is `for every η>0, there exists B(A,η)`. It is **not** `there exists B(A) attaining lower density c*`, and it gives no exact natural density for the good primes. A safe endpoint formulation is

`sup_B liminf_(x→∞) #{good primes for B in (x,2x]}/N(x) ≥ c*`.

The same c*−η lower bound transfers to cumulative relative lower density by summing dyads above a fixed threshold; alternatively discard a finite number of initial dyads and then let their relative mass vanish. This does not establish existence of a density. Taking η↓0 does not commute with choosing a single B. The opening summary should therefore retain η, or say simply that an absolute positive lower density (for example c*/2) is attained with B depending on A. Fixing η=c*/2 legitimately makes B a function of A alone. No explicit effective x0 is furnished by qualitative PD convergence.

## 4. Corollary B1

Fix a, take η=c*/2, and let B=B({a},c*/2). On (X/2,X], at least (c*/2)(π(X)−π(X/2)) primes have ord_p(a)≥(p−1)/B≥(X/2−1)/B. Their contribution is ≫_a X²/log X. The upper bound follows from ord_p(a)≤p−1 and PNT, or the crude bound Xπ(X). Thus the two-sided order-of-magnitude assertion is correct.

On the same dyad each good prime contributes at least 1/B to ord_p(a)/(p−1). Dividing by π(X) and using (π(X)−π(X/2))/π(X)→1/2 proves a liminf at least c*/(4B)>0. The source report did not write out this second assertion, but it follows immediately. No convergence or explicit limiting constant is claimed or proved.

Call this the **fixed-base prime-average order-of-magnitude result**. Arnold's original conjecture concerns averaging over all integer moduli; B1 does not settle that conjecture or the GRH prime-average asymptotic with its predicted constant.

## 5. The Artin reduction: reject the stated proof, retain a stronger repaired conditional version

There are two distinct mistakes/omissions in §4.4.

First, complete splitting in `K_q(μ_M)` forces p≡1 mod M. For an arbitrary chosen class u, it does **not** count primes which split in K_q and satisfy p≡u mod M. In the usual quadratic-nonresidue class it can even select a disjoint set. The relevant Frobenius has identity restriction to K_q and prescribed restriction to Q(μ_M); it is not generally the identity of the compositum. Positivity for the compositum's prime-ideal sum cannot just be reused to count it. A suitable twisted/Chebotarev estimate would require its own derivation.

Second, suppose a cutoff Y is removed by choosing p≠1 mod each odd q≤Y, as well as (a/p)=−1. A single resulting class has density 1/φ(M_Y), which can decay exponentially in Y. The global tail O_a(1/Y) need not be smaller than its reservoir. The weaker hypothesis written in the report, `liminf P(G | p≡u mod M)>0`, gives an unspecified number depending on M,u. Changing Y changes M and this unknown number. One cannot choose Y after seeing it while pretending the progression remains fixed. The report supplies no quantitative inequality closing that circle. This is a proof failure, not a counterexample to Artin or to a possible stronger implication by some other method.

**Repair using full progression PD, without any nonabelian conditioning.** Assume additionally that for every fixed reduced progression u mod M, the PD law is the same PD(1) law as for all primes. The common limiting probability c(θ)>0, not merely unknown positivity, is sufficient. Here is a proof for every single admissible integer a with |a|≥2.

Use the actual upstream lemma `alg:quadratic-progression` to choose M0=8∏_(odd ℓ|a)ℓ and a reduced class u0 such that (a/p)=−1 throughout that class and u0≠1 mod every odd ℓ|M0. This handles negative squares and odd perfect powers as well as ordinary nonsquares. The lemma's proof explicitly constructs such a class by quadratic reciprocity; it is not an assumption that every desired Frobenius class is an arithmetic progression.

For fixed Y beyond q0(a) and all prime factors of M0, let

`M_Y = M0 ∏_(3≤q≤Y, q∤M0) q`.

Retain **all** reduced classes modulo M_Y lying over u0 modulo M0 and avoiding residue 1 at every newly adjoined q. Their union R_Y has prime density

`w(Y) = [1/φ(M0)] ∏_(3≤q≤Y, q∤M0) (q−2)/(q−1) ≍_a 1/log Y`.

For completeness, compare each factor with 1−1/q: the quotient is 1−1/(q−1)², whose infinite product over odd primes converges to a positive number. Mertens' product estimate supplies the asserted size. All odd index divisors q≤Y are impossible because q∤p−1, and 2 cannot divide the index because a is a quadratic nonresidue.

For each fixed Y the union contains finitely many fixed classes. Full progression PD, summed over those classes, yields

`#(G(x)∩R_Y)/N(x) → c(θ)w(Y)`.

The global middle-range bound from (S) loses at most `C_a/Y+o(1)` in relative density, and the Q exception is o(1). Choose Y sufficiently large that `C_a/Y < c(θ)w(Y)/2`, possible because Y/log Y→∞. **Then fix Y and M_Y, and only then let x→∞.** Positive lower density remains, and every remaining index is 1. No growing-modulus PD theorem, no splitting estimate inside an arbitrary progression, and no Chebotarev-conditioned PD are used.

Thus the answer to the stated dichotomy is nuanced: unconditioned PD alone does not supply the required small-prime avoidance; the report's qualitative progression-positivity argument is incomplete; but **full PD in each fixed progression suffices** for this single-base positive-density reduction. Chebotarev-conditioned PD is an alternative stronger input, not a demonstrated necessity. I have not established progression PD from the pinned unconditioned theorem. Robustness of internal marked estimates under twists is a separate contract-verification problem and cannot be silently inferred from the theorem's marginal law.

## 6. Primary literature and novelty limits

Searches targeted “bounded residual index”, “bounded index” with Artin/density, “nearly primitive roots”, fixed-base average multiplicative order, and unconditional small-index distributions. Results from forums and aggregators were only search leads; the conclusions below use the primary works cached in the assigned source directory.

1. **Kurlberg–Pomerance**, *On a problem of Arnold: The average multiplicative order of a given integer*, Algebra & Number Theory 7 (2013), Theorem 2 and §1.1, gives a GRH-conditional prime-average asymptotic for fixed rational g≠0,±1. Theorem 6's small-order tail bound is also conditional on GRH. Page 985 explains an unconditional upper bound and contrasts the fixed-base problem with base-averaged results. These do not supply B's unconditional-given-corpus lower bound. B1 has the right magnitude but is weaker than their conditional asymptotic. Their discussion distinguishes Arnold's all-moduli problem from prime averaging. [Publisher PDF](https://msp.org/ant/2013/7-4/ant-v7-n4-p08-p.pdf). SHA-256 `b50549022fbe8f6d6139fbb7e440dc79c4cefbb908b0fb6b09375cf6813e09cf`.

2. **Kurlberg–Pomerance**, *On the period of the linear congruential and power generators*, §4, Lemmas 19–20, gives a positive proportion with ord_p(e)>p^0.677 for fixed e≥2. The proof uses the same elementary short-product exception for a large factor of p−1; hence that part of the proposed method is established prior art. It also directly contradicts round 1's historical claim that Baker–Harman's 0.677 only supplies infinitely many primes: Lemma 19 explicitly states positive proportion. This does not imply bounded index. I make no claim here that 0.677 is the current optimal exponent. [Author PDF](https://math.dartmouth.edu/~carlp/PDF/par11.pdf). SHA-256 `81ce6bfc13f99657ea3bb439b52f1e5599b092464cc31514d4197313adfbd0f3`.

3. **Goldmakher–Martin–Péringuey**, *Refinements of Artin's primitive root conjecture*, arXiv:2502.19601v1, Theorems 8.1/8.8 give unconditional upper bounds for cumulative small values of index-factor statistics; Theorems 8.2/8.11 give lower bounds for their expectations. These have the opposite useful direction from a lower density of bounded index. Their truncated-statistic results also do not control all large index prime factors. This check found no duplicate of B. [Primary manuscript](https://arxiv.org/html/2502.19601v1). HTML SHA-256 `593a558413a27081cb3de4c6044bb9f126ff5c0831988e128e429faa7bdaeefd`.

4. The report's reference “Luca–Shparlinski; arXiv 1509.03768” conflates sources: **1509.03768 is Sungjin Kim**, *On the Order of a modulo n on Average*. Its abstract averages over bases and integer moduli. Correct the authorship and do not cite it as a fixed-base prime-average result. [arXiv record](https://arxiv.org/abs/1509.03768). Cached-record SHA-256 `fb4cabb28cbf9ca6502e24e0794a58264f142995f43c7809be31364c0072f528`.

The accepted corpus's primitive-root theorem already contains the two index-divisor ranges, Kummer descent, smoothed splitting estimate, and product-divisor exception. B replaces its thin controlled-predecessor construction by a positive-proportion PD reservoir and allows a bounded contribution from finitely many small primes. This is a clean synthesis and a meaningful conclusion, but **(S) itself is already displayed in the accepted source**; it must not be marketed as a newly invented analytic estimate.

No unconditional pre-corpus fixed-base positive-density bounded-index theorem was found in this targeted pass. This is positive novelty evidence, not a proof that no such theorem exists. I did not independently re-audit the MathDB importance label. The parent's success gate must decide whether this synthesis is sufficiently nonroutine; correctness and absence of a located duplicate do not by themselves discharge that requirement.

## 7. Finite verification, including limitations

Reproduction: `python3 frontier/experiments/i02_arithmetic_r2/check.py`. Full output is `frontier/experiments/i02_arithmetic_r2/results.json`.

- Re-ran the original test at x=200000 for a=2,−3,12: good counts 6388, 6389, 6382; zero violations. Their common B is 1004566331767387989600, exceeding every tested p−1. Thus the original numerical check i≤B is vacuous; the simultaneous prime-factor check still tests part of the logic.
- Added an independent exact-threshold test at x=1000,10000,200000, with 18 bases ±2,±3,±4,±8,±9,±12,±16,±27,±64. Used θ=7/20, Y=3, k2=3, k3=2, so B=12 is nonvacuous. Comparisons Q^20>x^13 avoid floating-point threshold ambiguity. Checked the cyclic-group index criterion at each prime divisor, Q∤m, the product-divisor implication, and i|12 outside the three exceptions. Across 54 base/dyad cases: 86232 surviving base-prime instances, zero violations.
- Independently verified 2430 multiplicative orders by repeated multiplication rather than the factor-stripping routine.
- Enumerated reduced residues modulo 36: E3 union density 7/12, versus the sum 2/3. This is a finite CRT counterexample to the asserted equality.
- Recorded finite progression-union masses versus the 1/Y tail and the logarithm of φ(M_Y), illustrating why using all classes changes the budget. The proof is the product calculation in §5, not those numerical values.
- Rechecked the QRH geometry identity on 221 exact rational grid points.

**None of these checks tests the asymptotic at θ<10^-6, the zero-free theorem, (S), PD convergence, or novelty.** The tests are implementation/finite-logic checks only. No attempt is made to extrapolate the empirical fractions to the theorem's tiny exponent.

## 8. QRH and idoneal side claims: limited review, separate verdict

QRH file: `preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`, Git blob `268c4e3206d460c617d3d2129742a72b831b3def`, SHA-256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.

I inspected equations `old-eq:5.1`, `eq:stage-high-exponent`, and the definition of α in §`sec:selection`. The algebraic identity σ0=11/12−ℓ/4 follows from the displayed geometry and low/Mellin exponents. The source explicitly separates dynamic κ from the fixed sixth-power slope α=5/6; replacing α by 3/4 merely because an improved zero-free ceiling is known is not justified. These support the decision not to claim a bootstrap theorem.

The claimed numerical global optimum near ℓ=0.166838 is a coarse scan, not a certificate over a continuous parameter region. I did not reproduce or certify that full optimization. Likewise the expression −1/4+5ℓ/4+b/6−bδ/2 under the stipulated ideal row counts yields the formal 13/15 floor as b,δ↓0, but only within the retained formulas and parameter restrictions. It is not a universal impossibility theorem for all variants of a two-representation method. Neither side observation is an accepted new theorem.

For idoneal numbers, the reduced-form obstruction is plausible and can be justified locally: for odd p<√n with p∤n and (−n/p)=1, choose b even with b²≡−4n mod4p and |b|≤p. The primitive positive form (p,b,(b²+4n)/(4p)) is reduced and its last coefficient exceeds p. The ambiguous reduced-form alternatives b=0 or |b|=p force p|n; equality of the outer coefficients is impossible. Thus the form is nonambiguous, contradicting the standard exponent-two class-group characterization of an idoneal n. This validates the asserted obstruction once that characterization is supplied.

I did **not** verify the claimed effective L(1,χ) constant, the numerical scale e^170, or a complete certified cutoff/search. Round 1 supplies no such computation, and this review does not promote it. No idoneal classification or additional finding is accepted.

## 9. Required revisions and outstanding objections

1. Accept B's proof only with E3≤, explicit strict error margins, the empty-set case, and the correct B(A,η) density quantifier. A polished version can use §3 directly.
2. Retain the all-q derivation of (S) from the lemmas, including large-q qualification for perfect powers, rather than citing the narrow proposition outside its range.
3. Correct or remove §4.4. The repaired conditional theorem in §5 needs full fixed-progression PD (or an explicitly sufficient quantitative lower bound), which has not been derived from the pinned marginal theorem.
4. Correct the 0.677 historical statement, the Kim citation, and the description of B1 as a prime-average magnitude result.
5. Keep novelty and the nonroutine/significance success gate open to parent judgment. This review certifies the repaired deduction, not an unconditional external-literature priority claim, an Artin resolution, or the exact endpoint density for one fixed B.

No unresolved mathematical gap remains in the repaired formal Theorem B/B1 proof given the stipulated accepted contracts. The progression hypothesis and the novelty/success-gate assessment remain unresolved and must not be merged into that correctness verdict.
