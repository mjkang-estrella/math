# W001 — Classical factoring baseline ledger

Date: 2026-10-07, America/Los_Angeles. Bounded independent literature pass; primary sources checked online, including selected 2024–2026 work. This is not an exhaustive survey or an independent proof audit of every cited paper. No factoring experiment was run. **Verified new algorithmic improvement: NONE.** Disposition: baseline corrected and research questions narrowed; no new algorithm accepted.

The assigned baseline lens supersedes the request for speculative mechanism cards. This report does not develop or rely on H002 or other agents' hypotheses. Project instructions and the specification were read; no shared code, Lean, checkpoint, or other report was changed.

## 1. Units and claims that must remain separate

Throughout, **N is the integer being factored**, n = floor(log2 N) + 1 is its input length, and p is a prime divisor, usually the smallest. Natural logarithms occur in

\[
L_N[\alpha,c]=\exp((c+o(1))(\ln N)^\alpha(\ln\ln N)^{1-\alpha}).
\]

Thus N^(1/5+o(1)) = 2^(n/5+o(n)), whereas L_N[1/3,c] = exp((c(ln 2)^(1/3)+o(1)) n^(1/3)(ln n)^(2/3)). Both exceed every fixed polynomial in n. A smaller fixed exponent of N is an exponential improvement in n, but remains asymptotically slower than an L_N[1/3,c] bound. Comparisons must retain the latter's heuristic status.

Use bit operations, with M(w) denoting multiplication cost for w-bit integers. Modular exponentiation with an e-bit exponent costs O(e M(n)) up to reduction factors, not O(1). Exponents with small descriptions can still have exponentially many bits. Size-dependent advice, factor-base construction, polynomial selection, prime generation, lattice construction, relation filtering, algebraic square roots, and memory traffic belong inside the accounting.

A verified factor is a certificate of correctness, not a bound on finding it. A per-input expected-time theorem averages over algorithmic randomness, not over N. If an always-correct algorithm has E[T(N)] ≤ F(N) uniformly, truncating after 3F(N) gives success at least 2/3 by Markov's inequality; this remains an F(N)-scale algorithm. A heuristic expected estimate supplies no such theorem. For independent repeated attempts of expected cost C(N) and success probability s(N), the restart cost is C(N)/s(N). Neither s(N) nor independence may be silently assumed.

## 2. General classical baselines

**GNFS: the standard heuristic comparison.** Buhler–H. W. Lenstra–Pomerance's general number field sieve predicts L_N[1/3,(64/9)^(1/3)], with constant approximately 1.923. It builds compatible rational/algebraic relations, sieves for smooth values, solves a sparse parity system, constructs square roots, then takes gcds. Smoothness predictions for the actual structured values and productive dependencies are hypotheses, not an all-input expected-time proof. The scope is general integers after elementary preprocessing. [Original GNFS chapter, primary publisher record](https://link.springer.com/chapter/10.1007/BFb0091539); [Pomerance's primary account, especially §§6–9](https://math.dartmouth.edu/~carlp/PDF/paper99.pdf).

**Do not call 1.923 the sharpest theoretical heuristic NFS constant.** Coppersmith's multiple-polynomial modification gives about 1.902; the exact optimized constant is ((92+26√13)/27)^(1/3). Its polynomial multiplicity, generation and enlarged algebraic factor bases are part of the optimization. His separate amortized-precomputation estimate near 1.639 is not the cold cost of factoring one arbitrary input. [Coppersmith, 1993, §§3–4](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf); [Lee–Venkatesan, Remark 4.31, exact constant](https://arxiv.org/html/1805.08873v1).

**Quadratic sieve: heuristic general factoring, L_N[1/2,1].** Its smaller square residues improve smoothness yield; sieving avoids trial-dividing every candidate by every factor-base prime. The modern estimate includes sparse linear algebra. It does not follow merely from the existence of a parity dependency. [Pomerance, *Smooth numbers and the quadratic sieve*, 2008](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf).

**Proven randomized general factoring.** Dixon establishes expected exp(O(√(ln N ln ln N))) work by random-square relations. Lenstra–Pomerance subsequently prove complete factorization of every positive integer in expected L_N[1/2,1] time, without GRH, using class-group relations with multipliers and analytic control of exceptional characters. This is the strongest unconditional general randomized baseline verified in this pass; no claim is made that the search excludes every newer improvement. The theorem includes finding factors, not just relations. [Dixon, 1981](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf); [Lenstra–Pomerance, 1992, main theorem and §§10–12](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).

**The rigorous-randomized-NFS distinction.** Lee–Venkatesan's Theorem 2.1 obtains a square congruence in expected L_N[1/3,(64/9)^(1/3)] time. Their Theorem 2.3 obtains a useful congruence for Blum semiprimes, p ≡ q ≡ 3 mod 4, conditional on character-decorrelation Conjecture 7.82. Therefore this paper cannot replace the preceding unconditional complete-factoring entry. [Lee–Venkatesan, 2018, Theorems 2.1/2.3 and §7](https://arxiv.org/html/1805.08873v1).

**Proven deterministic worst-case general factoring.** Harvey's exponent 1/5 result and Harvey–Hittmeir's refinement give

\[
O\left(N^{1/5}(\log N)^{16/5}/(\log\log N)^{3/5}\right)
=O\left(2^{n/5}n^{16/5}/(\log n)^{3/5}\right)
\]

bit operations for full factorization, in a fixed finite-tape Turing model. The progression through Pollard–Strassen's exponent 1/4 and Hittmeir's 2/9 is historical; none is a polynomial-in-n bound. The semiprime core is accompanied by a reduction handling additional prime factors and repeated factors. [Harvey, 2020/2021](https://arxiv.org/abs/2010.05450); [Harvey–Hittmeir, 2021 preprint / 2022 publication, Theorem 1.1](https://arxiv.org/html/2105.11105).

**Space and total-work ledger.** Standard factor-base sieve analyses use approximately B relations/columns up to polynomial factors. Sparse matrix algorithms cost roughly B^(2+o(1)) field operations and store sparse data of size B·poly(n); replacing this with dense elimination can change the leading estimate. QS balances B = L_N[1/2,1/2]. Standard GNFS balances B = L_N[1/3,(8/9)^(1/3)]. These are algorithm/parameter descriptions, not lower bounds, and polynomial factors hide coefficient and index widths. Algebraic square-root reconstruction can involve much larger intermediate representations than a single residue modulo N. [Pomerance, 2008](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf); [Coppersmith, §2 cost analysis](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

The class-group entry does not assert polynomial space: conservatively, a bit-machine computation cannot allocate more new bits than its charged steps, giving an expected-space bound no larger than its expected-time bound, not a tight space theorem. Deterministic collision/product-tree methods also have substantial stored lists. Harvey states O(N^(1/5) log^(11/5) N) space for his original algorithm, without supplying its detailed analysis. This report does not transfer that precise logarithmic bound to later variants. [Harvey, Theorem 1.1 discussion](https://arxiv.org/html/2010.05450).

## 3. Special-factor and special-input baselines

**Pollard rho.** Iterating a cheap map and taking gcds of collisions gives the familiar heuristic O(√p) iterations, hence approximately 2^(n/4) iterations for balanced semiprimes. A random-map birthday argument does not establish that each chosen polynomial iteration modulo every unknown p behaves that way. Charge modular multiplication, gcd batching, seed/map changes and failed cycles. Cycle detection permits O(n)-bit state apart from implementation buffers. It is a useful small-factor baseline, not a rigorous general subexponential theorem. [Pollard, 1975](https://pages.cs.wisc.edu/~cs812-1/pollardrho.pdf).

**Pollard p−1.** First check gcd(a,N). For a unit a, stage one uses E = lcm(1,…,B), computes a^E mod N and gcd(a^E−1,N). A sufficient condition for success on N = pq is p−1 | E and a^E not congruent to 1 modulo q. “B-smooth” alone is insufficient if a prime-power divisor exceeds the exponent covered by E. Since log E = O(B), modular powering costs O(B M(n)), plus prime/exponent generation; a sieve costs about O(B log log B) operations and its storage must be counted. This elementary accounting is conditional on the stated factor property and separating base. Lenstra's original ECM paper explains the p−1 antecedent and replaces its fixed group by varying curves. [Lenstra, 1987, introduction](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf).

**ECM.** The conjectural small-factor bound is L_p[1/2,√2]·poly(n), not L_N[1/2,√2]. At p ≈ √N this becomes L_N[1/2,1]·poly(n). The missing density assertion concerns smooth group orders near p, rather than uniformly random integers across an entire large interval. Curves, scalar multiplications, gcds, unsuccessful curves and the schedule for unknown p must be charged. The original method can use O(log N) storage; memory-heavy second stages are optional changes needing their own accounting. [Lenstra, *Factoring integers with elliptic curves*, especially Conjecture 2.10 and §2.11](https://annals.math.princeton.edu/1987/126-3/p09).

**SNFS.** Negligible polynomial coefficients for suitable special integers reduce the heuristic constant to (32/9)^(1/3) ≈ 1.526. Having a convenient small-coefficient representation is part of the scope. A method which has to find such a representation for arbitrary N must charge and justify that search. [Pomerance, 1994, §9](https://math.dartmouth.edu/~carlp/PDF/paper99.pdf).

**Close factors / partial information.** For odd N = pq, Fermat's search takes (p+q)/2 − ceil(√N) + 1 trials. Writing Δ = q−p, the real gap is

\[
(p+q)/2-\sqrt N=\frac{\Delta^2}{2(p+q+2\sqrt N)}.
\]

Thus closeness can explain very fast examples without any general improvement. This is an exact algebraic identity, not a timing fit. Coppersmith's small-root methods also exploit sufficiently accurate partial information; known factor bits or a narrow supplied interval change the input contract. Finding that information must itself be priced. [Coppersmith, 1997, original research record](https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities).

## 4. Selected 2024–2026 results checked

**2024 — power-divisor scope.** Hales–Hiary's *A generalization of Lehman's method* gives algorithms which return a nontrivial divisor **or certify r-power-freeness**, with r > 1. Theorem 1.2 states O(N^(1/(3+2r)) log^(16/5) N) time and space. A squarefree semiprime may produce only the second output, so the small exponent does not improve general splitting. The paper also explicitly compares against Harvey–Hittmeir's earlier N^(1/(4r)+o(1)) power-divisor algorithm. [Published 28 October 2024, Theorems 1.1–1.2](https://link.springer.com/article/10.1007/s11139-024-00959-7).

**2025 — balanced-semiprime logarithmic improvement.** Gao–Feng–Hu–Pan use the second vector of a rank-3 reduced lattice in collision handling. For N = pq with p,q = Θ(√N), their stated bound is O(N^(1/5) log^(13/5) N / (log log N)^(3/5)). This improves a logarithmic factor in that scope, not the N exponent. Their power-divisor and sums/differences-of-powers results have their own promises. Metadata lists a November 2025 revision and publication in Mathematics of Computation. The primary abstract and indexed Theorem 1.1 were checked; the full proof was not independently audited. [Paper 2025/1004](https://eprint.iacr.org/2025/1004).

**2025 — conditional exponent 1/6.** Umans–Wang's divisor-cover construction is a conditional research route, detailed below. It is not an established exponent improvement. Their polynomial-factorization parameter also must not be confused with the bit length of an integer input. [November 2025 preprint](https://arxiv.org/abs/2511.10851).

**2026 — large order, not order recovery.** Harvey–Hittmeir v2, 5 June 2026, proves that for N ≥ 3 and 1 ≤ D < N−1 one can deterministically output either a factor or an element α with ord_N(α) > D in

\[
O\left(D^{1/2}\frac{\log D}{\sqrt{\log\log D}}\log N\right)
\]

bit operations, with small logarithms regularized. No lower threshold such as D ≥ N^(1/6) remains. Their stated, but not detailed, space estimate is O(D^(1/2) log N / √(log log D)). This does not compute ord_N(α), find a short discrete logarithm for free, or necessarily output a factor. [Theorem 1.1](https://arxiv.org/html/2601.11131v2).

Oznovich–Volk's SODA 2026 result had D ≥ N^(1/6) with D^(1/2+o(1)) time. Nir's independent May 2026 preprint has D > exp(√(2 log N log log N)) with D^(1/2+o(1)) time, plus a slower arbitrary-D variant. These are distinct prerequisites and should not be conflated with the stronger June theorem. [Oznovich–Volk](https://epubs.siam.org/doi/epdf/10.1137/1.9781611978971.229); [Nir](https://arxiv.org/abs/2605.09592).

**2026 — supplied-parameter trap.** Blake's *Rational Base Descent* advertises O(log³ N) factor isolation with the correct rational-base parameters for a structured factor and additional size restrictions. Its abstract explicitly separates parameter search and balanced-RSA applicability. This is not an N-only polynomial-time algorithm; the report does not promote the abstract to a checked bit-complexity theorem. [May 2026 primary preprint](https://arxiv.org/abs/2605.08846).

## 5. Actual quantum results, separately

Shor gives polynomial-time quantum factoring, including order finding and efficient classical reconstruction. Treating the quantum order-finding primitive as a free classical call removes the essential computational work. This is a theorem about a different computation model, not evidence of a classical implementation. [Shor, full paper](https://arxiv.org/abs/quant-ph/9508027).

Regev's original multidimensional algorithm uses O(√n) independent circuits of roughly n^(3/2) gates each, followed by polynomial classical processing, under a number-theoretic heuristic. [Regev, original preprint](https://arxiv.org/abs/2308.06572).

Pilatte removes the number-theoretic assumption for modified algorithms. Theorem 1.1 in the checked v3, revised 24 August 2026, states O(n^(3/2) log³ n) gates and O(n log³ n) qubits per circuit, O(√n) calls, polynomial classical processing, and constant success probability. Consequently aggregate quantum gate work is O(n² log³ n), before amplification; n^(3/2) is not the complete gate count. Generation of the random small primes and classical lattice processing are inside the construction. These are ideal algorithmic circuit bounds, not fault-tolerant physical-qubit or laboratory factoring records. [Pilatte, 2024–2026, Theorem 1.1 and §4.3](https://arxiv.org/html/2404.16450v3).

## 6. Three ranked research bottlenecks

Ranking is by suitability for a bounded, falsifiable next pass, not a predicted chance of polynomial factoring. All are existing research gaps, not novelty claims.

**1. Implicit simultaneous collisions after large-order construction.** Harvey's Proposition 4.2 charges, suppressing polynomial logarithms,

\[
r+m+N^{1/2}/(r^{1/2}m).
\]

The requisite small-factor search contributes (N/r)^(1/4). The 2026 theorem can construct an element of order exceeding m for roughly √m work. This leaves target construction/collision extraction as the promising part to change. Harvey already identifies a full square-root speedup of Lehman's search as a possible route to exponent 1/6. [Harvey, §3 and Proposition 4.2](https://arxiv.org/html/2010.05450); [Harvey–Hittmeir, 2026](https://arxiv.org/html/2601.11131v2).

Own cost audit: put r=N^ρ and m=N^μ. The displayed cost envelope has exponent

\[
\max\{(1-\rho)/4,\rho,\mu,1/2-\rho/2-\mu,\mu/2\}.
\]

Its minimum is 1/5, achieved at ρ=μ=1/5. Indeed an envelope ≤ N^t requires ρ,μ ≤ t and 1/2−ρ/2−μ ≤ t, forcing t ≥ 1/5. This proves only that reoptimizing these charged terms cannot certify a smaller exponent; it is **not a lower bound on factoring or on the actual algorithm**.

Hypothetically replacing the r-scale target work by r^θ, while preserving all coverage/extraction guarantees, balances at ρ=1/(4θ+1), μ=θ/(4θ+1). For θ=1/2 this gives N^(1/6+o(1)) = 2^(n/6+o(n)), with no claimed heuristic advantage over GNFS. **Unsupported primitive:** exploit the implicit target structure without enumerating it, and recover a proper factor even when collisions also occur modulo N. Materializing Θ(r) residues or coefficients immediately falsifies that proposed implementation's √r cost; reducing residues modulo N controls width but does not remove their count.

**2. Constructible prefactored divisor covers.** Umans–Wang use sets S,T with |S|,|T| ≤ R^β, magnitude ≤ exp(R^α), generalized-progression structure, and divisibility coverage of every i ≤ R by a nonzero difference s−t. Integer factoring additionally requires efficiently outputting the prime factors of each difference. With R ≍ √N their conditional exponent is max(α,β)/2; α=β=1/3 would yield 1/6. Their conjectures say “infinitely many” R. [Conjectures 3.3/5.1 and Theorem 5.5](https://arxiv.org/html/2511.10851).

Project acceptance obligations: give one finite construction, charge its search, provide usable scales for every input, and do not turn prefactoring into an oracle. R is exponential in this report's n. At α=β=1/3, a listed element can have Θ(N^(1/6)) bits; writing all elements outright can cost N^(1/3), already too much. The intended compressed/modular representation therefore matters. Cheapest falsifier for a candidate construction: a missed divisor i, an uncharged construction step, or a leaf-difference factorization slower than the advertised bound. A finite cover alone does not establish an asymptotic family.

**3. Cheap relations whose square roots actually separate factors.** The randomized-NFS gap in §2 supports targeting a per-input lower bound on useful output probability, rather than merely more square congruences. [Lee–Venkatesan, §7](https://arxiv.org/html/1805.08873v1).

For any proposed sampler, explicitly bound

\[
\frac{T_{\rm setup}+T_{\rm generation}+T_{\rm filtering}+T_{\rm linear\ algebra}+T_{\rm roots}}{s_N}.
\]

A rigor-only gain would replace the unconditional L_N[1/2,1] baseline by an L_N[1/3,c] theorem; beating the heuristic frontier additionally requires a better complete exponent/constant. **Unsupported steps to expose:** smoothness law for generated values, rank/independence of relations, successful root construction, and a lower bound on s_N. Cheapest falsifier for a concrete sampler is an explicit infinite bad family or finite counterexample to its claimed all-input success bound, with complete dependency enumeration only on tiny cases. Rank growth alone is not success: x=y always supplies a square congruence and never a proper factor. This direction remains mathematically promising but is less bounded than item 1.

## 7. Recommended next step and reviewer tripwires

**Recommended next pass: one focused implicit-product lemma, no infrastructure.** Take r=ceil(N^(1/3)), m=ceil(N^(1/6)), α of order exceeding m, and the Lehman targets

\[
t_{a,b}=\alpha^{aN+b-\lceil\sqrt{4abN}\rceil}\pmod N,
\qquad 1\le ab\le r.
\]

After removing factors up to (N/r)^(1/2), ask for a representation permitting collision tests between these targets and α^i, 0≤i<m, including proper-factor extraction, in N^(1/6+o(1)) **total bit work and space**. The obvious polynomial P(X)=∏(X−t_(a,b)) has Θ(r log r) listed factors; building its coefficient vector does not meet the target. The precise challenge is an implicit recurrence or product evaluation, with generation and gcd=N recovery charged.

Bound the investigation to one proposed recurrence and one proof attempt. Reject the proposed implementation if it enumerates all (a,b), requires an unknown p/order, loses the Lehman coverage guarantee, or exceeds the full bound. If a recurrence is actually proposed, a later optional tiny exhaustive check should compare its products and extracted factors with direct enumeration, with each run capped at 60 seconds. Failure to discover a recurrence is inconclusive, not a proof that none exists. No recurrence, experiment, or new complexity theorem is claimed in this report.

Reviewers should catch these unsupported promotions:

- Replacing log N by N, suppressing exponent bit width, or counting an unbounded product as one operation.
- Calling standard GNFS rigorous, treating its conventional 1.923 constant as unbeatable, or omitting Coppersmith's polynomial multiplicity/preprocessing.
- Treating any square congruence, relation-space kernel, large-order element, approximate factor, or lattice short vector as an already available factor.
- Calling an element of order >D an algorithm computing its order; calling D=poly(n) a general splitter.
- Describing p-dependent rho/ECM bounds as N-only guarantees, or counting only successful seeds/curves.
- Reporting power-freeness as factorization; generalizing balanced-semiprime, supplied-bit, close-factor, or structured-input performance to arbitrary composites.
- Calling a conditional exponent 1/6, an existential cover, or infinitely many favorable sizes a uniform all-input theorem.
- Quoting n^(3/2) quantum gates per circuit as total factoring cost, or moving the quantum sampler into a classical oracle slot.
- Claiming novelty because a finite search found no match. Known components can still yield progress, but the changed primitive and full bound must be identified and independently reviewed.

The baseline itself is the result of this pass. The search found relevant recent changes to scope, logarithmic factors, subroutines and quantum rigor, but did not verify a new general classical factoring improvement for this project.
