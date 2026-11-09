# W001 — Classical structure in order recovery and interference

Bounded independent ideation pass, 2026-10-07 America/Los_Angeles. **Verified factoring improvement: NONE.** Four mechanisms are specified below; none currently supports an all-input polynomial classical factoring claim. The most useful positive result is an explicit conditional reduction from short binary recurrences to a verified order multiple, without an auxiliary integer-factorization oracle. Its concrete raw-bit cutoff failed a small diagnostic. The remaining untested direction is contraction of output marginals after exact cancellations, with every intermediate width charged.

Read: `AGENTS.md`, `docs/SPECIFICATION.md`, `README.md`, `RESEARCH_LOOP.md`, and `research/STATE.md`. The present assignment supersedes the checkpoint's H002 next action; H002 and other researchers' proposals were not inspected. No shared harness, Lean, state, or other agent output was changed. The only supplementary file is the permitted diagnostic `W001-orders-screen.py`. No delegation, installation, commit, publication, or scheduling occurred.

## Shared accounting and comparison

Input is N alone; n = bitlength(N). A base a is sampled using O(n) random bits per draw, and gcd(a,N) is checked first. A proper gcd is already an answer. Even inputs and perfect powers have ordinary polynomial preprocessing. Orders, factors, CRT coordinates, and family labels below are analytical quantities, never solver inputs.

Write M(b) for multiplication and modular reduction on b-bit operands; the conservative bound O(b²) suffices throughout. One modular power with an O(n)-bit exponent costs O(n M(n)); sequential powers cost O(M(n)) each. Exponents in Fourier queries have O(n) bits even when their range is exponential. Memory is counted in bits, including precision and index widths.

An order multiple R is enough for splitting: verify a^R = 1 mod N, write R = 2^t u with u odd, and inspect the successive squares of a^u. A nontrivial square root of one gives a gcd factor. This costs O(bitlength(R) M(n)) plus gcds, without factoring R. Some bases still fail. If a candidate only works on some bases, its needed assumption is a lower bound δ(N) on the **joint** event that its structural condition holds and the base splits N. Multiplying unrelated success fractions is unjustified. A worst-case cost C per attempt becomes O(C δ⁻¹ log(1/ε)) under such a proved bound; unbounded retries do not give a bounded-error theorem. The classical reduction and quantum Fourier order recovery are prior art in [Shor's original paper](https://arxiv.org/abs/quant-ph/9508027).

For comparisons, adaptive baby-step/giant-step order finding takes O(√r) group operations and stored group elements up to logarithmic factors, where r = ord_N(a); generation, comparisons, and n-bit arithmetic must be added. See the primary analysis in [Sutherland's thesis, §3.2](https://math.mit.edu/~drew/sutherland-phd.pdf). This is a standard baseline, not an asserted optimal generic bound; that thesis also develops improvements. Improving full-order recovery does not automatically beat factoring: the general number field sieve has heuristic exp(O(n^(1/3)(log n)^(2/3))) complexity, as analyzed by [Buhler–Lenstra–Pomerance](https://link.springer.com/chapter/10.1007/BFb0091539). An unconditional deterministic comparison already available is [Harvey–Hittmeir's N^(1/5) polylog(N) bound](https://arxiv.org/abs/2105.11105). These are comparison points, not a claim that this bounded search established a complete current bibliography.

## A. Recover an order multiple from binary recurrences

**Primitive and algorithm.** Generate x_t = a^t mod N by repeated multiplication. For each bit j, form b_j(t) = bit_j(x_t) over F₂. With a public cutoff s, collect 2s terms and apply Berlekamp–Massey to every stream. Interpret the resulting polynomials as forward-shift annihilators C_j(T), and form C = lcm_j C_j, of degree D ≤ ns. Reject malformed candidates with a zero root. Factor C over F₂, including multiplicities:

    C(T) = product_i f_i(T)^(e_i),   d_i = degree(f_i),
    E = 2^ceil(log2(max_i e_i)) * lcm_i(2^(d_i) - 1).

For C = 1 set E = 1. Verify a^E mod N = 1 and perform the square-root splitting procedure above. A failed verification is a failed attempt, not permission to substitute the true period. Polynomial factorization here is over the fixed field F₂; no integer 2^d − 1 is factored.

**Why the reduction works, conditionally.** If the infinite bit streams really have linear complexity at most s, 2s terms recover their recurrences. Every nonzero root of an irreducible degree-d polynomial lies in F_(2^d)^*, so its order divides 2^d−1. In characteristic two the prefactor 2^ceil(log2(max e_i)) handles repeated roots. Thus C divides T^E−1. Every output bit repeats after E; their joint encoding is injective, hence a^(t+E) = a^t mod N and r divides E. Also bitlength(E) ≤ D + ceil(log₂ D) + O(1), since the sum of distinct irreducible degrees is at most D. A short recurrence therefore gives a short *multiple*, even when computing the exact orders of its roots would introduce another hard problem. This is a derivation here, not a novelty claim.

**Complete conditional cost.** Generating 2s residues and bits costs O(s M(n)+ns); straightforward synthesis costs O(ns²) binary operations. A deliberately conservative deterministic bound for lcm construction, fixed-field polynomial factorization, multiplicities, and E construction is O(D⁴). Verification and splitting cost O((D+log D)M(n)), with ordinary gcd factors. Space is O(ns+D²+n) bits using a dense finite-field linear-algebra implementation. Thus one attempt costs

    O(s M(n) + ns² + D⁴ + (D+log D)M(n)),   D ≤ ns.

With s = n² this is, conservatively, O(n¹²) time and O(n⁶) space, **only if the required recurrence bound and joint success probability hold**. It would be an asymptotic gain over the comparison algorithms under those assumptions. As written, the algorithm has no general polynomial success guarantee; allowing s to grow to r reinstates exponential work. Field arithmetic is exact and requires no numerical precision or Fourier sampling oracle.

**Prior art and distinction.** Recurrence recovery is [Massey's shift-register synthesis](https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf); projected recurrences are also central to [Wiedemann's sparse linear algebra](https://www.enseignement.polytechnique.fr/profs/informatique/Francois.Morain/Master1/Crypto/projects/Wiedemann86.pdf). Fixed-field polynomial factorization is [Berlekamp's algorithm](https://onlinelibrary.wiley.com/doi/abs/10.1002/j.1538-7305.1967.tb03174.x). The proposed factoring specialization is to use all residue bits, then construct a verified exponent from factor *degrees* and multiplicities. The unsupported ingredient is low complexity of these explicitly computable observations. Neither BM nor a sparse multiplication circuit supplies it. Working modulo N itself would give the trivial recurrence x_(t+1)=a x_t but would hide order recovery in a root over the unknown composite ring.

**Cheapest falsifier and observed result.** Any finite-prefix linear complexity exceeding s rules out that bound for the corresponding infinite stream. The preregistered cutoff s=n² was tested using 4n² terms, 15 generated balanced semiprimes at sizes 16,20,24,28,32, and four sampled unit bases per modulus. It failed on **59/60 pairs**: 11/12 at 16 bits, and 12/12 at every larger size. No attempts timed out. This is evidence against this exact low-degree proposal; it neither disproves every polynomial bound nor measures a factoring speedup. The sole non-refuted pair is not a confirmed useful family.

An analytical obstruction sharpens the screen: if an odd prime ℓ divides r, some bit recurrence must have an eigenvalue whose order is divisible by ℓ; its irreducible degree is a multiple of ord_ℓ(2). Thus at least one bit has linear complexity ≥ ord_ℓ(2). This follows from injectivity and finite-field root orders, not a black-box factoring lower bound. An efficiently computable encoding with a genuinely smaller joint recurrence would need an additional construction and proof.

**Disposition:** reject the specific universal s=n² raw-bit hypothesis. Retain the order-multiple reduction as a conditional lemma; no general-input algorithm survives this screen.

## B. Random-sign Fourier sampling without storing the work register

**Primitive and algorithm.** Let Q be the smallest power of two at least N². Choose an efficiently evaluable four-wise independent sign hash h on n-bit residues. Define

    f_h(x) = h(a^x mod N),
    A_h(y) = (1/Q) sum_(0≤x<Q) f_h(x) exp(2π i xy/Q).

Parseval gives sum_y |A_h(y)|²=1. Pairwise independence already implies the exact identity

    E_h |A_h(y)|²
      = (1/Q²) sum_(x,x') 1[a^x=a^x' mod N] exp(2π i (x−x')y/Q)
      = P_Shor(y).

Consequently, drawing a fresh h and then one sample from |A_h|² reproduces the desired marginal; no empirical average over exponentially many hashes is needed. The concrete proposal is to recover a k-sparse approximation of A_h using sparse Fourier algorithms, normalize its squared entries, and sample that list. Query f_h by modular exponentiation, not an orbit table.

**Complete proposed gain.** A four-wise independent hash can use a random cubic over F_(2^n), followed by a nonzero binary linear functional. Its seed has O(n) bits; constructing the field with verified irreducibility has expected poly(n) cost, or capped polynomial cost with a failure event. Evaluation has polynomial bit cost H(n). If a k-entry representation has sufficiently small ℓ₂ error η, its normalized squared entries have O(η) total-variation error. Sparse recovery therefore costs

    k * poly(n, 1/η) * (n M(n) + H(n) + M(b))

bit operations and O(k(n+b)+poly(n)) bits of memory, with numerical precision b polynomial in n, log(1/η), and any conditioning parameters actually used by the recovery algorithm. Support generation and probability-list construction are included. Accuracy/conditioning cannot be left as unit-cost real arithmetic. Polynomial k, inverse accuracy, and conditioning would yield a polynomial factoring route. Use per-sample TV error ≤1/(100n²), O(n²) Fourier samples per base, continued fractions with denominator bounded by N, explicit power verification, and ordinary base restarts. These are conservative polynomial repetition budgets, not a claim that one Fourier sample always reveals r.

**Where it fails.** The mixture identity does not produce the inner sampler. For a period-aligned diagnostic transform with Q a multiple of r, A_h has r possible frequencies, and its nonzero coefficients are the r-point Fourier transform of the signs on the orbit divided by r. Four-wise independence gives

    E_h sum_j |A_h(jQ/r)|⁴ ≤ 3/r.

By Markov's inequality, with probability at least 0.9 this sum is ≤30/r. Cauchy–Schwarz then bounds the mass of *any* k frequencies by sqrt(30k/r). Capturing 90% of the mass requires k ≥0.027r on that event. The fourth-moment bound comes by expanding four signs: only paired orbit labels contribute. This calculation is a diagnostic derivation; choosing a period-aligned Q is not a permissible solver step when r is unknown. It shows that even the favorable, leakage-free version lacks the required generic sparsity. The actual power-of-two window also needs an explicit tail bound; non-divisibility by r must not be silently discarded.

Likewise, a bounded-variance sample-mean estimator for an amplitude of typical size r^(-1/2) needs order-r samples for fixed relative accuracy. Uniform samples of x, or exact evaluation of an individual f_h(x), do not provide Fourier length-square samples. A success on r=poly(n) is scoped and competes with direct O(√r) order finding, not general factoring.

**Prior art and distinction.** The sparse transform primitive is [Hassanieh–Indyk–Katabi–Price](https://arxiv.org/abs/1201.2501). General dequantization frameworks already expose their low-rank and sampling-access requirements; see [Chia et al.](https://arxiv.org/abs/1910.06151). This card supplies an explicit factoring-specific random-sign mixture and charges the missing transformed sampler. It does not claim a new Fourier algorithm, or apply an oracle lower bound to arithmetic factoring.

**Cheapest decisive falsifier:** the fourth-moment calculation above rejects the generic sparse-spectrum assumption in the aligned diagnostic case. Any rescue must specify a different inner sampler or a structured hash family with both the exact mixture guarantee and a proved compressible spectrum; selecting convenient hashes without checking mixture bias changes the algorithm.

**Disposition:** reject sparse-spectrum recovery as the proposed general dequantization; retain the exact identity as a diagnostic, not a factoring primitive.

## C. Contract conditional output probabilities after cancelling arithmetic

**Primitive and algorithm.** Uniformly construct a reversible, schoolbook modular-exponentiation circuit from a,N, including computing all a^(2^j) mod N. A conservative gate budget G=O(n⁴) suffices; no compiled gates depending on r are allowed. Use the semiclassical Fourier transform: each next output bit is a phase-basis measurement determined by earlier outcomes. Construct the doubled arithmetic tensor network for the joint probability of an observed prefix. Trace the work output, contract identical Boolean wires and conjugate gate pairs where algebraically valid, and retain the product measurement tensors.

Fix an implementable elimination rule: perform those local cancellations to a fixed point; repeatedly eliminate a variable adding the fewest graph edges, breaking ties by creation index, with low-bit arithmetic wires created first. Record w, the maximum number of binary variables in any intermediate factor. Abort a trial that exceeds a public width cap. Compute the two next-prefix masses, normalize with error control, and draw the next bit. This asks for output probabilities directly; it does not build an MPS approximation of the full state.

**Complete cost and target.** Circuit generation and base powers cost poly(n). Naive deterministic planning is bounded by O(G⁴), including all tie-breaking and graph work. Given its actual elimination order, a marginal contraction costs O(G 2^w M(b)) up to polynomial bookkeeping. For O(n²) full samples, O(n) marginal steps each, one base therefore costs conservatively

    poly(n) + O(G⁴ + n³ G 2^w M(b))

with O(G² + G 2^w b) bits of memory. Here w is the maximum over the required prefixes, not merely the initial state. The polynomial target needs w=O(log n) for the stated efficiently found order and a sufficiently large joint fraction of splitting bases.

Use certified interval arithmetic, allocating unconditional prefix-mass error δ ≤ ε_s/(10 Q log₂ Q). This conservative allocation tolerates small conditioning probabilities; it spends O(n+log(1/ε_s)) precision bits to represent δ, not exponential precision bits. Bounding all path counts by 2^O(G) and charging rounding permits a deliberately conservative b=O(G+n+log(1/ε_s)). Interval widths must be proved, not inferred from floating-point agreement. If a branch cannot be certified at that budget, count a failure. Choose ε_s ≤1/(100n²); charge O(n²) samples, continued-fraction tests, power verification, and base restarts as in B. Exact cyclotomic amplitudes in a degree-Θ(Q) basis would instead carry exponential representation cost; they are unnecessary for this approximate-sampling proposal.

**Known barriers that do and do not apply.** After modular exponentiation, the state is

    Q^(-1/2) sum_(0≤x<Q) |x>|a^x mod N>.

Across the exponent/work partition its Schmidt weights are c_j/Q, where c_j is floor(Q/r) or ceil(Q/r). A Schmidt-rank-D approximation has squared overlap at most D(1/r+1/Q). Near-unit fidelity therefore requires D=Ω(r). This prices the common whole-state low-rank shortcut and agrees with the order-dependent resources of [Wang–Hill–Hollenberg](https://arxiv.org/abs/1501.07644) and the refined entanglement organization in [Dang–Hill–Hollenberg](https://arxiv.org/abs/1712.07311).

That argument does **not** prove output marginals hard: a scalar contraction can sometimes be easy despite a high-rank state. Conversely, writing

    P(y) = Q^(-2) sum_(|d|<Q) (Q−|d|) 1[a^d=1 mod N] exp(2π i dy/Q)

only rewrites an exponential sum. For negative d, the predicate uses the modular inverse of a. Substituting d multiples of the unknown r or granting interval counts floor(B/r) installs the missing order oracle. Indeed, exact counts of positive d≤B with a^d=1 let binary search recover the first such d in O(n) queries.

**Prior art and distinction.** Width-dependent tensor simulation is [Markov–Shi](https://arxiv.org/abs/quant-ph/0511069). [Yoran–Short](https://arxiv.org/abs/0706.0872) already reduce Shor simulation to suitable product-basis measurements of modular exponentiation using the semiclassical Fourier transform. This is consequently not a new simulation reduction. The concrete research question is whether early paired-arithmetic cancellations plus the specified ordering have small *actual intermediate factors* for N-only generated circuits. No such width theorem or measurement has been obtained in this pass. A hypothetical optimal contraction order is not supplied for free.

**Cheapest falsifier.** First measure only the structural elimination widths; do not run a numerical simulator. For a registered cap w≤2 ceil(log₂ n)+4, any generated prefix network exceeding the cap rejects that bounded implementation. A small observed width must still be paired with a uniform bound, precision analysis, and success theorem. A large width for this rule rejects this rule, not every contraction representation or classical factoring algorithm.

**Disposition:** unresolved and the highest-priority remaining structural question. It is not a screened algorithm or evidence for a speedup.

## D. Sparse dyadic order products and coefficient gcds

**Primitive and algorithm.** Work exactly in (Z/NZ)[X]. Store coefficients of

    F_m(X) = product_(j=1..m) (1 − a^j X)

as a sparse degree→residue dictionary. Generate dyadic lengths using

    F_(2m)(X) = F_m(X) F_m(a^m X).

After each convolution reduce coefficients modulo N, delete zeros, and check nonzero coefficient gcds for a proper factor. Also evaluate F_m(1) and take its gcd. For N=pq, a prime p divides F_B(1) precisely when ord_p(a)≤B. If a product gcd is N, locate the first nonunit prefix by binary search, using shifted blocks F_m(a^u X); differing component orders can then separate the factors. Equal component orders can fail and require another base. This card is explicitly scoped to balanced odd semiprimes after elementary preprocessing; no general-composite success theorem is supplied.

**Proposed complete gain.** Let S bound retained support sizes at every dyadic or shifted block needed. Indices have O(log B) bits and coefficients have n bits; scale a coefficient of degree k by a^(mk), charging its O(log B)-bit exponent. Sparse convolutions, temporary terms, gcds, binary-search calls, and preprocessing give a conservative bound

    O((log B)² (S² + S log B) M(n))

plus polynomial control work, and O(S²(n+log B)) temporary bits. If support stayed polynomial in n all the way to B≈√N, this would be a polynomial-time component-order detector. Its missing assumption is sparsity **before** a factor is available. A tiny recursion description alone does not imply a tiny evaluated object: F_m(X) and F_m(a^m X) have different arguments.

**Correct comparison.** Directly multiplying B factors costs O(B M(n)). Baby-step/giant-step geometric-product evaluation already achieves arithmetic cost quasi-linear in √B; [Bostan–Yurkevich](https://arxiv.org/abs/2012.08656) develop precisely such q-factorial/q-holonomic evaluation algorithms. Over the composite ring, a safe comparison uses monic product/remainder trees, or charges gcd detection whenever a proposed division encounters a nonunit. Fast polynomial arithmetic yields a conservative bit bound of the form soft-O(√B poly(n)). With B≈√N this is 2^(n/4) poly(n), already exponential and not an improvement over the general factoring comparisons. Rediscovering that batching is not a new gain.

**Decisive falsifier, algebraic.** Let p divide N, a be a unit, and m<ord_p(a). The coefficient of X^k in F_m is

    (−1)^k a^(k(k+1)/2) * product_(h=1..k)
             (1−a^(m−k+h)) / (1−a^h)   mod p.

Every numerator and denominator is nonzero because all displayed exponents lie between 1 and m. Hence **all m+1 coefficients are nonzero modulo p**. Before the smallest component order, all coefficients are units modulo N. Sparse storage is therefore dense and coefficient gcds give no early factor. This finite q-binomial identity can be checked by the displayed doubling/product recurrence; no factors are needed by the algorithm to use the recurrence. Here factors appear solely in its analysis.

At m comparable to an exponential component order, materializing the previous dyadic polynomial already costs exponential space and time. This is a representation-specific obstruction, not a lower bound on arbitrary scalar q-product evaluation. A later collapse such as product over a full prime-field orbit = 1−X^r arrives after the method has paid for dense stages.

**Prior-art distinction and disposition:** coefficient gcds and explicit zero pruning are the proposed specialization; no novel q-product evaluator was found. Reject this sparse expansion as a general route. Small-order families are already accessible to established order methods.

## Ranking and a bounded next step

There are **no surviving demonstrated factoring improvements**. Rank the remaining questions, not claimed algorithms:

1. **C: direct marginal contraction**, unresolved. It avoids the already-priced full-state approximation, but still owes a width bound for a fully specified arithmetic circuit and ordering.
2. **A: recurrence-to-order-multiple reduction**, a useful conditional lemma; the tested raw-bit cutoff is rejected. Revisit only with a concrete observation map or structural family and charged construction cost, rather than simply increasing the cutoff.
3. **B and D: rejected in their stated compression forms**, by the spectral-spread diagnostic and coefficient-density argument, respectively.

**Recommended next pass, falsifiable and bounded:** implement only the graph/constraint representation needed to screen C, not a simulator framework. Freeze one ripple-carry modular multiplier with explicit reductions and the cancellation/min-fill rule above. At n=8,12,16,20, generate three balanced semiprimes per size with seed 1002 and two unit bases each; hidden factors stay in generation. For each circuit inspect every prefix length using one fixed all-zero semiclassical measurement history (a failure on this history already rejects a uniform width cap). Cap the entire run at 60 seconds and record all unstarted/censored cases. Stop on w>2 ceil(log₂ n)+4; that falsifies the registered small-width implementation. If no failure appears, derive a symbolic bound for the same graph family before spending time on amplitudes. Phase-dependent cancellations or sampling success are not established by this graph-only pass.

A focused companion lemma for A, requiring no additional experiment, is: the lcm of all bit-stream annihilators is invariant under invertible F₂-linear mixing of the output bits. Thus a Gray-code or invertible XOR relabeling cannot remove the joint recurrence obstruction. Prove this in ordinary algebra first; no Lean changes are authorized in W001.

## Diagnostic record and evidence limits

The only executed experiment was the finite-prefix recurrence screen in [W001-orders-screen.py](W001-orders-screen.py), SHA-256 `c93057c079edf708b8943fbea8413d8a0520cba65e8e1f7b2d574d4a0954ec6f`. Command:

    timeout 60s python3 research/hypotheses/W001-orders-screen.py

It uses Python's standard library, seed 1001, an internal 55-second cap, and prints every (N,a) and outcome. Generation uses trial primality tests only for the tiny diagnostic primes; `profile(N,a)` receives neither factors nor periods. Setup, generation, and all 60 diagnostics completed in approximately 0.91 seconds as measured inside the script. This timing is not a factorization benchmark. Bit-packed Python integer operations were an implementation convenience, not a unit-cost complexity assumption.

Per-size results (12 pairs each):

- n=16: 11 refutations; maximum bit-stream complexity per pair ranged 150–514; cutoff 256; 1024 terms.
- n=20: 12 refutations; range 801–804; cutoff 400; 1600 terms.
- n=24: 12 refutations; range 1153–1156; cutoff 576; 2304 terms.
- n=28: 12 refutations; range 1569–1572; cutoff 784; 3136 terms.
- n=32: 12 refutations; range 2050–2053; cutoff 1024; 4096 terms.

A reproducible witness is N=51959, a=36978: among its 16 streams, observed complexities were 508–513, all greater than 256. The sole non-refuted pair was N=34579, a=26201, with complexities 144–150. Its exact infinite-period complexity, factor yield, and comparative cost were not established. The seed and source reproduce all 60 records; no unsuccessful outcomes were dropped.

These are diagnostic observations plus the algebraic derivations explicitly given above, not a validated candidate splitter or a formal proof. The other three cards were not benchmarked. Primary links were checked by web search/open during this pass; the NFS chapter's publisher page was verified after a university-hosted PDF fetch failed. The search was bounded and cannot certify novelty or exhaust the literature. No inference of impossibility is made from these failed representations or the absence of a positive algorithm.
