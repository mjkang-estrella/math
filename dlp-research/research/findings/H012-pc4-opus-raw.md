# H012 PC4 Opus raw review — qualified, not adopted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h012-pc4-cost-priorart-opus-20261008-r1`.
Provider claudeAgent, model claude-opus-5-5. Completed, no pending children.
Root corrections include: twist order is ODD; solution/rank yield is not granted
by grid size; no measured brute-force event count; matrix capacity is not runtime;
saturation alone does not establish an empty-instance failure. See disposition.

# H012 PC4-v1 review: cost/yield, family and prior art

**Bottom line:** I recommend not running the proposed single-node diagnostic in its current form. If it succeeds, it tells us almost nothing that changes a decision. It is likely to hit the 1M-event cap, and a cap hit is inconclusive. The best primary evidence I could access points against the method, but it does not settle the question. A cheaper ladder test (section 4) is better: whichever way it comes out, it changes the next decision.

This was a read-only paper audit. I made no edits, ran no experiments, installed nothing and launched no subagents. I did not repeat the native critic's degree-4 obstruction work.

## 1. Cost/yield threshold

- **The 1.5 threshold is right.** The ledger is setup + O(B·K/σ + B²). With B ≈ q^{1/5}, an exponent gain needs K/σ ≤ B^{1.5−ε}. Factor-base sparse linear algebra costs about (5B)² ≈ q^{0.4}, which is not the bottleneck. σ = Θ(1) holds only if N = ∏B_i is about q. Any slack in N, say N ≈ q^{1−ε}, costs a factor q^{ε} in σ.
- **The cost of one node is not the problem.** The number of nodes is. At the top node, n = Σg_i·k_i + m − 2 = Θ(log B), so M = C(n+4,4) = Θ(log⁴ B). Even the conservative dense bound O(nM·M²) is polylogarithmic in B. The charged items (chart enumeration, coefficient history, term operations, derivation DAG, replay) multiply this by polylog factors and leave the exponent alone. They must stay in the ledger, but they don't decide the question.
- **What actually decides it is the pruning threshold:**
  - The 5-subset chart has B⁵ ≈ q leaves.
  - Visiting V = o(B^{1.5}) nodes means degree-4 constant certificates must succeed on almost all empty nodes whose remaining grid has about B⁵/V ≈ B^{3.5} ≈ q^{0.7} tuples.
  - This must hold with Θ(log q) variables and a refutation-failure rate of o(1) at those levels.
  - The 2-, 3- and 4-subset charts also go over budget without pruning (B^m leaves, which exceeds B^{1.5} for m ≥ 2). The m = 2 chart can instead use a per-x₁ gcd costing B·polylog.
- **A useful framing for the card:** "degree-4 PC must refute S6-on-grid instances with about q^{0.7} grid points." That is the claim that needs evidence.
- **Emptiness over the algebraic closure matches rational emptiness.** I checked the card's twist argument. #E′ = 2p+2−q is even, so the twist can have 2-torsion. However, a twist-part sum that is anti-invariant under Frobenius and also 2-torsion is fixed by Frobenius, so it lies in E(F_p)[2] = {O}. Extra closure solutions need a separate twist zero-sum, at roughly 1/q per tuple, so they are negligible. Empty nodes are genuinely empty, and the hard part is refutation degree, not semantics.

## 2. Restrictive family: a bigger problem than the card says

The card asks for B_i = ℓ_i^{k_i} ≈ q^{1/5} for ℓ = 2, 3, 5, 7, 11, pairwise coprime, with ∏B_i | p−1 and ∏B_i ≈ q ≈ p.

- **This forces p−1 to be almost entirely 11-smooth,** with balanced exponents and a cofactor of size p^{o(1)}.
- **Such p are very rare.** Only polylog(p) numbers up to p are 11-smooth, so each size gives only a handful of candidates. Each must also be prime and must carry a prime-order curve, found by point counting or CM.
- **Even the existence of such p is open.** I don't know of any result showing infinitely many primes with p−1 11-smooth (the p−1 = 2^k case is the Fermat-prime question). Even a growing family is not established.
- **So the asymptotic claim is conditional on open number theory,** in addition to everything else. It does not transfer to arbitrary p, and PC4-v1 never applies to secp256k1.
- **Possible fix:** if work continues, use one subgroup μ_B with B | p−1, B ≈ q^{1/5}, and five different shifts u_i. That needs only a q^{0.2}-smooth factor, which is the same kind of requirement as PKM §3.3, but it needs its own ledger for distinctness and symmetry.
- **Small cases can't show scaling.** I agree with the objection: at k_i = 1 the domains (2, 3, 5, 7, 11) are lopsided, and fixed-size runs prove nothing asymptotic.

## 3. Would a successful one-node diagnostic be worth anything? Almost nothing.

- **Brute force is cheaper on that node.** At k_i = 1, the root grid has only 2·3·5·7·11 = 2310 tuples. Enumerating them with signs costs about 10⁴–10⁵ events, which is less than the closure capacity (M = 7315, up to nM ≈ 1.3·10⁵ requests, each reducing against up to M rows). Success would only show that a certificate exists for a grid that is far easier to brute-force, and far smaller than the q^{0.7}-size grids that matter.
- **Only one outcome is informative:** the queue running out with no constant certificate, before the cap. That is a fairly strong practical negative, although it is not monotone in size and not a proof. A cap hit only rejects that schedule.
- **Setup could use up the cap.** The card requires p ≡ 1 mod 2310, prime full order q and paid search. Naive O(p) Legendre point counting at about 20-bit p already costs roughly 10⁶ events. The frozen protocol must name the point-counting algorithm (for example a BSGS-based O(p^{1/4}) method), the expected number of trials, and the setup budget before anything runs.

## 4. Cheapest test that could change the decision: an m = 2 ladder

- **Set-up:** two domains only, one S3 equation, no intermediate variables, using exactly the PC4 degree-4 closure. Use ℓ = 2 (and then 3), with k = 1…6 per domain, so n = k₁ + k₂ ≤ 12 and M ≤ 1820.
- **Targets:** choose p much larger than the grid, so that most nodes are empty. Confirm emptiness by exhaustive grid enumeration, which is paid and cheap.
- **Measurement:** use several declared targets per k, all within a single 1M/60 s budget. Record the fraction of empty roots that degree-4 refutes, as k grows.
- **Comparison with prior art:** this setting is essentially PKM's Table 4 case (2-power subgroup, m = 2), which gives a direct cross-check.
- **Why it decides something:** if degree-4 refutation already fails around grids of 2^{10}–2^{12}, it cannot plausibly reach q^{0.7}-size grids. That would retire PC4-v1 at degree 4 in practice, though not as a proof. If it holds up, that justifies freezing the 5-domain node next.

## 5. Prior art and what I actually accessed

- **[PKM, PKC 2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf)** — I read the full PDF pages directly.
  - §3.3 is almost exactly PC4-v1's family and system: factor base from a smooth-order subgroup of F_p^* or its coset aG, constraints broken into chains of maps x^{p_j}, combined with S_{m+1}.
  - Table 4 (prime field, p−1 subgroups, m = 2) gives Magma's corrected degree of regularity D_av^corr as:
    - 4.00 for n₁ ≤ 5 (p = 1153);
    - 5.00 for n₁ = 6–9;
    - 6.00 for n₁ = 10–11 (p = 4206593).
  - The authors state the asymptotic complexity is unknown and that their attacks are not practical.
  - They also report that, on preliminary tests, Semaev's original factor base was easier for Gröbner bases.
  - **Caveats:** this is F4 step degree on systems that often have solutions, not PC refutation degree on empty nodes, and it uses only 2-power domains. It is suggestive evidence against degree 4, not decisive.
- **Semaev 2015** — root's PDF fetch got 403. I accessed the [ePrint abstract page](https://eprint.iacr.org/2015/310) and [arXiv 1504.01175](https://arxiv.org/abs/1504.01175) through an ar5iv render; the ar5iv passages came via a summarizing fetch tool, so treat the wording as moderately reliable.
  - The S3 chain with t−2 intermediate variables, taken in F_q, is Semaev's.
  - The analysis is for binary curves, with a regularity-degree-at-most-4 assumption backed by experiments.
  - The text states that it is "not quite clear" how to solve the system when q is a large prime.
  - PC4-v1's differences: intermediate variables over the algebraic closure, a capped PC procedure plus digit branching, and an exhaustive leaf fallback. Digit branching looks like standard guess-and-determine; I did not check a source for that.
- **[Kosters–Yeo, arXiv 1503.08001](https://arxiv.org/pdf/1503.08001)** — I extracted the text myself. In binary-field experiments, they report that the degree of regularity appears to grow with n, contrary to the first-fall-degree assumption. This is binary fields only.
- **[Amadori–Pintore–Sala, ePrint 2017/609](https://eprint.iacr.org/2017/609)** — I read the abstract only. It is a prime-field variant reported to beat Semaev's method and PKM. I saw no regularity data.
- **Clegg–Edmonds–Impagliazzo** — I did not access it (root's DOI fetch failed and I did not retry). The standard n^{O(d)} bound for degree-d PC is not verified from the source here.

## 6. What remains open

Nothing above proves that degree-4 PC fails for this system. The prior evidence uses different degree measures (Gröbner step degree rather than refutation degree), different domains and different m. Verified improvement remains **NONE**. The family-existence point is "not established", not "known false".
