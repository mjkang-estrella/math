# Unaccepted external critic report

This is the verbatim delegated report, retained for process evidence. It is NOT
an accepted theorem or cost model. See H001-delayed-canonicalization-gate.md and
the coordinator disposition for qualifications. Some universal assertions,
transferred exponents and toy measurements remain unsupported/unreproduced.

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h001-algorithm-critic-opus-20261008-r1`
Provider/model: `claudeAgent/claude-opus-5-5`; status completed.

# Independent critic report on H001 (read-only, no repo edits)

**Bottom line:** none of the three shortlisted ideas has a mechanism that could change the full-size ECDLP assessment. Verified improvement: **NONE**. Only item 1 has a test that could change the conclusion, and that test would replicate prior art (Petit–Kosters–Messeng, Amadori–Pintore–Sala). Items 2 and 3 should be rejected.

## Current best supported full work (ordinary prime-field, prime-order curve)

- **Single target, negation only.** Parallel rho with the negation map takes (1+o(1))·√(πq/4) ≈ 0.886√q iterations on average, under a random-walk heuristic. This is BLS PKC2011 §3, which I read from the retrieved PDF.
  - Measured on their 55-bit curve: on average **1.0074·√(πℓ/4)/2²⁰** distinguished points over 257,241 runs. At 50 bits the figure was 1.0789.
  - Fruitless cycles cost a factor 1+Θ(1/√r), with r=2048 and a 2-cycle check every 48 iterations.
  - Negation-related operations take **under 4% of cycles per iteration** (BLS §5).
- **With an order-6 automorphism (j=0):** about √(πq/12) is the known constant. It is baseline, not a discovery. I did not retrieve a primary measured overhead for order 6.
- **Memory:** the distinguished-point store, plus an r-table of 2048 points.
- **Scope:** these are heuristic averages, not per-input bounds. The only sub-√q per-target costs I know of need counted precomputation or several targets (Bernstein–Lange precomputation; Kuhn–Struik for multiple targets). I did not retrieve those sources this round, so treat them as unverified pointers.

## Ranked verdicts

### 1. Coordinate-aware Semaev relation generation — Unsupported. Accept-to-test only as a bounded replication of prior art.

**Joins and buckets are disqualified, for two reasons:**
- **Counting bound (heuristic random model).** If relations come from collisions among N computed sums of factor-base points or aP+bQ, you get about N²/q relations. You need about B of them, so N ≥ √(qB) = q^{1/2+(1/5+δ)/2}. That is worse than rho. A shared-table meet-in-the-middle is no better: storing 3-sums costs B³ = q^{3/5+3δ} up front, and each target still costs B².
- **Wagner/k-tree bucketing.** Its merge step needs a filter f with f(P₁+P₂) determined by f(P₁) and f(P₂). Such an f is a homomorphism onto a quotient group, and a prime-order E(F_p) has no nontrivial quotient. Coordinate buckets like "x mod 2^k" are not cosets, so merging them guarantees nothing. This rules them out outright, not just as a matter of constants.

**What remains is the algebraic problem.** You must find xᵢ in a factor base V with S_{m+1}(x₁..x_m, X)=0. PKM (PKC2016, retrieved) already give the exact cost model:

  P(p,m) + (m!·p/(deg L)^{m−1})·T(E,m,L) + (deg L)^ω

This beats √p only if a single decomposition attempt costs T < p^{1/2−1/m}, with (deg L)^m ≈ m!·p. Their "structured elimination" is the shortlist's mechanism: V is the kernel of L, written as a composition of low-degree maps. It needs p−1 with a large smooth factor, or an auxiliary curve, and that precomputation P must be counted. Their conclusion: *"The attacks are not practical at the moment and we do not know their asymptotic complexity."* APS (FFA 2018, ePrint 2017/609) improve on PKM and Semaev, but the abstract I retrieved makes no claim against rho.

**Exact thresholds, written for a fixed saving ε > 0 (little-o is not enough):**

| Variant | Linear-algebra / attempt count | Per-attempt budget T |
|---|---|---|
| m=5, no large primes (H001's case) | B² with B=q^{1/5+δ} needs δ ≤ 1/20−ε | T ≤ q^{3/10−δ−ε}/(m!·correction) ≈ B^{1.5} |
| m=4, no large primes | B² = q^{1/2} | ties at best; no fixed saving |
| m=3 / 4 / 5, double large prime | about q^{4/9} / q^{3/8} / q^{8/25} attempts | T < q^{1/18} / q^{1/8} / q^{9/50} |

- The double-large-prime rows are **my heuristic transposition** of Gaudry's Õ(q^{2−2/n}) (JSC 2009) from extension fields. I confirmed that exponent only through a catalogue entry and a Joux–Vitse talk, not the paper itself.
- H001 misses these rows. Rebalancing with large primes lowers the linear-algebra exponent but shrinks the per-attempt budget.
- **Best known T:** exhaustive search over m−1 coordinates costs q^{(m−1)/m}; generic meet-in-the-middle costs about q^{1/2} per attempt. Both are far above every threshold.
- **Lattice/Coppersmith route (my analysis, not a cited result).** S_{m+1} has degree 2^{m−1} in each variable, so standard small-root bounds need roughly B < q^{1/(m·2^{m−2})}. At that size the decomposition probability goes to zero. Only a *linear* relation would allow B^m ≈ q.
- **Memory:** the factor base, about 5B relation entries and sparse linear algebra are all O(q^{1/5+δ}), so memory is not the bottleneck. T is.

**Smallest decisive test:** for a fixed m (with m=3 as a diagnostic only), measure the growth of degree-of-regularity / solving cost for the PKM system (3) as the number of composition levels n₀ grows (deg L = 2^{n₀}). Report the exponent γ = log T / log deg L against the budget above. Bounded degree would change the assessment; linear growth confirms rejection.
- This repeats PKM/APS, so it can show they were wrong but cannot be counted as novelty.
- No Gröbner engine (msolve, Singular, Sage, sympy) is installed here. Installing one is a coordinator decision.

### 2. Delayed canonicalization / batched quotient rho — Reject analytically.

- **Maximum possible saving.** In affine coordinates with batched inversion, canonicalizing ±P is a sign test plus a conditional subtraction. BLS put everything negation-related, including cycle handling, at under 4% of cycles.
  - Note: the "24 cycles canonicalization" in Bos et al. (quoted by BLS) is *modular* reduction to a canonical form, not class canonicalization. It must not be counted as a saving.
  - For order 6, the extra cost is about 1M for βx per step. My estimate is ≤ about 15–17%; I have no primary measurement.
- **Loss.** If you canonicalize only every t steps, the map is only well-defined on classes at block boundaries. Between boundaries the walk lives in the full group. Two walks that meet at different phases diverge at the next canonicalization (with probability ½ per canonicalization), long before a distinguished point is reached. So merges must happen at the same phase.
  - Model, negation: steps L_t/L₁ = t·√(2/(t+1)) = **1, 1.63, 2.53, 3.77** for t = 1, 2, 4, 8.
  - Model, order 6: t·√(6/(t+5)) = **1, 1.85, 3.27, 5.43**.
  - Field work saved is at most C/(A+C) per step, where A is the cost of a point addition and C the cost of one canonicalization. That is below 4% for negation, so every t ≥ 2 loses.
  - r-table, cycle and restart overheads are unchanged or worse, as covered in the toy below.
- **Toy check** (/tmp only, 936k events, under 60 s, seeds 7919·t+s, 80 runs each): a stand-in walk on Z/262139, r=4096, short cycles restarted and charged. Measured step ratios were **1, 7.96, 4.78, 2.46**.
  - Fruitless cycles dominate t=2 and t=4 (7.05 and 1.94 per run). t=8 came in below the model, so the toy does not quantitatively validate the model.
  - What it does support is the direction: every t ≥ 2 costs at least 2.4× more, against at most 4% possible saving.
- No matched complete-run experiment is justified. Comparing against plain rho would be the wrong baseline anyway.

### 3. GLV as an exponent reduction — Reject.

- The map (k₁,k₂) ↦ k₁+λk₂ sends a box of area about q onto Z/q through a lattice of determinant q. Each k has O(1) decompositions, so the joint domain stays at about q.
- That gives one linear relation in two unknowns. Neither coefficient is revealed, and no operation shrinks the box. Two-dimensional generic search (Gaudry–Schost type) is still Θ(√q).
- An endomorphism acts on G as multiplication by λ. Quotienting by ⟨λ⟩ costs ord(λ) evaluations per step to gain √ord(λ). That is only worth it when the orbit is small and cheap: the order-4/6 automorphisms, which are baseline, or Frobenius on Koblitz curves, which doesn't apply here. No new information is identified.

## Strongest alternative

I have none that meets the bar of a concrete new mechanism plus a falsifier plus checked prior art. The only route with an open exponent is item 1's generalized root-finding problem (PKM's Problem 1), and that is already prior art.

## Sources

**Retrieved and read:**
- [BLS PKC2011](https://www.iacr.org/archive/pkc2011/65710132/65710132.pdf), §3, §5, §6
- [PKM PKC2016](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf), cost formula, Problem 1, conclusion
- Abstracts only: [Semaev 2004/031](https://eprint.iacr.org/2004/031), [Gaudry 2004/073](https://eprint.iacr.org/2004/073) (whose preprint exponents are 10/7 and 14/9, not 2−2/n), [APS 2017/609](https://eprint.iacr.org/2017/609)

**Secondary only:**
- Gaudry JSC2009's Õ(q^{2−2/n}), via the [MaRDI catalogue entry](https://portal.mardi4nfdi.de/entity/Q733510) and a [Joux–Vitse talk](https://www-fourier.univ-grenoble-alpes.fr/~viva/research/talks/ECC2011-vitse.pdf)

**Missing (not retrieved):**
- Bos–Costello–Miele (order-6 overheads)
- Bernstein–Lange precomputation papers and Kuhn–Struik
- Huang–Kosters–Yeo (last fall degree)
- The full APS text

## Next decisive experiment

Only item 1 is worth an experiment, and only if the coordinator approves installing a Gröbner engine: the PKM-system degree-of-regularity growth test in n₀ described above, with the budget γ from the threshold table. Otherwise, park item 1 as a known open problem. Items 2 and 3 should go to negative evidence with the arithmetic above.
