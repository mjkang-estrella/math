# Unaccepted independent initial proposal report: Factory Fable5.1

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-learning-tradeoffs-fable-20261008-r1`.
Status completed, no pending children. Read-only independent initial proposals.

WARNING: This raw report contains unsupported universal claims, cost-budget
errors and unverified reductions. It is retained as ideation, not accepted
mathematics or evidence of novelty. In particular, no universal coordinate
ST² bound, mutual-information-to-kangaroo conversion, or finite-test asymptotic
rejection is adopted. See coordinator disposition before using any formula.

# Independent ideation report: learned-heuristics / time-memory-preprocessing lens

Scope honored: read-only, no repo edits, no children, no experiments run, no wallet targets. I read only RESEARCH_LOOP.md / RESEARCH_TEAM.md for constraints and did not open any H001/H002 material. Target: ordinary prime-field prime-order curve, full unknown scalar, baseline = Pollard rho/kangaroo at $\approx\sqrt{\pi N/2}$ group ops with negation (and $j=0$ automorphism where present) constants; preprocessing baseline = Bernstein–Lange rho-with-precomputation on the Corrigan-Gibbs–Kogan tradeoff $ST^2 = \tilde\Theta(N)$.

Framing rule I applied throughout: a trained model of size $S$ bits is *advice* in the CGK sense. Any learned method must therefore be scored on the $(S, T, \text{preprocessing}, \epsilon)$ surface, and it only matters if it lands strictly below the generic $ST^2 = N$ curve at a size where that curve is measurable. That is also what separates "learning" from "hiding an inverse table in weights": a lookup table sits exactly on $ST^2 = N$ (BSGS-style $S \approx T$ pairs), so landing *on* the curve is zero evidence of learning.

Four cards, one short excluded list, then ranking.

---

## Card 1. Weak-bit learner + Blum–Micali amplification, with free "multi-view" features

**Mechanism.** Train a predictor $B_\theta$ for the hardcore predicate $h(k) = [k < N/2]$ (equivalently the LSB of $k \in [0,N)$, since $2^{-1}$ is computable mod $N$) from coordinates of $Q = kP$. The key feature-design point: from $Q$ alone one can compute any known multiples $c_1 Q, \dots, c_m Q = (c_i k) P$, so the input can be an arbitrarily long, perfectly consistent "multi-view" vector $\{x(c_i Q), y(c_i Q)\}$ at cost $O(m \log N)$ ops. Training data is free and unlimited (sample $k$, compute $kP$). Training is per-curve (curve-specific advice) with a cross-curve transfer arm as a control.

**Bridge to a full solver (two, both exact).**
- *Hard bridge (Blum–Micali, 1984):* if $\Pr[B_\theta(kP) = h(k)] \ge \tfrac12 + \epsilon$ over uniform $k$ for the fixed $P$, randomized self-reduction yields $k$ in $O(\log N \cdot \text{poly}(1/\epsilon))$ group ops plus $O(\log N / \epsilon^2)$ predictor calls. Håstad–Näslund (2004) extend to all bits for mod-$p$ DL; the EC version via halving works identically because $N$ is odd.
- *Soft bridge (information → kangaroo):* if the predictor outputs a posterior over the top $j$ bits of $k$ carrying $I$ bits of mutual information with $k$, a weighted kangaroo (Galbraith–Pollard–Ruprai nonuniform intervals) costs $\approx \sqrt{\pi N/2}\cdot 2^{-I/2}$. This handles partially-learnable predictors where the hard bridge's per-input advantage requirement fails.

**Source of gain.** Exponent-level only if $\epsilon(n) \ge n^{-c}$ (hard bridge) or $I(n) = \Omega(n)$ (soft bridge) with $n = \log_2 N$. Anything decaying like $2^{-cn}$ is a constant factor at best and $S$ of the network must then be charged against it.

**Applicability.** Any curve; no special structure assumed. Target-dependent at inference, target-independent at training.

**Costs.** Preprocessing = training (per curve). Memory $S$ = model size. Failed trials = Blum–Micali repetitions ($1/\epsilon^2$ per bit). Generalization to unseen sizes is *not* required if training is per target curve; what is required is seed/target generalization, i.e., genuine out-of-sample advantage.

**Prior art and novelty.** Blum–Micali 1984; Håstad–Näslund 2004; Boneh–Shparlinski (Crypto 2001) on bit security of ECDH; Shani (ePrint 2016/1189). Negative ML results: Takhanov et al., *Intractability of Learning the Discrete Logarithm with Gradient-Based Methods* (ACML 2023, arXiv 2310.01611), who prove gradient concentration for the parity bit in prime-order cyclic groups — directly on point — and observe decreasing accuracy with group order. Related: "The Discrete-Log Clock" (arXiv 2606.17399, 2026) on transformers grokking modular multiplication; "Learning Modular Exponentiation with Transformers" (arXiv 2506.23679). Novelty here (modest): (a) the free multi-view feature construction, which the gradient-concentration argument does not obviously cover because the feature map is not fixed-arity; (b) scoring the trained model on the CGK $(S,T)$ surface rather than by raw accuracy; (c) coupling to the two amplification bridges so a weak advantage is converted to a full-work number rather than reported as "accuracy". I am not aware of prior work that does (a)+(b) together, but I did not do an exhaustive search.

**Strongest unsupported assumption.** That gradient-trainable function classes over EC coordinates have non-negligible correlation with $h(k)$. Takhanov et al.'s result is a theorem against a broad gradient-based class for the plain representation; the multi-view extension is exactly where the assumption is unverified. Also implicitly assumed: Weil/Kohel–Shparlinski-type character sum bounds (which kill all *linear-in-characters* features at $O(N^{-1/2})$) do not extend to the product/compositional features the net can form. Prior probability of success is very low; the value is that the test is cheap and the negative result is sharp.

**Cheapest decisive falsifier.** Curves with $N \in [2^{16}, 2^{36}]$, 5 random curves per size, 3 seeds. Train on $10^5$–$10^6$ samples with $m \in \{1, 8, 64\}$ views. Measure held-out $\epsilon(n)$ with a shuffled-label control and a Wilson 99% CI. Decision rule: if $\log_2 \epsilon(n)$ is linear in $n$ with slope $\le -0.4$ for all $m$, reject the exponent claim (the trend is $2^{-cn}$). Also compute $S$ (parameter bits) and the implied $T$ via the hard bridge; reject the TMP claim if $(S,T)$ is on or above $ST^2 = N$. Fits the 60-second / $10^6$-event budget at the lower sizes; justify the top two sizes separately.

---

## Card 2. Symbolic feature search for coordinate-aware DL-bit correlations, with provable per-class exclusion

**Mechanism.** Replace the neural learner with a search (FunSearch-/PySR-style program synthesis or plain enumeration) over *short algebraic circuits* over $\mathbb{F}_p$ evaluated on the multi-view vector of Card 1: Legendre symbols $\left(\frac{x(c_iQ)+a}{p}\right)$, residues $x(c_iQ) \bmod \ell$ for small $\ell$, products/sums of these, traces of Frobenius of small-degree isogenous curves at points mapped through the isogeny, etc. Objective: maximize empirical correlation with $h(k)$ or with $k \bmod m$. A hit is then an explicit formula, not weights.

**Bridge.** Identical to Card 1 (hard and soft bridges). A formula with correlation $\epsilon$ is a predictor with advantage $\epsilon$.

**Source of gain.** Same as Card 1, but with two structural differences that make this a genuinely distinct mechanism, not a re-skin:
1. *Exact transfer across sizes.* A formula found at 32 bits is tested at 64 and 128 bits by evaluation, with no retraining; if it is an algebraic identity its advantage does not decay. Neural weights cannot be tested this way.
2. *Provable negative results per feature class.* For each class in the search grammar one can often bound the correlation analytically. For single Legendre-symbol or additive-character features of $x(kP)$ against linear phases in $k$, Kohel–Shparlinski-style exponential sums over elliptic curves give $O(\sqrt{p}\log p / N) \approx N^{-1/2}$, so the entire linear span is excluded with a theorem, not a benchmark. The search is thus confined to the compositional classes where no bound is known, and the negative evidence it produces is interpretable.

**Applicability.** Any curve. The isogeny-trace features are the only ones with any heuristic motivation (they expose arithmetic of the isogeny class not visible from $E$ alone); everything else is a blind search.

**Costs.** Preprocessing = search time (per curve class, not per target). Memory $S$ ≈ size of formula — essentially zero, so this is the one mechanism where a positive result would be unambiguously below $ST^2 = N$. Failed trials = the Blum–Micali repetitions. No generalization cost across targets or seeds by construction.

**Prior art and novelty.** Shparlinski's exponential-sum program (e.g., "Playing hide-and-seek with numbers", 2005; Kohel–Shparlinski 2000; Lange–Shparlinski on random walks on elliptic curves); Boneh–Shparlinski 2001; FunSearch (Romera-Paredes et al., Nature 2024) and symbolic regression tooling. I am not aware of program-search used to hunt for ECDL bit distinguishers specifically; novelty is in the combination and in using character-sum bounds as *pruning theorems* for the search grammar. Unknown whether anyone has done this.

**Strongest unsupported assumption.** That a short algebraic formula with $\epsilon \gg N^{-1/2}$ exists at all. The Weil-bound results strongly suggest that for low-complexity features it does not; a positive would be a theorem-level surprise. This is a high-risk card entered knowingly.

**Cheapest decisive falsifier.** Enumerate the grammar to depth 2–3 (a few thousand formulas) at $N \approx 2^{24}$ with $10^5$ samples; compute correlations; apply a Bonferroni-corrected threshold at $5\sigma$ above the $N^{-1/2}$-scaled noise floor. Any survivor is re-evaluated at $2^{40}$ by direct computation (no retraining). Decision: zero survivors at $2^{24}$ after correction, or survivors that collapse to noise at $2^{40}$, rejects. This is cheaper than Card 1 and shares its sampling code.

---

## Card 3. Learned walk-fate prediction inside Bernstein–Lange rho-with-precomputation (constant-factor TMP card, doubling as a non-genericity probe)

**Mechanism.** In BL preprocessing (ePrint 2012/458), a table of $T$ distinguished points is built offline; online, one starts walks from random $R = Q + aP$ and each walk of expected length $W$ ends at a DP that is in the table with probability $c$ (the coverage fraction). Expected online cost is $\approx W/c$; the wasted work is the $(1/c - 1)$ walks that end at non-table DPs. Train a classifier $F_\theta(R) \to \Pr[\text{walk from } R \text{ ends in table}]$ from coordinates of $R$ (and, optionally, of the first $j \ll W$ steps). Use it to pick starting points: sample $r$ candidate $R$'s, evaluate $F_\theta$, walk only the best. The classifier is *advice* and is charged to $S$; its training is *preprocessing* and is charged alongside the table build.

**Bridge.** Executable as-is: it is BL's algorithm with a start-point filter. Correctness is unaffected (the walk itself produces the DL); only the hit rate changes.

**Source of gain.** Strictly bounded: a perfect oracle at zero cost improves online time by exactly $1/c$, and in the BL optimum $c$ is a modest constant (they report walks tuned around $W \approx \tfrac12 (N/T)^{1/2}$ with wasted fraction of order one), so the ceiling is a small constant factor. The gain is *real* only if the classifier is both cheap ($\ll W$ ops per evaluation) and has AUC meaningfully $> 0.5$ on held-out $R$. Under the random-walk heuristic the fate of a walk is a pseudorandom function of $R$ and AUC $= 0.5$ exactly; any detectable AUC above chance is evidence that the r-adding walk $R \mapsto R + M_{h(R)}$ with $h = x \bmod r$ leaks its trajectory through coordinates, which is the only interesting outcome.

**Applicability.** Any curve; multi-target amortization inherited from BL.

**Costs.** Preprocessing: BL table build plus training on $\sim 10^5$ labelled walks (each label costs a full walk, so training cost is $\approx 10^5 W$ ops — must be included). Memory: table $T$ + model $S$. Failed trials: walks that miss the table despite the filter. Generalization: must hold across start points and ideally across tables; across sizes only matters for predicting whether AUC grows or shrinks with $N$.

**Prior art and novelty.** Bernstein–Lange 2012 (they already select table DPs by in-tree size, i.e., coverage-based *table* pruning); Bernstein–Lange "Non-uniform cracks in the concrete" (Asiacrypt 2013); Corrigan-Gibbs–Kogan 2018 (bound); the ITC 2022 "fully constructive DL preprocessing algorithm". Learned *start-point* selection is, as far as I found, not in the literature, but the idea is close enough to known table pruning that I would not call it a discovery even if it worked at constant factor. Teske's r-adding walks and Bernstein–Lange–Schwabe on the negation map are the walk-design baselines.

**Strongest unsupported assumption.** That a coordinate-computable function of $R$ predicts a $W$-step pseudorandom trajectory's endpoint membership better than chance at cost $\ll W$. There is no mechanism I can state for why it should.

**Cheapest decisive falsifier.** $N \approx 2^{28}$, one BL table ($T = 2^{10}$, $W \approx 2^{8}$), generate $10^5$ labelled walks, train a small gradient-boosted model on $(x, y, x \bmod \text{small primes}, \text{first } 4 \text{ step indices})$, measure held-out AUC with 3 seeds and a shuffled-label control. Decision: AUC $< 0.52$ with CI covering 0.5 rejects. Fits the budget. If AUC $> 0.5$ robustly, the next question is whether it comes only from the "first $j$ steps" features (then it is trivial path-prefix information, not structure) — ablate them.

---

## Card 4. Learned decomposability filter and learned Gröbner selection for prime-field summation-polynomial index calculus

**Mechanism.** Petit–Kosters–Messeng (PKC 2016) run Semaev index calculus over $\mathbb{F}_p$ with factor base $V = \{(x,y) : x \in [0, p^{1/m})\}$ and decompose $R = Q + aP$ into $m$ factor-base points by solving $S_{m+1}(x_1, \dots, x_m, x(R)) = 0$ with each $x_i$ in the interval, via a Gröbner basis after a bit-expansion of the interval constraint. Amadori–Pintore–Sala (ePrint 2017/609) reduce this to a single Gröbner computation. Cost structure: $\text{(trials)} / \Pr[\text{decomposable}] \times \text{GB cost} + \text{linear algebra}$. Two learned components: (i) a *decomposability filter* $D_\theta(x(R)) \to \Pr[R \in V + \dots + V]$ applied before each expensive GB call; (ii) a *learned S-pair selection / variable ordering* for the GB step (Peifer–Stillman–Halpern-Leistner, ICML 2020 RL for Buchberger; Kera et al., NeurIPS 2024 transformers for GB; HATSolver, ePrint 2025/2219, hierarchical attention + curriculum, which is explicitly cryptanalysis-motivated).

**Bridge.** Executable: PKM/APS pipeline with the filter in front of relation generation and learned selection inside the GB solver.

**Source of gain.** Honest accounting: (ii) is at best a polynomial factor in the GB step and does not move the exponent; PKM themselves conclude the prime-field variant is worse than generic methods because the system degree ($2^{m-1}$ per variable, times the bit-expansion) blows up. Component (i) is the only one with exponent potential: if $D_\theta$ had precision improving with $p$, relation generation would cost $\approx 1/\Pr[\text{dec}]$ fewer GB calls, and for $m \ge 3$ where $\Pr[\text{dec}] \approx 1/m!$ that is still only a constant unless the filter also lets one *shrink the factor base* (smaller $V$ ⇒ cheaper linear algebra but rarer decompositions, which a good filter would compensate). That tradeoff is the actual lever.

**Applicability.** Prime-field curves specifically; this is the one classical non-generic route for them.

**Costs.** Preprocessing: training the filter requires labelled decompositions, each of which costs a full GB solve — so training is expensive and must be amortized across targets on the same curve. Memory: GB intermediate matrices dominate, not the model. Failed trials: GB calls on non-decomposable $R$ (filter false positives) and missed relations (false negatives, which only cost time). Generalization: per-curve training; cross-size transfer irrelevant.

**Prior art and novelty.** Semaev 2004; PKM 2016; APS 2017; Peifer et al. 2020; Kera et al. 2024; Malhou–Perret–Lauter 2025. ML-for-Gröbner is active and recent, but I found no application of it to the Semaev system for prime fields, and no "decomposability pre-filter" anywhere. Novelty is real but the ceiling is low unless (i) shows non-trivial signal.

**Strongest unsupported assumption.** That decomposability of $R$ into interval-constrained points is predictable from coordinates of $R$. The set $V$ is not algebraic (interval, not subfield), so $V + \dots + V$ should be pseudorandom in $E(\mathbb{F}_p)$ and AUC should be $0.5$. I know no reason to expect otherwise.

**Cheapest decisive falsifier.** $p \approx 2^{30}$, $m = 2$, $|V| \approx 2^{15}$, so $\Pr[\text{dec}] \approx 1/2$ and labels are cheap (resolve $S_3$ directly, no GB needed at $m = 2$). Label $10^5$ random $R$, train a classifier on $(x(R), x(R) \bmod \text{small primes}, \text{Legendre}(x(R) + a))$, report held-out AUC with 3 seeds, 3 curves, shuffled control. Decision: AUC $< 0.52$ rejects (i) and with it the only exponent lever; (ii) is then a known engineering line, parked. This is cheap and reuses Card 2's feature code.

---

## Considered and excluded (with reasons, so they are not re-proposed)

- **Learned non-uniform walk / biased stationary distribution to speed collisions.** A walk concentrating on a subset $M \subset E$ collides in $\sqrt{M}$ but costs $N/M$ to re-enter $M$; total $N/\sqrt{M} \ge \sqrt{N}$. Prime order leaves no closed proper subsets. Known (Teske; Bailey et al.).
- **Learned pairwise "proximity oracle" for batch collision.** An oracle for $|\log R_1 - \log R_2| < W$ is a $W$-interval DLP on $R_1 - R_2$, cost $\sqrt{W}$ by kangaroo; learning adds nothing unless it solves the DLP.
- **Learned lift selection for Xedni calculus.** Jacobson–Koblitz–Silverman–Stein–Teske (2000) show the dependency probability is asymptotically negligible; a learned selector would need to beat random by a factor $\sim p$, which is the problem itself.
- **Learned kangaroo priors / scalar-distribution exploitation.** Violates the full-unknown-scalar goal; also the RESEARCH_LOOP ban on secret-range narrowing.
- **Learned "pseudo-equivalence classes" beyond negation / $j=0$ automorphisms.** A class function compatible with the walk must be an endomorphism; ordinary curves have none beyond $\mathbb{Z}[\pi]$, which acts trivially on $E(\mathbb{F}_p)$.
- **Learned index structures to compress DP tables.** Pure storage engineering; sits on $ST^2 = N$ by construction. Explicitly *not* learning in the sense this lens requires; mention only as a cost-model constant for Card 3.
- **Learned constant tuning of r-adding / kangaroo jump distributions.** Known tricks, constant factors; fails the "known tricks are not discoveries" rule.

---

## Ranking (gain × testability, with my honest priors)

| Rank | Card | Potential gain if true | Prior that it is true | Falsifier cost | Why this position |
|---|---|---|---|---|---|
| 1 | **2. Symbolic feature search** | Exponent-level; $S \approx 0$, so unambiguously below $ST^2 = N$ | Very low | Lowest; exact size transfer; partly provable negatives | Best gain-per-test-dollar and produces theorem-grade negative evidence (character-sum exclusions) rather than "the net didn't train" |
| 2 | **1. Weak-bit learner + amplification** | Exponent-level if $\epsilon(n)$ is polynomial | Very low (Takhanov et al. 2023 is a direct negative for the plain representation) | Low–moderate | The multi-view gap in the existing negative result is the only place a learned method has room; the amplification bridges make any result full-work-comparable |
| 3 | **4. Decomposability filter for prime-field Semaev** | Constant unless filter precision grows with $p$ and permits factor-base shrinking | Very low | Low (at $m=2$ labels are free) | Only non-generic classical route for prime fields; ML-for-Gröbner is live literature (2024–2025), but its contribution is polynomial, not exponent |
| 4 | **3. Walk-fate prediction in BL preprocessing** | Constant factor $\le 1/c$ | Near zero for structure; modest for a constant | Low | Worth one cheap run as a non-genericity probe of r-adding walks; not a discovery even if it works |

None of these cards claims an improvement over the baseline; all four carry a stated unsupported assumption that I expect to fail. Their value is that each failure mode is sharp, cheap, and distinct: Card 2 fails with a theorem-backed noise floor, Card 1 fails with an $\epsilon(n)$ slope, Card 4 fails with an AUC at $m = 2$, Card 3 fails with an AUC against a fixed table. If synthesis wants one starting point from this lens, run Cards 2 and 4 first: they share the sampling/feature code, and both finish inside the 60-second / $10^6$-event envelope at the lower sizes.
