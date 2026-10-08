# Unaccepted H002 delegated report: filter-cost-review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-filter-cost-review-20261008-r1`.
Provider/model: `claudeAgent/claude-opus-5-5`; status completed.

This report is retained for process evidence, not automatically adopted. Primary
formula checks, cost assumptions and universal claims require coordinator
qualification. In particular the EDS index1 identity is under active correction;
no experiment should rely on it before resolution. See the coordinator disposition.

# Review: H002 L3/L4 cost gate (`findings/H002-filter-full-work-gate.md`, L3/L4 in `hypotheses/H002-learning-cards-and-disposition.md`)

I only read files and sources. I made no edits, started no children and ran no experiment. Sources I checked:
- **Bernstein–Lange (BL), "Computing small discrete logarithms faster".** The [ePrint 2012/458 abstract](https://eprint.iacr.org/2012/458) plus the full text of the [author PDF](https://cr.yp.to/dlog/cuberoot-20120919.pdf), §3–4.
- **Petit–Kosters–Messeng (PKM), PKC 2016.** I saw only a search-result excerpt of the [author PDF](https://christophe.petit.web.ulb.be/files/16PKC_primeECDLP.pdf). I did not read the full text.

## 1. Renewal equation and filter costs

The gate's formula `(a+g+rC)/(pt)` is right when attempts are independent and identically distributed and each attempt's cost does not depend on its outcome. By Wald's identity, cost and success may be correlated *inside* one attempt. Three corrections are needed:

- **Use the general form, not `r·C`.** With A = "filter accepts" and U = "outcome is usable", the cost per useful outcome is `E = (a + g + E[C·1_A]) / P(A∧U)`.
  - The perfect-filter case is `(a+g)/p + E[C | U]`, not `+C`.
  - BL's walks show why this matters. A successful walk has extra merge opportunities, so its length need not be the unconditional mean W.
  - The full-work inequality should therefore be `pt·H/K + a + g + E[C·1_A] < t(a + E[C])`.
- **Solver timeouts are false negatives.** If C is cut off at a time limit, the effective acceptance rate becomes `t_eff = t·P(no timeout | U)`. The timed-out cost still goes in the numerator.
- **Prefix filters need their own equation.** A filter that uses the first j walk steps is sequential, so a rejected walk has already paid for j steps. The cost is `a + j + g + 1_A·(C − j)`, and a walk that reaches a distinguished point within j steps is settled immediately.
- The amortization algebra (`pt·H/K`) checks out.

## 2. The matched baseline is under-specified

The finding matches the baseline on memory, but not on **preprocessing compute**.
- BL §4 shows that spending more preprocessing directly cuts online cost. They pick the T most useful distinguished points from a larger pool of walks, comparing pools of N=T, 2T and 8T.
- In L3, every training label is one walk from a known-log start. Those label walks are therefore valid pool walks. The fair baseline puts the same walks into BL's table selection.
- Matching memory: BL with T + ⌊S_model / bits_per_entry⌋ entries.

At pilot scale, model memory is not negligible. Take a table of T=64 entries at 40 bits each (2,560 bits):
- The raw card's gradient-boosted model (≈50 depth-3 trees, ≈27 kbit) would buy the baseline about 670 extra entries, more than 10× the table.
- A 64-coefficient model at 16 bits per coefficient is 1,024 bits, which buys about 26 extra entries.

## 3. Training amortization (K)

**L3 (endpoint filter):**
- K is the number of targets that share one table and one walk function. Labels are specific to that table.
- For a single target, L3 is not applicable. BL's precomputation costs about 1.24–1.9·(ℓT)^{1/2}, already more than rho's ~ℓ^{1/2}.
- Break-even even for a perfect, free filter: n_train·(a+C) ≤ K·(a+C)(1/p − 1). With n_train = 4,000 and p ≈ 0.22, that needs K ≳ 1,100 targets.

**L4 (relation filter):**
- Decomposability depends only on x(R), not on Q. One filter can therefore be shared across targets on the same curve and factor base.
- Within one target, K ≈ the number of relations needed (≈|F|), which is large and legitimate. This is the main structural advantage of L4 over L3.

## 4. Conditions for an endpoint filter vs a relation filter

| | L3 endpoint | L4 relation |
|---|---|---|
| Label | Deterministic given start, walk and table. Costs one walk; no scalar needed. | "Decomposes and is useful (new, raises rank)". Costs a full solve. |
| Cost of a false positive | One wasted walk, with E[C\|fail] measured separately | One wasted solve. An inconsistent Gröbner-basis system can be much cheaper or much dearer than a successful one, so both must be measured. |
| Cost of a false negative | Only through t in the denominator | Through t, plus filter bias: preferring some factor-base elements can lower rank and raise the number of relations needed |
| Dependence between attempts | Walks merge, so failures are correlated. A free non-learning baseline is to remember failed distinguished points for this target. | Duplicate relations and linear dependence |
| Ceiling at fixed parameters | 1/p = 1/(1−e^(−α²)), from BL §3: about 4.5× at α=½ | About 1/Pr[dec] (≈ m! for an interval factor base), constant at fixed m |
| Exponent lever | **Exists conditionally (see below).** The raw claim "small constant ceiling" holds only at BL's tuned α. | Only if the filter allows a smaller factor base with p→0 and still gives f = O(p) at g ≪ C |

**L3 exponent lever, derived.** With a perfect filter, run walks at small α, where p ≈ α² and W = α(ℓ/T)^{1/2}. Online cost is then ≈ (a+g)/α² + α(ℓ/T)^{1/2}. Minimizing over α gives ~(a+g)^{1/3}(ℓ/T)^{1/3}.
- This needs t bounded away from 0, f = O(α²) and g = O(1) group operations as α→0. In effect, the filter must test membership in a pseudorandom covered set without walking.
- The generic preprocessing bound of Corrigan-Gibbs–Kogan does not rule this out, because the filter reads coordinates. Nothing supports it either.
- So I would not prune L3 as "constants only". The falsifiable quantity is how f/p and t trend as α shrinks.

**L4 at m=2 is not usable as a validation case.**
- Labels are not free. With an interval factor base |V| ≈ √p, labelling means either (i) enumerating every x₁ ∈ V and solving a quadratic, about 2^15 operations per label at p ≈ 2^30 (about 3.3·10⁹ for 10⁵ labels), or (ii) precomputing V+V, which is O(p).
- Index calculus at m=2 with |V| = √p costs about p in total, already worse than rho. A filter can only shave constants off an algorithm below the baseline.
- PKM's factor base is algebraic, not an interval: points whose x is a root of a composed low-degree rational map L. The raw Card 4 description is wrong on this. So an m=2 interval pilot validates neither PKM nor m=5.

Smaller points:
- The raw claim "AUC = 0.5 exactly" is overstated. A start that is itself a distinguished point, and the first step index, leak trivially.
- A non-learning early-abort rule (cutoff on walk length) is a baseline any prefix filter must beat.

## 5. One corrected bounded experiment (L3-E1), not run

I think this is justified only as a low-priority falsification pilot, after the pool has been ranked. I am not proposing any L4 spec: none is justified until a specific PKM-style factor base and solver exist and their success and failure costs are measured.

**Setup**
- **Curve:** one prime-order short Weierstrass curve with p ≈ 2^20, from a fixed seed.
  - Prime order is certified by finding the order of a random point by baby-step giant-step over the Hasse interval (width 4√p ≈ 4096, about 128 operations per candidate curve).
  - This costs ≤ 4,000 events, counted.
- **Walk:**
  - Base-G r-adding walk with r = 16 and step multipliers of known log; the step index is bits 6–9 of the canonical x.
  - A point is distinguished when x mod 64 = 0 for α=½, or x mod 32 = 0 for α=¼.
  - Walks are capped at 16W steps; a capped walk counts as a failure at full cost.
- **Starts:** R_i = R_{i−1} + sG with tracked log, costing 1 addition each. Every walk therefore has a known log and can also serve as a pool walk.
- **Two configurations** with T = 64:
  - A: α = ½, W = 64
  - B: α = ¼, W = 32
- **Table:** for each configuration, 512 pool walks (8T). Keep the top T using BL's weight: total length of walks reaching the point + 4W per walk.

**Labelled walks and splits**
- A: 6,000 walks, split 3,000 train / 1,500 validation / 1,500 untouched test.
- B: 8,000 walks, split 4,000 / 2,000 / 2,000.

**Arms**
- Logistic regression only: L2-regularized, at most 100 iterations, coefficients quantized to 16 bits and evaluated in quantized form.
- *Static features* (51):
  - low 8 bits of x
  - y parity
  - one-hot first step index (16)
  - one-hot x mod 3, 5, 7 and 11 (26)
- *Prefix features* (83): the static set plus one-hot indices of the first 2 steps.
- *Shuffled-label control.*
- *Oracle pipeline control:* the label itself, used to check the accounting.

**Baselines, all computed from the same walks, which do not depend on the table**
1. The T-entry table alone
2. Memory-matched: T + ΔT entries, with ΔT = ⌊model bits / 40⌋ (26 for static, 34 for prefix)
3. Preprocessing-matched: top T from the pool walks plus the training walks
4. Baselines 2 and 3 combined
5. Non-learning walk-length cutoff, tuned on validation

**Event budget** (1 event = one group operation, table lookup or model inference)

| Item | Expected events |
|---|---|
| Curve setup | ≤ 4,000 |
| Pool walks | 33,300 (A) + 16,900 (B) |
| Labelled walks | 390,000 (A) + 264,000 (B) |
| End-to-end check: 16 real targets solved in config A, scalars verified | ~5,200 |
| Table lookups: 4 table variants × 14,000 walks | 56,000 |
| Inference: 3 arms × 7,000 validation + test points | 21,000 |
| **Total** | **≈ 790,000** |

- Hard abort at 1,000,000 events and 60 s wall time; an aborted run is reported as incomplete.
- The standard deviation of total walk steps is about 6,000, so the cap is very unlikely to bind.
- Training time is reported separately, in seconds and in addition-equivalents. The training walks are already counted in H.

**Metrics**
- Ratio estimators on the test split:
  - Unfiltered: E = Σ(1 + C_i) / Σ S_i
  - Filtered: E = Σ(1 + g + prefix_i + A_i·(C_i − prefix_i)) / Σ A_i S_i
- g is the measured inference time divided by the measured time of one addition.
- Thresholds are chosen on validation only; t and f come with Clopper–Pearson intervals.
- 98.75% bootstrap intervals (Bonferroni over 2 configurations × 2 arms).
- AUC is reported as a diagnostic only.

**Decision rules**
- **Abort as invalid if either control fails:**
  - the oracle arm misses the analytic ceiling (a+g)/p + E[C|U] by more than its interval, or
  - the shuffled-label arm beats baseline 1.
- **Pass:** the upper bound of E_filtered is below the lower bound of the best of baselines 2–5, in a given configuration. A pass means only "replicate on more curves, seeds and sizes (2^24, 2^28)". It is not an improvement.
- **For the exponent lever:** report t and f/p̂ in A versus B. Only a non-growing f/p as α halves is interesting.
- **Fail:** rejects only this feature set, model, size and table configuration.

## 6. Unresolved
- I have not read PKM's complexity sections or their success/failure solver cost distributions.
- BL's compressed entry size (their §5) would lower bits per entry and so raise ΔT. I used 40 bits uncompressed.
- The small-α lever is purely conditional. Testing its scaling would need sizes beyond this budget.
- Correlation between attempts caused by walk merging is not modelled. The suggested non-learning fix (remembering failed distinguished points) is not a BL baseline, and I have not checked whether its effect at this scale is negligible.

Verified improvement over the baseline: **none**.
