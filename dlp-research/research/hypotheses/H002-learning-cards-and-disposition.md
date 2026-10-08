# H002 learning/tradeoff cards: retained ideas, corrected claims

Factory Fable5.1 completed four independent initial cards. Raw report and exact
task ID are preserved in H002-fable-initial-raw.md; no experiment ran. Coordinator
does not adopt its reductions, lower bounds, novelty claims or budget estimates.
These are speculative proposals awaiting independent skeptical review, not results.

## Retained mechanisms

| ID | Mechanism and hoped-for gain | Unsupported bridge | Cheapest useful test |
|---|---|---|---|
| L1 | Predict a scalar predicate from coordinates of several computable c_i Q; if advantage is usable, reduce search work | Stable out-of-sample advantage and an applicable efficient error-tolerant reconstruction algorithm | Small bounded pilot with unseen scalars, permutation controls, all feature/data-generation costs; then independent reconstruction review |
| L2 | Search short explicit coordinate-feature formulas instead of trained weights | A concise predicate with usable bias that transfers beyond selected data | Correct multiple-testing control, fresh curves/seeds and declared grammar; compare cost/bias after selection |
| L3 | Predict which starting points reach a precomputed distinguished-point table, avoiding unproductive walks | Endpoint membership predictable substantially cheaper than walking; gain survives training/storage amortization | Tiny table, disjoint starts, prefix ablation, compare complete work at fixed table/advice/preprocessing budget |
| L4 | Predict factor-base decomposability or choose elimination steps before/during polynomial solving | Filter reduces total successful-relation cost; solver-policy change helps actual target systems | Label cost first, then a bounded matched filter/no-filter test for one explicitly specified factor base and solver |

L1/L2 share the same scalar-predicate bridge and should be deduplicated into one
mechanism with two implementation routes unless independent advantages emerge.
L4 contains two separable components; do not count both as gains without testing.
Expected benefit is speculative. L3 initially targets constants/amortized work;
L1/L2 could affect exponents only with appropriate cost/advantage scaling; L4
has no exponent conclusion until actual relation yields and solver costs are known.
Training labels, features, model/formula storage, inference, retries and all
preprocessing count. Models need held-out targets and scaling evidence; per-curve
training is allowed only with its cost and amortization explicit. Nothing is free.

## Corrections before review or testing

1. [Corrigan-Gibbs–Kogan's primary author page](https://people.eecs.berkeley.edu/~henrycg/pubs/eurocrypt18discrete/)
   states a preprocessing lower bound for GENERIC algorithms with S-bit advice,
   online time T and success probability ε. It is not a universal coordinate
   bound or a test that all meaningful practical gains must violate ST²≈N.
   Ordinary BSGS with S≈T≈sqrt(N) does not satisfy ST²=N; it gives N^(3/2)
   even ignoring bit/log factors. A full lookup table is a different endpoint.
2. The raw information-to-kangaroo formula is unjustified. For example, side
   information revealing a uniform scalar entirely with probability α and nothing
   otherwise carries α log₂N bits of mutual information. The remaining1−α cases
   still have the original uniform search problem; an automatic work reduction
   to N^((1−α)/2) does not follow. Distribution, access and algorithm matter.
3. No exact noisy-bit-to-ECDLP complexity is accepted from the raw report.
   Specify the predicate, averaging distribution, oracle errors, adaptive queries,
   group assumptions and actual reduction. ECDH coordinate-bit security is not
   interchangeable with ECDLP scalar-bit recovery. Correct final candidates by
   scalar verification; sampling accuracy alone is not a solver result.
4. Training samples require scalar multiplication; multi-view features require
   actual additions/multiplications. They are computable, not free. The raw L3
   pilot alone proposes100000 labels times256 steps:25.6M walk steps BEFORE
   training, exceeding the1M initial cap. L4 m=2 labels are not free either;
   enumerating a factor base per target or preparing pair sums must be counted.
   No proposed60-second budget is accepted without an inspected implementation.
5. A finite accuracy/AUC failure rejects only the tested learner, grammar and
   parameters, not an exponent claim for every size or all algorithms. A failure
   at m=2 cannot exclude a different m=5 decomposition mechanism. AUC alone
   does not quantify useful precision/recall or full-solver work. Use fresh-data
   validation after model selection; multiple comparisons and uncertainty matter.
6. Bounds for individual features do not automatically exclude unrestricted
   linear combinations; feature count/coefficient norms and hypotheses matter.
   Explicit formulas still need generalization tests. Model size is not zero.
7. A finite prime-order GROUP has no proper nontrivial subgroup; a chosen walk
   can have closed subsets. Quotient-compatible walks are not necessarily group
   endomorphisms (negation orbit classes already illustrate the distinction).
   The raw broad exclusions of biased walks/pseudo-equivalence are not adopted.
8. Solver heuristics can change observed solving-degree growth; neither an
   exponent improvement nor a universal polynomial-only ceiling follows from
   calling something an ordering heuristic. PKM's actual algebraic factor-base
   mechanisms must not be replaced by an assumed interval-bit solver. Novelty
   for these combinations is UNKNOWN until primary-source review.

[Takhanov et al.'s primary paper](https://proceedings.mlr.press/v222/takhanov24a/takhanov24a.pdf)
is relevant prior art on gradient-based parity learning, not an unconditional
rejection of every possible coordinate feature or learning algorithm. Root has
verified its scope from the primary abstract; detailed theorem hypotheses remain
to be inspected before using it as a pruning theorem.

## Current priority

Keep L1/L2 as one high-risk mechanism with cheap corrected diagnostics, L3 as
an amortized constant-work hypothesis, L4 as a relation-generator hypothesis.
Do not launch the raw oversized pilots. Broader independent arithmetic, geometry
and algebraic cards are still arriving; rank across the deduplicated pool before
selecting experiments. Current best supported reference unchanged; improvement
NONE. These corrections prevent false rejection as well as false optimism.
