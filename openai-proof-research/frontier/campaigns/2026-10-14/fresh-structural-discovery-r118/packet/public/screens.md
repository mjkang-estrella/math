# Other structural/discrete screens and precise interfaces

All entries are prefreeze. No complete monotone-Boolean, descriptive-matroid or fast general-factor target was frozen. Method obstructions below are not universal impossibility results.

## 192: reporting, mean cell cost, and monotonicity

The source's basic report uses a selector i(u), leaf interval tests, B=all leaves passing, P=all unselected leaves passing and A=P minus B. Its indicator expansion subtracts B from a sum of selected-index terms, saving one coordinate in every cell's algebraic degree. This is an exact pointwise indicator identity, not a decision-tree query bound. The retained conditional score on the rare event has variance saving, and the source already gives finite iteration and final Boolean readout without losing the indicator degree.

The actual alternatives are stronger than just this basic rule. `lem:coarse-report` merges all-pass reports into one mark and computes their exact loss, leaving positive gain. The independent-extra-input rule has `eq:switching-variance` and `eq:switching-correction`: q+p(1−Var(L|A)), with correction from the chosen predictor to the conditional mean. `lem:refinement` makes a finite grid on A's complement so retained variance exceeds average cell cost. `thm:mean-cost` retains whole label words under a total-cost threshold and merges the other words into one failure label. The complement identity bounds failure-label degree; a fourth-moment bound for the fixed finite observation controls its variance loss, and a CLT plus L2 closeness restores the iteration invariant. `lem:mc-transfer` requires no fourth moment for its fixed-partition first-moment transfer. These full operations were read; heterogeneous costs, rare cells and repeated CLT restoration are already supplied.

The direct reporting score does not preserve coordinate monotonicity. Fix u and all unselected leaves inside their intervals. As the selected leaf moves below/through/above its interval, the report is A, B, A. The A score is the same constant on both sides; the B score changes with the selected leaf. A nonconstant function with equal constant tails cannot be monotone. This concerns the score operation, not every possible final threshold sign and not all alternative constructions.

A classical Boolean coordinate compression also fails to preserve degree in general. The multiplexer

    f=(x2+x3)/2+x1(x2−x3)/2

is Boolean of degree two. Sorting each x1 pair into increasing order replaces its linear coefficient b by |b|=(1−x2*x3)/2. The resulting Boolean function

    g=(x2+x3)/2+x1(1−x2*x3)/2

has degree three. This only defeats this compiler. In particular it is not a counterexample to a monotone influence bound.

The actual [Filmus–Hatami–Keller–Lifshitz v3](https://arxiv.org/pdf/1404.3396v3) Lemmas 3.14–3.15 preserve total L1 influence by averaging a monotone real-valued function over permutations and then comparing a univariate polynomial. Theorem 3.16 is for values in [−1,1], not just Boolean values. The averaging loses Boolean values; applying sign has no general Fourier-degree preservation (a linear sum's sign can be majority of full degree). Thus it supplies no missing Boolean compiler. R25's complete cyclic-disjointification and wreath-product comparison was read; it already retains source conditional laws under cyclic symmetry. Renaming that construction as a symmetry extension would not supply a new operation. A genuine monotone event/indicator amplification with positive variance advantage remains unbuilt here.

## 185: ordinal descent versus a regular replacement

The pinned `lem:selfdual-reduction`, `lem:columns`, `lem:ultrafilter`, `lem:thinning`, `lem:reservations`, and the full double-ray counterexample were inspected. The two parity direct sums place a self-dual local matroid on adjacent countably infinite bundles. An alleged independent covering propagates an ultrafilter-large part outward and forces a strict infinite ordinal descent (`eq:ordinal-descent`). Finite changes do not affect the two relevant ideals/ranks. The consequences section's universal packing/covering failures are already paid.

R21's actual checkpoint constructs connected self-dual counterexamples by standard elongation followed by truncation. Its proof preserves the descent under finitely many errors in each local component, not merely a uniformly bounded total error. R32 also records this antecedent. Bowler–Geschke's [author version dated 6 October 2014](https://www.math.uni-hamburg.de/home/geschke/papers/UniformMatroid7.pdf), Lemma 4, Theorem 6, complete Theorem 8 and Theorem 10 proofs were read. Theorem 8 says a uniform matroid that is neither finitary nor cofinitary is infinitely connected. It does NOT say that arbitrary source direct sums become infinitely connected or supply a tameness theorem. Its uniform exchange argument and the primary truncation definitions already account for the obvious connectivity routes.

R114's `screen-185.md`, read late before any freeze, already asks the Borel-independent-family question and examines the source classifier plus determined circuit games. Its auxiliary free ultrafilter cannot itself be Borel, by finite-change invariance/zero-one law and complement symmetry. That does not prove the final independent-set family non-Borel. Its actual primary circuit-game comparison has finite local pieces/overlap-one interfaces different from the source's infinite bundles and local Q. This round did not newly read the circuit-game primary or solve that interface. No obstruction-preserving regular replacement was constructed, and neither a tame nor a finite/local substitute is offered. This direction is an inherited open interface, not a newly discovered question.

## 120: factor networks and the actual general-factor oracle

Pinned `thm:main` already gives one uniform randomized word-RAM program for explicit maximum cardinality matching, with every-path input-size almost-linear bound, charged randomness, arithmetic, unsuccessful computations and output. `factor:reduction` and `cor:f-factor` already give prescribed-degree factors through incidence ports and logarithmic-size rearrangeable networks. The exact f array is part of the input. The reduction proof and main interface were freshly read; the entire matching backend was not reread.

R35's signed-weight attempt lacks a weighted dual invariant; two expensive odd bins can expose the cost of losing their internal edges. R111's actual interval/parity factor reduction already uses dummy vertices and matching-realizable degree sets. Those are prior operations, not fresh weighted or general-factor work.

The strongest further primary examined was Shao–Zivny's [ISAAC2023 author preprint](https://www.cs.ox.ac.uk/standa.zivny/publications/sz23isaac-preprint.pdf), particularly Theorem 5 and Lemmas 7–8/Algorithm 1 interfaces. Its degree-three exceptional types are {p,p+1,p+3} and {p,p+2,p+3}, split into a parity pair D0 and a singleton D1. The recursive algorithm assumes a *Decision oracle for the enlarged general-factor class*, in addition to Optimization for matching-realizable restrictions. It invokes up to n Decision calls and quadratically many Optimization calls. Theorem 5's local-exchange condition uses an optimum in D0; the version with an optimum in D1 is not supplied. Thus substituting a fast prescribed-factor solver neither supplies that Decision oracle nor batches the quadratic calls. The short version refers its central structural proof to the full paper, which was not newly acquired here. No theorem depending on that unread proof is claimed. A truly subpolynomial-call/witness-preserving implementation remains absent, as does a full weighted matching reduction.

## Further actual history, unequal depth

* 168: r111's marked-generator/parabolic comparison already covers the apparent simple recurrence extension; its full screen was read. No fresh primary proof was acquired here.
* 171: r32's full screen and actual later r114 operation passages exclude all-r linear growth (the first-moment obstruction for r>=5), and distinguish the unresolved r=3,4 density/label budget. R48 was searched, not reread completely. No sparse-host repair is substituted.
* 175: r111's complete screen already supplies a compatible heterogeneous-component saturation construction; no new parameter variant was pursued.
* 190: r23's checkpoint already computes the bounded row/column VC-dimension transfer and compares the smaller ordered matrix result. Its primary is historical evidence here, not a fresh full primary read.
* 180: the large I164 body was content-searched and its square-expansion/signed-state passages inspected; the full output truncated. Hamiltonian counting/affine-span extraction was not closed. It is not classified from a title.
* 187: r101's working-threshold body distinguishes the paid biased Snaky response from remaining biases. No new response tree was produced.
* 161: I13's actual regular-pattern identity explains why the regular score collapses; the full combined display truncated and is not treated as full-family clearance.
* R113's actual report excludes its existing 176/130/238/097 routes. I198's source095 regularization discussion was inspected as an exclusion. These are bounded history screens, not fresh full source investigations.

No negative author verdict was used as the reason to stop a family. The reasons are the actual compatible operation or the precise unconstructed interface above. None asserts exhaustive literature clearance.
