# I343 reading, failed routes, and validation

Date: 2026-10-13. End state: paid endpoint moments and Lindeberg for k ≥ 4; substantial fluctuation target unresolved.

## 1. Reading and authentication

Read the supplied discovery brief in full, project AGENTS.md, sources/upstream.json, the SAT entries in sources/CONTENTS.md, and the relevant paths from sources/preprints-tree.json. The stipulated upstream revision was used for every upstream retrieval. No theorem was accepted from a catalogue summary alone.

### Linear-3 source

Read all 713 lines of preprints/Linear-Variance-of-the-Random-3-SAT-Hitting-Time-October-5-2026/build/source/main.tex. The freshly retrieved full-byte SHA256 was 888db8d247151937a55c67a14f7b014bb9a6c812639680dd300ea5df94adfcf4, matching the parent brief.

Important actual statements/proofs:

- thm:main, lines 61–70: linear variance about the exact Hₙ.
- lem:one, lines 179–209: falling-factorial one-clause comparison, including the exactly-two-frozen-coordinate error.
- lem:potential, lines 216–264: bounded P_d and drift control of q_d^{3/2}.
- lem:omission, lines 284–304: clause-prefix martingale reduction.
- Conditional product exposure and the two filtrations, lines 306–378; lem:tests, lines 382–418: root-flip independence and collision losses.
- lem:occupation and cor:duration, lines 428–488: conditional occupation and remaining mean duration.
- prop:delay, lines 496–537; lem:moments, lines 545–589: the squared-delay balance and collision averaging.
- First-moment cap removal, lines 605–634, and thm:wilson/cor:window, lines 636–704.
- Lines 706–709 explicitly leave a limiting centered law unasserted.

The source does not prove higher remaining-duration moments merely by giving their mean. Our proof supplies a conditional induction at every later history. Its new general-k potential retains the exceptional frozen-coordinate error and pays its finite-cap contribution.

### Earlier variance source

Read the ten files in preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/build/source/sections/ in full: introduction.tex, replacement.tex, deletion.tex, occupation.tex, conventions.tex, lower-bounds.tex, three-clause-refinements.tex, replacement-sharpness.tex, direct-comparison.tex, appendix-c.tex. Bodies were freshly fetched in memory from pinned raw URLs; the manifest records individual SHA256 values and line counts. The full introduction hash dc63bb28e88b320d713cbfe8bedc453b5aa783fd9516cc7cbae15cdcd717a248 matched the supplied parent hash.

The main proof gives a lifetime product with β = k/(k−1), not a pathwise bounded duration. Its occupation integral has exponent k−2β−1; the earlier k = 3 logarithm is removed by the later bounded potential. Actual root counts d = max(1,Z), rather than logarithmic incidence truncation, are essential to its sharper general-k result. The joint factorial identity for incidence/collision counts supplies the averaging needed in this round's higher-moment proof.

The source pays V = 0, V = 1, and V ≥ 2 because its target is a second moment. Reusing only those cases for a third moment would leave a term L³P(V ≥ 2) = O(n). Our proof instead uses k−v surviving root tests for every 0 ≤ v < k, and reserves the cap-only treatment for V ≥ k. That difference is necessary for the endpoint k−1 moment.

The two sharpness propositions concern arbitrary assignment subcubes. They delimit uniform replacement/lifetime exponents. They do not prove a lower bound on moments of deletion delays encountered in the actual SAT process. direct-comparison.tex and appendix-c.tex contain center comparisons and alternative variance arguments, but no two-sided √n bias rate or fluctuation limit.

### Computability source

Read the full introduction (91 lines), probability.tex (724 lines), sensitivity.tex (164 lines), proof-map.tex (115 lines), certificates.tex (60 lines), and assembly.tex (66 lines). The introduction hash ce097bf0270147675456facc16237707e48a6cff8bd21fc1e5b51849600ae58c matched the parent. The probability proof was read through its free variable-deletion bound, interpolation, one-sided mean bound, strict-side transfer to proper clauses, finite computation, and robust-unsatisfiability/soft-pressure sign proofs.

Scoped actual statements in the larger pressure sections were also inspected: transition.tex lines 1–140, including ct:transition; theorem/lemma inventories and statement windows in closure.tex and trials.tex. Their roles are finite hierarchical pressure approximation and rational witness completeness. No claim of reading every unrelated structural/pressure proof is made. The manifest separates full reads from these statement inventories.

The 6/5 free-variable-deletion moment in probability.tex concerns a relaxed Poisson clause law with repeated variables inside a clause, even under other allowed deletions. It is not the index-preserving proper-clause omission Dᵢ used here. The bound α ≥ fₙ/n−2⁶⁷n⁻¹/⁶ is one-sided and uses that auxiliary law. The witness-search proof is expressly designed to halt without a convergence modulus; it does not supply |EHₙ−α₃n| = o(√n).

### External primary reading

Consulted the primary Wilson preprint, Carenini ECCC TR26-229 (October 5, 2026), the 2024 2-SAT solution-count CLT proceedings paper, the Boucheron–Bousquet–Lugosi–Massart moment paper, and the actual triangular-array martingale criterion in Péter Major's authored proof notes. Exact links and limits of those comparisons are in literature.md. Major's notes explicitly require both conditional variance convergence and conditional Lindeberg; the first has not been proved for this Hₙ.

## 2. Routes tested and their exact stopping points

### A. Variance order ⇒ Gaussianity

Rejected. Var(Hₙ) = Θ(n) identifies a scale and fixed-level windows but not a distribution. Even uniformly bounded omission moments of all orders need not force Gaussianity. The folded-normal product-measure example in analysis.md gives an explicit logical countermodel with vanishing first-order projections. It is not a counterexample to SAT.

### B. Martingale CLT with only an averaged variance bound

Initially two obligations remained: Lindeberg and predictable quadratic variation. The endpoint deletion theorem pays Lindeberg for k ≥ 4 with an explicit n^{−(k−3)/2} expectation bound. It also pays the difference between realized and predictable squared increments. The remaining sufficient estimate is precisely Qₙ/Var(T) → 1 in probability. Its expectation is already one after normalization, but concentration has not been derived. A sum of marginal moment estimates is not a covariance estimate.

At k = 3 the endpoint moment is only two. Uniform boundedness of those moments does not imply their uniform integrability; Lindeberg remains an additional unproved obligation.

### C. Higher powers from the source remaining-duration mean

The shortcut E[Nʰ | history] ≤ (E[N | history])ʰ is false. Corrected by exploiting a uniform mean bound at **every future history**, whose upper bound decreases because q_d(Sₘ) increases. Conditional induction yields h! times the h-th power of that bound. This is an actual paid subclaim, proved before its use in the deletion-moment calculation.

### D. Generalized potential and all-order deletion moments

Successful only up to the finite endpoint k−1. The general-k drift has β = k/(k−1), the collision-free test exponent is k, and a-th moments consume (a−1) duration powers plus one occupation budget. Thus aβ ≤ k closes uniformly, with equality handled by the bounded potential. Above a = k−1 the small-q exponent fails. The cap yields an n-dependent estimate; it cannot be advertised as uniform all-order control.

The sharpness examples in replacement-sharpness.tex explain why decreasing β uniformly over arbitrary residual sets cannot repair the argument. They do not exclude a stronger estimate using structural information about the states actually visited. No such extra estimate was established in this round.

### E. Treating rare collisions by the same crude cap as variance

Rejected for higher moments and repaired. The source's coarse V ≥ 2 case would lose the desired higher-moment scaling. The proof now retains the number of available roots for each V = v < k. The j = 1 test case is handled separately, because dividing its contribution by p^β would be invalid at p → 0. Averaging uses joint weighted collision moments, not independence of d and V. Every endpoint collision cost is O(n^{−v/k}), and V ≥ k costs O(n⁻¹).

### F. Sparse first-order Hoeffding expansion

There is an exact obstruction to first-order projection dominance: E[g(T)|Cᵢ] = E g(T) by transitive variable/sign symmetry. The same holds for Hₙ. Thus all first-order projections vanish. This is a complete structural subclaim, proved in analysis.md. It does not disprove a CLT in higher chaos; that route would still require dominant chaos identification plus appropriate contractions/cumulants. Neither is paid by source root-incidence sparsity.

It would also be incorrect to assume the first-hitting functional is symmetric under arbitrary clause-coordinate permutations. A complete family of 2ᵏ clauses plus a duplicate provides a direct admissible order-dependence example. This is distinct from variable/sign symmetry.

### G. Subgaussianity from bounded expected Efron–Stein cost

Rejected. Source deletion second moments control EGₙ = O(n). Exponential concentration requires stronger distributional control of the conditional resampling cost, such as the all-order norms stated in analysis.md, Section 9. The root-incidence count has bounded exponential moments, but the deletion duration remains a separate random quantity. Its finite-range moment bound cannot be replaced by the incidence count's exponential tail.

### H. Regeneration by clause-exposure intervals

No regeneration theorem was proved. Independent input blocks do not give independent hitting-time increments: the residual solution set depends on all previous clauses and persists between blocks. The root-exposure argument guarantees fresh ordinary contents only under its specified conditional law. It does not reset the residual set or create iid interval rewards. A useful missing ingredient would have to control the conditional residual-state transition, not just fresh input independence.

### I. Cap removal, Poissonization, quantiles, computability, and center replacement

Cap removal at B > Uₖ is paid with exponentially small fixed-order errors; it is already a technical source mechanism. The CLT reduction remains centered at ET for the cap and EHₙ for the uncapped process. No αₖn replacement is made. Wilson's fixed-level comparison is not silently converted into a density theorem. Source companion transfers and computability do not satisfy the substantial-discovery gate.

## 3. Independent proof validation

The following checks were completed analytically and are written in full in analysis.md.

1. **Exact clause law.** Falling factorials use distinct variables; signs are fair; repeated whole clauses remain allowed. The exceptional b = k−1 frozen subcube gives an Oₖ(u⁻ᵏ) error, never a positive single-clause kill probability.
2. **Potential telescoping.** All potential increments are nonnegative. Ordinary contents remain fresh under ℋₘ; nonordinary steps are charged individually. The finite-cap error is bounded using u ≥ n/2 and L ≤ Bn.
3. **Compatible conditioning.** Root tests are conditioned under 𝒢ₘ, duration under ℋₘ; the duration upper bound is 𝒢ₘ-measurable. Conditioning proceeds in that order before averaging over ℰ.
4. **Zero probabilities.** pₘ = 0 is assigned Wₘ = L, and the root-test factor vanishes for every j ≥ 1. No expression 0 × infinity is used.
5. **Higher duration induction.** Each later history has the same conditional occupation budget and a no-larger inverse-q upper bound. This proves factorial moment control rather than applying reversed Jensen.
6. **Endpoint arithmetic.** rβ = k; k−(r−1)β = β; r−(k−v)/β = v/β; v/β−v = −v/k. The separate j = 1 bound has the same endpoint exponent. An exact formal polynomial checker verifies these identities without numerical parameter scans.
7. **All collisions.** Cases V = 0,…,k−1 retain available-root tests; only V ≥ k uses the raw cap. Weighted incidence/collision moments are proved by expanding factorial collision counts. No independence between Z and V is assumed.
8. **Small sizes/caps.** L = 0 and i = L are trivial. The finitely many n < 2k have bounded caps and are absorbed in fixed constants. Floors contribute the qₖ⁻¹ factor in the late-cap error.
9. **Moment transfer.** Doob increments have bounded p-moments via conditional Jensen; their centered sum is bounded using a Taylor/Hölder recurrence. It does not presume independence of martingale differences.
10. **Gaussian checklist.** Conditional Lindeberg is verified in L¹ at k ≥ 4. Realized/predictable variation differences are controlled by 3/2 moments at k = 4 and fourth moments at k ≥ 5. Predictable variation concentration itself is left open explicitly.
11. **First-order degeneracy/order dependence.** Proofs use only the correct group action or explicit admissible clause lists. The folded-normal example is labeled as an abstract implication countermodel.
12. **Novelty gate.** Source second-moment, central-window, cap, and endpoint/Poisson consequences are overlap. Finite-order moment transfer is a paid partial, not certified as the requested substantial theorem or a new-to-literature result.

No empirical random-SAT runs, finite-size numerical scans, or statistical evidence were used. There was no Lean formalization or independent second-agent review. The proofs, not a numerical test suite, carry the mathematical claims.

## 4. Operational and retrieval record

Only the five assigned output files were written. No child agents, git commands, publication, shared-index or acceptance edits, live-sibling artifact reads, or retained full external source bodies were used. An initial read-only path inventory ran from the parent workspace before the brief's project-cwd rule was applied; it listed paths but read no other project's file bodies. Every subsequent filesystem command used openai-proof-research as its working directory. The supplied brief itself was read from its explicit project path.

Large source output was sometimes truncated by the tool display; the relevant sections were re-emitted or refetched in smaller scopes before reliance. The optional fitz PDF library was unavailable, so the installed pdftotext was used with in-memory input and stdout. No package was installed. A Yale-hosted textbook request failed certificate verification, and the Brown publisher page exposed an iframe only; the accessible authored Major notes supplied the actual CLT criterion. SymPy was unavailable; the validation uses a tiny in-memory exact polynomial checker instead, with no installed dependency or retained script.

Finite endpoint: finalize the endpoint moment proof, finite centered moments, and k ≥ 4 Lindeberg; state GAP-G and the separate all-order resampling-cost gap; stop this round. Do not replace these unproved estimates by claims based on literature search, heuristic regeneration, or accepted-claim pressure.
