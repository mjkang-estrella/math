# I343 — random-SAT fluctuations beyond variance

Date: 2026-10-13. Research endpoint: **UNRESOLVED for a substantial fluctuation theorem**. No acceptance, count, shared-index, publication, or repository-history changes are proposed.

## Outcome

I did not prove asymptotic Gaussianity, full fluctuation-scale stretched-exponential concentration, or all-order centered moments for the stipulated independent proper random k-SAT clause process. I proved a stronger finite-range deletion estimate and used it to settle the Lindeberg requirement for a potential martingale CLT when k ≥ 4. Gaussianity now has one precise outstanding sufficient estimate in that route: predictable quadratic-variation concentration.

This is an unresolved research report with complete paid partials, not a generic corollary offered for acceptance as a substantial theorem. There is no demonstrated new-to-literature claim.

## Exact model and paid statements

Fix k ≥ 3, n ≥ k. Clauses independently choose k distinct variables uniformly, then independent fair signs; whole clauses are sampled with replacement. Hₙ is the first unsatisfiable prefix, counting the killing clause. For fixed B > 0 let L = ⌊Bn⌋, T = min(Hₙ,L), and Dᵢ = T⁽ⁱ⁾−T, where Cᵢ is omitted while all later indices are retained.

The independently proved endpoint bound is

\[
\sup_{n\ge k}\sup_{1\le i\le\lfloor Bn\rfloor}
 \sup_{c\text{ proper }k\text{-clause}}
 \mathbb E[D_i^{k-1}\mid C_i=c]<\infty.                  \tag{P1}
\]

An empty coordinate range imposes no condition. The proof generalizes the linear-3 bounded potential P_d = ∑_{j<d}qⱼ to (k−1)-clause tests, obtains a conditional occupation budget for q_d^{k/(k−1)}, proves higher remaining-duration moments by a conditional induction, and pays separately for **all** collision counts. With v collisions, 1 ≤ v < k, the conditional cost is O(d^{k−v}L^{v(k−1)/k}); its averaged contribution is O(n^{−v/k}). The event V ≥ k is paid by the cap and has contribution O(n⁻¹). These are quantified estimates for the exact clause process.

The finite-range centered-moment consequence is, for every fixed real 2 ≤ p ≤ k−1,

\[
\mathbb E|H_n-\mathbb EH_n|^p=\Theta_{k,p}(n^{p/2})
\]

for sufficiently large n, with the corresponding upper bound for every fixed cap B. The lower order uses the stipulated source variance lower bound. This improves the polynomial tail exponent over two for k ≥ 4, but gives only finitely many orders for a fixed k. The transfer from deletion moments is generic and is not counted as the requested substantial finding. At k = 3 the endpoint itself overlaps source variance machinery.

For k ≥ 4 choose B > Uₖ = log 2/[−log(1−2⁻ᵏ)], let ℱᵢ = σ(C₁,…,Cᵢ), Mᵢ = E[T|ℱᵢ]−E[T|ℱᵢ₋₁], and σₙ² = Var(T) = Θ(n). P1 implies, for every fixed ε > 0,

\[
\mathbb E\left[\sigma_n^{-2}\sum_i
 \mathbb E[M_i^2\mathbf1_{|M_i|>\varepsilon\sigma_n}
              \mid\mathcal F_{i-1}]\right]
 \le C_{k,B}\varepsilon^{-(k-3)}n^{-(k-3)/2}\to0.          \tag{P2}
\]

Thus conditional Lindeberg is paid. Also maxᵢ|Mᵢ|/σₙ → 0 in probability, and the realized sum ∑Mᵢ² differs from its predictable counterpart by o_P(n). These statements are proved in the analysis file, including the k = 4 case that lacks a uniform fourth deletion moment.

## Exact remaining estimates

For the Gaussian route at k ≥ 4 define

\[
Q_n=\sum_{i=1}^L\mathbb E[M_i^2\mid\mathcal F_{i-1}].
\]

We know EQₙ = σₙ² exactly. We do **not** know

\[
\boxed{Q_n/\sigma_n^2\longrightarrow1\text{ in probability}.}
\]

For example ∑_{i,j}Cov(E[Mᵢ²|ℱᵢ₋₁],E[Mⱼ²|ℱⱼ₋₁]) = o(n²) would suffice. The source bounds and P1 control individual moments, but provide no such joint estimate. If this missing estimate is proved, the standard martingale triangular-array CLT and the exponentially small late-cap error give the CLT for (Hₙ−EHₙ)/√Var(Hₙ). That implication is conditional; Gaussianity is not claimed.

For k = 3, Lindeberg itself remains unproved in addition to quadratic-variation concentration. Bounded E Dᵢ² alone does not establish uniform integrability.

For all-order concentration, a concrete sufficient missing estimate is all-order Lᵠ control of the conditional coordinate-resampling cost Gₙ = ∑ᵢE[(T−T^[i])²|C₁,…,C_L], such as ‖Gₙ‖_q ≤ Cn qᵃ for every q ≥ 1 with constants independent of n,q. The paid range is only q ≤ (k−1)/2. The potential/root-test balance ends at deletion order k−1, so the present calculation cannot supply the needed all-order input. This is an argument gap, not a counterexample to SAT concentration.

## Source authentication, overlap, and validation

The three hashes supplied in the brief were freshly retrieved from immutable raw GitHub URLs and matched exactly. The full 713-line linear-3 source, all ten earlier variance sections, and the relevant computability theorem/probability and certificate proofs were read. Additional pressure/structural sections were scoped by their actual statements; Gaussian tests there concern finite-temperature trial approximation, not Hₙ fluctuations. The source manifest records exact reading scopes rather than implying every unrelated pressure proof was read.

The later linear-3 result removes the earlier O(n log n) loss. The earlier variance companion already covers all fixed k ≥ 4, caps, Chebyshev concentration, endpoint conventions, and technical transfers. The computability paper supplies α₃, a one-sided certificate bound for an auxiliary relaxed Poisson law, and no fluctuation-scale two-sided bias estimate for EHₙ−α₃n. Every fluctuation statement here retains the exact finite-size mean.

Current primary literature checked includes Wilson's fixed-probability separation, Carenini's October 5, 2026 polynomial-window/variance theorem, the 2024 random-2-SAT solution-count CLT, and the relevant martingale and Efron–Stein moment criteria. No theorem meeting this round's target for the exact fixed-k hitting time was located; this bounded search is not a proof of absence. See the literature file for primary links and reading limits.

Validation is analytic, not numerical: the exceptional k−1-frozen-coordinate error is retained; the two filtrations are preserved; remaining-duration moments use a genuine conditional induction; zero killing probabilities and the j = 1 collision case are handled separately; every root-collision count is averaged using its joint incidence moment; real-p centered moments and cap floors are accounted for. The abstract folded-normal example in the analysis shows why even bounded deletion moments do not imply a CLT; it is explicitly not a SAT counterexample.

A further exact structural check shows E[g(Hₙ)|Cᵢ] = E g(Hₙ) for each individual clause and bounded measurable g, by transitive variable/sign symmetry. Hence first-order clause Hoeffding projections vanish. Arbitrary clause-coordinate permutation symmetry fails, as witnessed by a complete set of 2ᵏ clauses plus a duplicate; no such false symmetry is used.

## Deliverables and finite endpoint

- [Complete proofs and exact gaps](../experiments/i343_sat_fluctuation_discovery/analysis.md).
- [Reading scopes, failed routes, and validation audit](../experiments/i343_sat_fluctuation_discovery/reading-and-failures.md).
- [Immutable-input authentication](../experiments/i343_sat_fluctuation_discovery/input-authentication.json).
- [Primary literature and overlap record](../sources/i343_sat_fluctuation_discovery/literature.md).

The round ends with P1, the finite moment range, and P2 proved, and the substantial target unresolved. No continuation is disguised as an achieved theorem. Detached SHA256 values for these five finalized files are returned outside their contents.
