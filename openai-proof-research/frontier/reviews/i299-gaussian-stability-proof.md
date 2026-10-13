# I299 — independent proof review of restricted global soft stability

2026-10-13. **PASS unchanged.** This verdict concerns the complete S295 proof chain, including the needed internal I128/I131/I290 deductions. It is conditional only on the user's stipulation that the OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true. Internal reports' prior verdicts were not treated as premises.

The frozen target analysis has SHA256 `70992530f4413ff1a7ce8149dc5643cfd2215ca2bb85f2a5861ee70e405ef813`; its report has SHA256 `59868a55043dd3096446672ad0b4f3609003309fc936f2b40970f5cde1fa5cea`. Both match. The I290 analysis matches `2057261d4defe12b348fc97625130cf909e345c99d83a26ead7947171d794cf5`. All 17 distinct local input hash records in I295's manifest match. These byte checks are separate from the independent proof review.

The result passed is exactly this: for uniform X on {-1,1}^n, arbitrary u:X→[-1,1], ψ(t)=((1+t)log(1+t)+(1−t)log(1−t))/2 and I(u)=Eψ(u)−ψ(Eu), every rectangle

    0<a₀≤a₁<1, 0<ρ₀≤ρ₁<1, ρ₁a₁<1/√2

admits a finite C depending only on its four endpoints such that, whenever exactly I(u)=ψ(a),

    min_(i,ε=±1) E|u−εaX_i|²
      ≤C[ψ(ρa)−I(T_ρu)]

for every n≥1, a∈[a₀,a₁], and ρ∈[ρ₀,ρ₁]. No balance, initial proximity, endpoint exclusion, support, rank, degree, or complexity condition has been added. C is existential.

The [independent analysis](../experiments/i299_gaussian_stability_proof/analysis.md) explains the checked deductions:

- Borell, exact-law quantiles, compatible upper halfspaces, layer cake and stop-loss order give R295, preserving both input law and mean.
- Scalar ordinary EPI applies separately to the biased binary posteriors, whose entropies and moments are finite even at kernel endpoints. Convex Jensen has the stated direction. Rearrangement precedes EPI and removes the dimension factor.
- The displayed curvature calculation and strong-convexity chord estimate give the claimed uniform positive Gaussian gap below amplitude 1/√2.
- I128's secant ODE has the correct sign and bounds earlier-time deficit by terminal deficit. A fixed unequal split λ>ρ₁ places λa in the Gaussian gap's range.
- Fixed-degree replacement, mixed fourth-moment bounds, the unbounded clipping-distance test, entropy/mean continuity and exact information normalization transfer both budgets. The degree is fixed before singleton size tends to zero.
- J290's strict joining equality classification follows in both parent branches from the actual canonical, reserve, capacity, thinning and wall operations. M290's fixed-square compactness and lower semicontinuity then give P290. B290 pays global entrance, the original-budget backward step, and local linear stability.
- Q131b and L131 were checked from their actual proofs. Compression preserves the information budget and pays the distance transfer; L131 permits spikes and boundary values. They close the arbitrary-kernel conclusion.

The explanations in this review elaborate valid existing steps. No invalid original step was replaced, no theorem was weakened or strengthened, and no substantive repair was needed. The case n=1, compact parameter endpoints, zero deficit and nonsmooth kernels are included by the same argument.

Full all-rectangle S128 remains unresolved here. Scalar monotone compactness is valid, but the large-amplitude pointwise cube-curve strictness U295 remains unpaid. Strict EPI addresses a different curve; ordinary LSI strictness does not pay the nonlinear reserve; complex analyticity hypotheses are not established. None is used to pass S295.

The [reading log](../experiments/i299_gaussian_stability_proof/reading-and-failures.md), [authentication record](../experiments/i299_gaussian_stability_proof/input-authentication.json), and [primary-source record](../sources/i299_gaussian_stability_proof/literature.md) state exact read scopes and limitations. This is a proof verdict, not an acceptance, contribution, or worldwide-novelty judgment. Thirteen toward twenty is user-supplied context and is unchanged. No subagents, live sibling reads (including I298), shared-ledger edits, numerical scans, staging, commits or publication occurred. Detached SHA256 values for the five principal authored files are returned separately.
