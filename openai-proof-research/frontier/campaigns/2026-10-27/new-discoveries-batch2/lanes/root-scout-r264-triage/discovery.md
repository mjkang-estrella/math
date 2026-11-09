# Sustained attempt: subsequential separation, not a source resolution

Target: Pavlenkov2610.29551v1 §4.4 as quantified in SCOUTING item1. The same iid law of Y must generate BOTH subsequences. Normalize on S_n>0; its complement has probability tending to zero. Center X, writing EX=0. Lemma3.1 gives limits Z(P)=ΣP_jX_j (dust contributes EX=0) and d(P)=EΣP_j². The source already proves finite variance, endpoint d=0, endpoint d=1, and stable-plus-Gaussian marks; none is a discovery here.

## Mechanism A: truncation and convex test functions

For symmetric integrable X set X_M=sign(X)min(|X|,M), also centered. Conditional contraction gives E|Z(P;X)−Z(P;X_M)|≤δ_M=E(|X|−M)_+, uniformly in EVERY random subprobability partition. For bounded X_M the exact identity is E Z(P;X_M)²=σ_M² d(P). If the original two marked limits agree in law, truncation only gives Wasserstein distance at most 2δ_M between the truncated marked limits. Since these are supported on [−M,M], the square function is 2M-Lipschitz there. Thus

    σ_M² |d(P)−d(Q)| ≤ 4Mδ_M.

This is a valid bound but does NOT force the desired equality for arbitrary integrable X. For symmetric Pareto |X| with P(|X|>t)=t^(−3/2) for t≥1,

    δ_M=2/sqrt(M),   σ_M²=4sqrt(M)−3,
    4Mδ_M/σ_M²=8sqrt(M)/(4sqrt(M)−3) → 2.

Exact rational checks at square cutoffs are retained. An attempt to use convex truncated quadratic functions encounters the same tail-scale contribution; no unproved exchange of the M→∞ and subsequence limits is used. This is an obstruction to this PARTICULAR quantitative truncation route, not proof of falsity of the conjecture or of all truncation arguments.

The source's absolute-value Jensen gap gives a strict loss from the original X when d<1; it is one-sided and does not order two arbitrary internal d values. Strict convexity likewise compares partitions under an actual refinement coupling. No such ordering follows merely from d(P)<d(Q).

## Mechanism B: stable characteristic products, then iid realizability

Take a symmetric α-stable integrable mark, φ_X(t)=exp(−|t|^α), with α=log(2)/log(3/2). Because 3/2<2<(3/2)², 1<α<2. Consider deterministic subprobability partitions

    P=(3/4,0,0,…), with dust1/4;
    Q=(1/2,1/2,0,…), with dust0.

Their marked characteristic functions are identical for ALL real t, since (3/4)^α=2(1/2)^α, while

    d(P)=9/16, d(Q)=1/2, d(P)−d(Q)=1/16.

Thus the tempting arbitrary-mass-partition strengthening of the source is rigorously false, even with a nondegenerate integrable mark. This is a classical stable-law mechanism, receives NO separate credit and is NOT a refutation of the source. The missing hypothesis is precisely realizability as two limits from ONE iid nonnegative weight law. It cannot be supplied by conditioning on a desired number of large weights.

To move beyond that shortcut, consider the standard rare-level iid construction: if a level occurs with probability q_k→0 and n_k q_k→c>0 while higher levels disappear, the count at that level converges to Poisson(c). A fixed deterministic number of large atoms does not result: P(N=j)=e^(−c)c^j/j!, with every nonnegative j retaining positive mass. With negligible lower-level sum and at least one large atom, the conditional partition has N equal atoms. Its stable scale is K=N^(1−α), and d=1/N. K is strictly decreasing in N≥1, so equality of its FULL distribution determines that of N and therefore d. A collision in a finite sweep of expected K would not suffice. Empty-level and nonnegligible dust cases also must be retained, not conditioned away.

With lower-level drift b and large-jump size a the compound-Poisson model instead has

    K=N/(b/a+N)^α,    d=N/(b/a+N)²,
    K'(x)=(b/a−(α−1)x)/(b/a+x)^(α+1).

This nonmonotonicity leaves an inverse-law problem; matching one moment does not match the entire K distribution. No pair of full normalized-jump laws with identical K law and different expected d, and no common-iid embedding, has been established. These formulas identify a concrete next calculation, beyond a finite sweep or one failed shortcut.

## Closest actual prior proof and a third bridge check

Lenzi2608.24616v3 predates the source: version3 dated10 September2026 versus Pavlenkov21 October2026. Actual Thm6.3 proof uses the full-sequence inverse theorem5.1 and depoissonization; Remarks9.2/10.5 explicitly prohibit replacing endpoint limits with subsequences in the relevant elasticity/Tauberian steps. Thms2.1/2.2 are stronger local tools than finite variance but do NOT automatically identify quadratic concentration for every mark: for moment abscissa α∈(1,2), the universally supplied limiting power sum is at α. The exact stable collision above explains that distinction.

Conditional on a fractional power-sum bound EΣP_j^r≤C, r<1, Lenzi Thm2.1 says that marks with moment abscissa1 force convergence of each expected power sum for 1<p<2. Interleaving the two candidate sequences then gives equality of those power sums; bounded holomorphic power-sum transforms on Re(s)>1 and the identity theorem would give equality at2. This is a source-dependent subclass bridge, not a new standalone result. The required r<1 bound is absent from the arbitrary-subsequence hypothesis; no blanket application is justified. For stable marks the abscissa lies strictly between1 and2 and the bridge does not apply.

Gao–Konstantinides–Passalidis–Wang–Xu2602.23112v4 was checked after the current Breiman search. Its actual Lemma2.2/proof machinery extends product-tail Breiman asymptotics in risk models, not the normalized-weight subsequential separation assertion. This is a title/alias exclusion, not an asserted subsumer.

Status: INCOMPLETE; no ordinary proof/refutation of the full source result, no PROOF.md, no formalization or manuscript. Decisive next work is the compound-Poisson/normalized-subordinator inverse-law problem with common-iid realizability, or a source-specific theorem obtaining quadratic concentration directly from a marked subsequential law. Novelty and current registry gates remain HOLD.
