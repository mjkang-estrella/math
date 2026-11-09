# 328389: full ordinary route; zero credit, classical-subsumption objection

Read Fincher–Olney–Cherry, arXiv:1407.5850, Proposition 6 including its proof (text lines 155–223), Theorem 11 proof and Conjecture 12 (lines 310–383). The source uses chordal/Fubini–Study distance |u∧v|, not its arcsine. The following argument addresses that convention.

Put N=n+1≥2, δ=D², and let A have the unit vectors as columns. Its positive definite Hermitian Gram matrix G=A* A has diagonal 1, trace N and determinant δ. Proposition 6 and the Gram determinant identity give d_i²=δ/det(G with row and column i removed)=1/(G⁻¹)ii. Thus d_min²=1/max_i(G⁻¹)ii. This is a semantic bridge, not an assumption about equal edge lengths.

## Scalar minimization proved in ordinary mathematics

On the set of positive λ₁,…,λ_N with sum N and product δ∈(0,1), minimize T=∑1/λ_i. This set is compact: each λ_i≤N and λ_i≥δ/N^(N−1). Its constraint gradients (1,…,1) and (1/λ_i)_i are independent, because δ<1 excludes the all-equal point. At any minimizer Lagrange multipliers α,β give

α λ_i²+β λ_i+1=0.

Consequently the coordinates have precisely two distinct positive values a<b. (One value would force every coordinate to equal 1.) Their quadratic has α=1/(ab), β=−(a+b)/(ab). For L=T−α(∑λ_i−N)−β(∑log λ_i−logδ), the constrained Hessian is diagonal, with entries 2/λ_i³+β/λ_i². At λ_i=b this equals (1−b/a)/b³<0. If b occurred at two indices, the vector with entries +1,−1 at those indices and 0 elsewhere would be tangent to both constraints and have strictly negative Hessian quadratic form. The second-order necessary condition for a local constrained minimum forbids this. This condition applies on the smooth constraint manifold by gradient independence; its tangent vectors are realized by smooth curves through the point, and the first-order multiplier equation removes the normal acceleration term.

Therefore b occurs once, a occurs N−1 times, b=N−(N−1)a and a^(N−1)b=δ. Necessarily 0<a<1<b. The function a↦a^(N−1)(N−(N−1)a) is strictly increasing from 0 to 1 on (0,1): its derivative is N(N−1)a^(N−2)(1−a)>0. Hence this a is unique, and every minimizer has that spectrum. For δ=1 AM–GM gives λ_i=1 directly. This also handles N=2; the potentially negative tangent direction is needed only when b repeats.

## Exact optimizer

For every admissible Gram matrix,

max_i(G⁻¹)ii ≥ tr(G⁻¹)/N ≥ ((N−1)/a+1/b)/N.

Set G*=a I+(1−a)J, with b=N−(N−1)a. This matrix has diagonal 1, eigenvalues a (N−1 times) and b (once), determinant δ. Its positive square root supplies unit column vectors. All distinct inner products are 1−a; thus these vectors give a regular projective simplex. Its inverse has constant diagonal, attaining both inequalities. In particular the exact maximum of d_min² is

Nab / ((N−1)b+a).

The argument proves existence of a regular maximizing configuration, as requested, without claiming uniqueness of all maximizers under an undefined stronger notion of complex regularity. N=1 has no opposite nonempty face and is outside the meaningful source distance setup.

## Why this is not offered as a new significant solution

After deriving the above route, primary comparison located Aliyev, Journal of Inequalities and Applications 2024:29, DOI 10.1186/s13660-024-03107-3, Section 2. Its actual proof explicitly optimizes three coordinates at fixed sum and product, then establishes the one-large-coordinate pattern. That is the key scalar ingredient here. The present geometric conclusion follows by standard Gram/inverse-diagonal identities. Treat this as a strong routine-corollary/subsumption objection, not a cleared new discovery. No Lean endpoint or credit is claimed. Formalizing only the scalar helper would not cure that eligibility objection.

The 2024 article's main named inequality is different; the objection uses the actual interior proof argument, not its title or abstract. The older inequalities cited there (including 2011/2013 references) have not all been body-read. No worldwide-priority clearance is asserted. Further formalization would require a finite-dimensional constrained second-order minimum theorem, then spectral Gram bridges and square-root realization; none is silently assumed as a Lean result.
