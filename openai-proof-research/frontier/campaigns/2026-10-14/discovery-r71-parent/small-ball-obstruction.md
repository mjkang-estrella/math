# Biased homogeneous exact atoms do not give the same small-ball bound

Parent author-side deduction, 2026-10-18. No independent review, nomination, or count change. This does not settle the symmetric higher-corank question. It identifies a failed possible use of the supporting exact-section lemma from structural r68.

Fix p∈(0,1) with p≠1/2, let μ=2p−1, and let s∈{−1,1} be the more likely sign. Write v=max(p,1−p) and u=1−v. Let k≥1 be fixed. All signs below are independent and have probability p of being +1.

For each N≥1 take k disjoint blocks, each containing one distinguished sign ε_i and N auxiliary signs η_ij. Define

    c_N = sqrt(1+1/(μ²N)),
    (A_N x)_i = [x_i − s/(μN) sum_{j=1}^N x_ij]/c_N.

The rows have disjoint supports and squared norm1, so A_N A_Nᵀ=I_k. The equation A_N x=0 is homogeneous, and A_N has rank k. Every column is nonzero. There is no affine term in the matrix equation.

Put Z_i=−s/(μN)∑_jη_ij+s. These independent random variables have mean0 and variance (1−μ²)/(μ²N). Therefore

    A_N ε = (ε_distinguished − s·1 + Z)/c_N,
    E||Z||₂² = k(1−μ²)/(μ²N) = V_N.

The distinguished signs and Z are independent. Conditional on all distinguished signs equaling s, the output is Z/c_N. Markov's inequality gives, for every r>0,

    P(||A_N ε||₂ ≤ r)
      ≥ v^k [1 − V_N/(c_N²r²)].

The lower bound is useful for large N; its possible negativity at small N causes no issue. In particular its limit inferior is at least v^k.

For any fixed 0<r<2, the probability also converges to v^k. Indeed, on every other distinguished-sign configuration the vector ε_distinguished−s·1 has norm at least2. For all sufficiently large N, 2−r c_N>0. If its sum with Z has norm at most r c_N, the triangle inequality forces ||Z||₂≥2−r c_N. Hence

    P(||A_N ε||₂ ≤ r) ≤ v^k + V_N/(2−r c_N)² → v^k.

Finally,

    v^k − [p^(k+1)+(1−p)^(k+1)]
      = u(v^k−u^k) > 0.

Thus for every fixed radius r∈(0,2), the supremum over ambient dimensions and orthonormal rank-k row matrices of the radius-r small-ball probability is at least v^k, strictly larger than the exact homogeneous-section bound f(k+1)=p^(k+1)+(1−p)^(k+1). In particular there cannot be an error function e(r)→0 as r↓0 with

    P(||Aε||₂ ≤ r) ≤ f(k+1)+e(r)

uniformly in the number of columns and all such A. For any proposed sufficiently small e(r), fix r first and then take N large in the explicit construction. The order of quantifiers is essential. At each fixed finite matrix the exact zero atom still satisfies the r68 lemma; there is no contradiction.

For p=1/10 and k=2 the limiting small-ball mass is81/100, while f(3)=73/100. The construction works for every biased p and every k≥1. It makes no assertion about the fair law p=1/2, where μ=0 and this construction is undefined. Replacing the raw signs by centered signs also changes the problem and removes this particular deterministic-shift mechanism.

This blocks only a dimension-free replacement of the existing affine small-ball cost by the sharper homogeneous exact-atom cost. It does not rule out additional restrictions, adaptive exposure estimates, treatment of compressible and incompressible kernel spaces separately, or the full random-matrix conjecture. No literature priority is claimed. The argument uses elementary independence, variance, Markov and triangle inequalities; no new external source theorem is imported. Parent derivation is author collaboration, not independent review of r68.
