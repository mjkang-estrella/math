# Frozen target PCW: posterior critical wave process

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT; third-party rights retained privately.

For every integer d>=3 set b=d-1, theta=b^(-1/2), beta=atanh(theta). Let T_d=(V,E) be the infinite d-regular tree. Let sigma in {-1,1}^V have the free zero-field Ising law: on each finite connected D,

    P(sigma_D=eta)=2^(-|D|) product_{uv in E(D)}(1+theta eta_u eta_v).

Let (B_v) be independent standard real Brownian motions, independent of sigma. For t>=0 put X_v(t)=t sigma_v+B_v(t), F_t=sigma(X_v(s):v in V,0<=s<=t) with the usual augmentation, m_v(t)=E[sigma_v|F_t], and h_v(t)=atanh(m_v(t)). Use the continuous posterior versions supplied by the pinned family236; m_v(0)=h_v(0)=0.

The target is: for every finite nonempty ordered vertex tuple F=(v_1,...,v_k) (distinct vertices suffice) and every finite T>0, as epsilon decreases to0,

    (epsilon^(-1/4) m_{v_i}(epsilon t))_{i=1}^k
       => (G_{v_i}(t))_{i=1}^k  in C([0,T],R^k),

with the uniform topology. The same convergence is claimed with h in place of m. The centered Gaussian limit has continuous paths, starts at0, and has covariance, for every u,v in V and s,t>=0,

    E[G_u(s)G_v(t)] = A_d phi_d(dist(u,v)) sqrt(min(s,t)),
    A_d = d / sqrt((d-1)(d-2)),
    phi_d(n) = (1+(d-2)n/d) (d-1)^(-n/2).

Thus its time parameter is sqrt(t), not t^(1/2) times one fixed spatial Gaussian sample. Existence/consistency of this Gaussian process and identification of the covariance are part of the target. Limits concern the actual planted infinite-volume posterior, not an independently resampled one-time fixed point.

This full path claim at every degree, all finite spatial tuples, and time0 is frozen. A one-time CLT, an explicit second moment, finite-dimensional time convergence, a subsequence, a conditional bracket implication, or a strict-temperature result is supporting work only. Finitary coding, quantitative IID coding rates, capacity criteria, mesoscopic spatial distances, and finite-graph limits are not in scope.

The new deductions may use the exact pinned source hypotheses/contracts recorded separately. Source theorem truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No guarantee of a full proof or counterexample; unresolved work must retain this original scope.
