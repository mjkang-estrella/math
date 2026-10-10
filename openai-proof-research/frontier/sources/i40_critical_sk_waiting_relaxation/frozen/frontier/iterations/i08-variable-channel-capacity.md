# Candidate: exact weighted capacity for inhomogeneous four-state reconstruction

Date: 2026-10-08. **Complete proposed deduction; independent proof and significance reviews pending. Not counted among the accepted ten.** This closes, at the author-proof level, the converse left open in the [parent screen](i07-parent-probability-screen.md). Assume the pinned corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## 1. Statement and source contract

Let T be an infinite deterministic rooted tree with at most B<∞ children at each vertex. Zero- and one-child vertices are allowed. Each edge e carries the symmetric four-state channel

\[
 P_e(j\mid i)=\lambda_e1_{i=j}+(1-\lambda_e)/4,
 \qquad 0<\lambda_e\le1.
\]

The uniform root is broadcast independently along edges conditional on parent spins. The tree and all parameters are known. Let a_n be the expected total-variation distance from uniform of the root posterior given the spins at depth n. Reconstruction means lim a_n>0.

Write r_e=λ_e², R_ρ=1 and R_v=∏_{e∈[ρ,v]}r_e. For a nonnegative conserved flow θ to infinity, set

\[
 V(\theta)=\sup_{\xi\in\partial T}
 \sum_{e=(v,w)\in\xi}(1-r_e^2)
           \left(\frac{\theta(e)}{R_w}\right)^2,
 \qquad
 C(T)=\sup\{|\theta|:V(\theta)\le1\}.
\]

The value +∞ is allowed for C(T). Flows used in the proof have finite mass.

**Theorem (candidate).** Reconstruction occurs if and only if C(T)>0. There is no uniform lower bound on λ_e and no uniform upper bound below one. Perfectly transmitting edges λ_e=1 are allowed.

The essential accepted input is the preserved posterior-law class and moment-saving inequality in **A Capacity Criterion for Four-State Potts Reconstruction on Trees**, `build/main.tex`, `prop:companion` / `eq:moment-saving` (itself citing the threshold companion's Proposition 3.2). The class contains revealing/uninformative experiments and is closed under channels with *any* t∈[0,1] and conditionally independent products. Its inequality is

\[
 m(\mu\star\nu)\le m(\mu)+m(\nu)
 -\frac1{1000}\big(E_\mu[A^2]m(\nu)+m(\mu)E_\nu[A^2]\big).
\]

Here the source coordinates are x=Lp, where L has columns (1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1), with a harmless ordering of labels. Define m=E|x|² and h=|E x₁x₂x₃|. Then 0≤m≤3, h≤m, and m/8≤E TV≤√m/2. Channel t sends (m,h) to (t²m,t³h). Source bytes and hashes are retained in the [32-file source manifest](../sources/i07_parent_screen/retrieval-manifest.json).

The source's main capacity theorem assumes one constant 0<λ<1. Its sufficiency argument uses a constant depending on 1/(1−λ). The new steps here are a uniform local third-moment bound and a flow-splitting estimate that replaces that geometric-kernel argument. Merely substituting edge products in the source's unweighted capacity is false, as the exact ray example below shows.

## 2. Uniform local posterior estimates

**Lemma.** For any two symmetric four-state posterior laws, without channel smoothing,

\[
 m(\mu\star\nu)\ge a+b-7(h_\mu b+a h_\nu),
 \qquad h(\mu\star\nu)\le h_\mu+h_\nu+460ab,
 \tag{L}
\]

where a=m(μ), b=m(ν). These lower/upper estimates require symmetry, not the preserved class. Subadditivity of m is used separately only for laws in that class.

**Proof.** Under independent marginal posterior vectors x,y, put s=x·y, Z=1+s and N_i=x_i+y_i+x_jy_k+x_ky_j for {i,j,k}={1,2,3}. The joint observation marginal is tilted by Z and the combined coordinate vector is N/Z. We have 0≤Z≤4 and |N_i|≤Z, including N=0 when Z=0. Set contributions at Z=0 to zero. Symmetry gives E x_i=0, E x_ix_j=(a/3)1_{i=j}, and similarly for y.

The exact algebraic expansion from the source gives

\[
 m(\mu\star\nu)=a+b-4(\tau_\mu b+a\tau_\nu)
 -6\tau_\mu\tau_\nu+E\frac{|N|^2s^2}{1+s},
\]

where τ is the signed third moment. The last term is nonnegative; |τ_μτ_ν|≤(h_μb+ah_ν)/2 proves the first inequality. Zero-normalizer terms extend continuously since |N|²/Z≤3Z.

For the third moment use

\[
 \tau(\mu\star\nu)=E\frac{N_1N_2N_3}{(1+s)^2},
 \qquad
 (1+s)^{-2}-(1-2s)=\frac{s^2(3+2s)}{(1+s)^2}.
\]

The absolute expectation of the remainder is at most E[36s²]=12ab: |N₁N₂N₃|≤Z³, Z≤4 and |3+2s|≤9. This is uniform even at Z=0, where the product contribution tends to zero.

In the polynomial N₁N₂N₃(1−2s), the only pure terms are x₁x₂x₃ and y₁y₂y₃. Mixed monomials of degree one in either vector have zero expectation. Each remaining monomial has absolute expectation at most ab: its degree in each vector is at least two, and |x_i|≤1 bounds that vector's monomial by |x|². The coefficient absolute sum of the entire polynomial is at most 4³(1+2·3)=448. Thus the polynomial part differs from τ_μ+τ_ν by at most 448ab. Adding the remainder and taking absolute values proves the second inequality with 460. ∎

## 3. Necessity

This repeats the preliminary weighted argument, including λ_e=1. Let m_v be the limiting subtree information, so m_ρ>0 under reconstruction. Write b_w=r_e m_w, S=Σb_w and D=max_{w≠w′}b_wb_w′(b_w+b_w′), with D=0 for fewer than two children. Combining the maximizing pair first using the accepted moment saving, then other branches by subadditivity, gives m_v≤S−cD, c=1/1000. Also S³≤Σb_w³+B³D.

Set K=c/B³, y_v=m_v+Km_v³ and a=2K/(1+9K)³. Since m_v≤3,

\[
 y_v\le\sum_w r_e y_w-K\sum_w r_e(1-r_e^2)m_w^3
 \le\sum_w\frac{r_e y_w}{\sqrt{1+a(1-r_e^2)y_w^2}}.
\]

The last step uses y_w≤(1+9K)m_w and (1+2t)^(−1/2)≥1−t. Choose d_e between zero and the displayed coefficient of y_w so that y_v=Σd_e y_w. Set ℓ_ρ=1, ℓ_w=ℓ_vd_e, θ(e)=ℓ_wy_w, and g_v=ℓ_v/R_v. Conservation is immediate, and

\[
 a(1-r_e^2)(\theta(e)/R_w)^2\le g_v^2-g_w^2.
\]

Telescoping on each ray proves V(√a θ)≤1. Its mass is √a y_ρ>0. All sums at vertices are finite. The preserved class is used at finite depths before passing to limits; membership of a limiting posterior law is not assumed. ∎

## 4. Flow profile and finite noisy observations

Suppose C(T)>0. Choose an admissible flow θ of finite mass A>0. Scale it by ε>0, writing Θ=εθ and M=εA. For v≠ρ let Θ(v) be its incoming flow, set Θ(ρ)=M, and define X_v=Θ(v)/R_v. Flow conservation reads

\[
 X_v=\sum_{w\in ch(v)}r_eX_w.
\]

Every positive-flow vertex extends to an infinite ray. Along such a ray,

\[
 X_w^2-X_v^2\le(1-r_e^2)X_w^2,
\]

since r_eX_w≤X_v. Consequently

\[
 \sup_{v:\Theta(v)>0}X_v^2\le M^2+\varepsilon^2
 =\varepsilon^2Q,\qquad Q=A^2+1. \tag{P}
\]

Choose ε√Q≤1. At each depth-n terminal v independently pass its spin through a channel with parameter √(X_v/3), using parameter zero on zero-flow terminals. Its information and third moment are exactly

\[
 \widehat m_v=X_v,\qquad
 \widehat h_v=(X_v/3)^{3/2}. \tag{T}
\]

All experiments belong to the preserved class. Subadditivity inductively gives m̂_v≤X_v. Zero-flow branches have uninformative observations throughout and can be omitted.

At each positive-flow vertex define

\[
 t_{vw}=\Theta(w)/\Theta(v),\quad \sum_wt_{vw}=1,
 \quad \beta_v=1-\sum_wt_{vw}^2,
 \quad U_v=\widehat h_v/X_v.
\]

Use (L) to combine branches one at a time. For branch w let b_w=r_e m̂_w≤r_eX_w=t_{vw}X_v and h′_w=λ_e³ĥ_w. The third moment of a partial product is at most Σh′_w+460Σ_{i<j}b_ib_j. The quadratic-information deficit at each addition is at most 7(h_partial b_new+m_partial h_new). Summing these inequalities, bounding the cubic remainder by 460X_vΣ_{i<j}b_ib_j, gives, with the universal choice C₀=2000,

\[
 U_v\le\sum_wt_{vw}\lambda_e U_w+C_0 X_v\beta_v, \tag{H}
\]
\[
 0\le D_v:=\sum_wr_e\widehat m_w-\widehat m_v,
 \qquad
 \frac{D_v}{X_v}\le C_0\left[
 X_v\sum_wt_{vw}(1-t_{vw})\lambda_eU_w+X_v^2\beta_v\right]. \tag{D}
\]

For clarity, the pair terms in the deficit sum are exactly bounded by 7Σ_w h′_w(S−b_w), S=Σb_w, and S−b_w≤X_v(1−t_vw). The cubic remainder is at most (7·460/2)X_v³β_v. Both constants are below 2000. With one child β_v=0 and D_v=0, as required; no artificial loss is inserted on noiseless chains.

## 5. The splitting-energy bound

Sample a ray according to the flow Θ/M, and write V_i for its depth-i vertex, X_i=X_(V_i), t_(i+1)=t_(V_i,V_(i+1)), α_i=1−t_(i+1), and λ_(i+1) for that edge. Zero-flow vertices are never visited. Let E denote this ray expectation. Then E[α_i|V_i]=β_(V_i).

At a vertex v, direct conditional expectation gives

\[
 X_v^2-E[X_{i+1}^2\mid V_i=v]
 +E[(1-r_e^2)X_{i+1}^2\mid V_i=v]
 =X_v^2\left(1-\sum_wt_{vw}^3\right)
 \ge X_v^2\beta_v.
\]

Telescoping, dropping the nonpositive terminal term, and using the pathwise capacity bound proves

\[
 E\sum_{i=0}^{n-1}X_i^2\alpha_i
 =E\sum_{i=0}^{n-1}X_i^2\beta_{V_i}
 \le M^2+\varepsilon^2=\varepsilon^2Q. \tag{E}
\]

For i<j define K_ij=∏_{k=i+1}^j√t_k. On every ray, the telescoping inequality 1−t≤2(1−√t) gives

\[
 \sum_{j>i}^{n-1}\alpha_jK_{ij}\le2,
 \qquad \sum_{i<j}\alpha_iK_{ij}\le2,
 \qquad \sum_{i<n}\alpha_iK_{in}\le2. \tag{K}
\]

In the first inequality compare K_ij−K_i,j+1=K_ij(1−√t_(j+1)). In the second and third, use α_iK_ij≤2(K_i+1,j−K_ij), with K_jj=1. These bounds require no decay rate in depth.

Since X_j=X_i∏_{k=i+1}^j(t_k/λ_k²),

\[
 X_iX_j\prod_{k=i+1}^j\lambda_k
 =X_i^{3/2}X_j^{1/2}K_{ij}
 \le\left(\tfrac34X_i^2+\tfrac14X_j^2\right)K_{ij}.
\]

Using (K) on rows and columns therefore gives, pathwise,

\[
 \sum_{i<j<n}\alpha_i\alpha_j X_iX_j
                  \prod_{k=i+1}^j\lambda_k
 \le2\sum_{i<n}\alpha_iX_i^2. \tag{B}
\]

This replaces the fixed-channel source's geometric convolution estimate.

## 6. Closing sufficiency

Iterate (H) down to level n, then insert in (D) and take ray expectations. At each internal descendant j, β_(V_j) may be replaced by α_j inside expectation because every earlier factor is measurable before the next branch choice. This produces

\[
 E\sum_{i<n}\frac{D_{V_i}}{X_i}
 \le C_0\varepsilon^2Q
 +C_0^2E\sum_{i<j<n}\alpha_i\alpha_jX_iX_j
                         \prod_{k=i+1}^j\lambda_k
 +C_0E\sum_{i<n}X_i\alpha_i
                         \left(\prod_{k=i+1}^n\lambda_k\right)U_{V_n}.
\]

The middle term is at most 2C₀²ε²Q by (B) and (E). For the terminal term, (T) gives U_(V_n)=√X_n/(3√3). Hence

\[
 X_i\left(\prod_{k=i+1}^n\lambda_k\right)U_{V_n}
 =\frac{X_i^{3/2}}{3\sqrt3}K_{in}.
\]

By (P) and (K), its sum with α_i is at most 2ε^(3/2)Q^(3/4)/(3√3), pathwise. We conclude that

\[
 E\sum_{i<n}D_{V_i}/X_i
 \le (C_0+2C_0^2)\varepsilon^2Q
       +\frac{2C_0}{3\sqrt3}\varepsilon^{3/2}Q^{3/4}. \tag{F}
\]

Choose ε>0 small enough that ε√Q≤1 and the right side of (F) is at most 1/2. This choice is independent of n and all edge parameters.

Finite-tree telescoping of the information deficits, using R_w=R_vr_e and the terminal identity m̂_v=X_v, gives

\[
 \widehat m_\rho
 =\sum_{|v|=n}R_vX_v-\sum_{|v|<n}R_vD_v
 =M-M E\sum_{i<n}D_{V_i}/X_i\ge M/2.
\]

The flow sums on every level equal M; finite dead-end branches carry no flow. The original level observation is more informative than the degraded one. Thus a_n≥M/16 at every depth, proving reconstruction. ∎

## 7. Scope, checks and novelty limits

For constant λ∈(0,1), the factor 1−λ⁴ is constant, so positivity agrees with the source's L³ capacity. For a ray λ_j=1−1/(j+1)², the product P_n=(n+2)/(2(n+1)) tends to 1/2, reconstruction advantage tends to 3/8, and the weighted unit-flow potential telescopes to 15. The unweighted substituted capacity is zero. A perfectly transmitting infinite ray has zero potential for every finite flow and reconstructs perfectly. These examples are consistent with the candidate theorem.

The theorem concerns ferromagnetic four-state symmetric channels only. It does not assert three-state or antiferromagnetic analogues, unbounded-degree necessity, random unobserved trees, or a uniform positive reconstruction advantage over every tree.

The exact finite checks in `frontier/experiments/i08_variable_capacity/check.py` target the new polynomial and splitting-energy identities. They do not replace the asymptotic argument or independent review. The prior parent screen supplies the source retrieval records; no corpus truth audit is performed.

A bounded preliminary search found no direct matching variable-edge theorem, but that is not a priority claim. Independent reviewers must assess whether the proposed bridge is correct and whether its contribution is substantial beyond standard nonlinear-capacity arguments, including Pemantle–Peres and stronger corpus companion statements. The candidate remains outside the accepted 2/10 count until both reviews and parent integration complete.
