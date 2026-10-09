# Capacity strengthening: locally finite trees and degree-independent bounds

Date: 2026-10-08. **Proposed strengthening of the same capacity finding, not a separate finding.** The [bounded-degree candidate](i08-variable-channel-capacity.md) has passed an [independent proof audit](../reviews/i08-variable-capacity-r2.md). This extension has not yet had independent review. The original audited file remains unchanged while its significance review runs.

Assume the pinned corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The sole additional source input is the same preserved-class binary moment saving, not a stronger unquoted theorem. Its exact statement is `prop:companion` / `eq:moment-saving` of *A Capacity Criterion for Four-State Potts Reconstruction on Trees*, `build/main.tex`; source provenance is in the existing [audit input manifest](../sources/i08_variable_capacity_r2/input-manifest.json).

## Statement

In the notation and observation model of the bounded-degree candidate, replace the uniform bound on the number of children by **local finiteness**: each vertex has finitely many children, with no common bound. Keep arbitrary known edge parameters `0<lambda_e<=1`, the uniform four-state root, conditional independence, and the weighted capacity

\[
 C=\sup\left\{|\theta|:\sup_\xi\sum_{e=(v,w)\in\xi}
       (1-\lambda_e^4)(\theta(e)/R_w)^2\le1\right\},
 \qquad R_w=\prod_{e\in[\rho,w]}\lambda_e^2.
\]

Only nonnegative conserved flows of finite mass are used. The supremum may be infinite. Put `m_infty=lim_n E|Lp_root^(n)|^2`, the limiting quadratic posterior information, and

\[
 K=1/3000,\qquad \kappa=\frac{2K}{(1+9K)^3}.
\]

**Proposed theorem.** On every such locally finite tree, reconstruction holds if and only if `C>0`. More quantitatively,

\[
 \frac{1}{20000}\frac{C}{\sqrt{1+C^2}}
 \ \le m_\infty\ \le\min\{3,C/\sqrt\kappa\}. \tag{1}
\]

The fraction on the left is interpreted as one when `C=+infty`, and as zero when `C=0`. The constants do not depend on any vertex degree, edge parameter, depth, or tree. As before, `m/8<=E TV<=sqrt(m)/2` relates this information to reconstruction advantage.

## 1. A binary change of variable removes the degree loss

Let `mu,nu` be two laws in the accepted preserved class. Write `a=m(mu)`, `b=m(nu)`, `d=m(mu star nu)` and `c=1/1000`. Jensen and the source saving give

\[
 0\le d\le a+b-cab(a+b)\le a+b.
\]

For the increasing function `g(t)=t+Kt^3` on nonnegative arguments, use the first bound for the linear term and the last bound for the cubic term:

\[
\begin{aligned}
 g(d)&\le a+b-cab(a+b)+K(a+b)^3\\
 &=g(a)+g(b)+(3K-c)ab(a+b)\\
 &=g(a)+g(b). \tag{2}
\end{aligned}
\]

This does not require that `a+b<=3`. Only `d,a,b` themselves are moments of posterior laws. Every partial product stays in the preserved class. Inductively applying (2), rather than estimating the largest pair among all children, gives

\[
 g\big(m(\mu_1\star\cdots\star\mu_d)\big)
       \le\sum_{j=1}^d g(m(\mu_j)) \tag{3}
\]

for every finite `d`, with the same `K`. The empty product has information zero. This is the step that eliminates the former factor `B^3`.

## 2. Necessity and the upper bound in (1)

At each vertex let `m_v` be the limit of information from its descendant levels. Data processing makes the finite-depth quantities decreasing and bounded in `[0,3]`. Apply (3) to finite-depth branch experiments and pass to the limit through the finitely many children. With `r_e=lambda_e^2` and `y_v=g(m_v)`, this gives

\[
\begin{aligned}
 y_v&\le\sum_w g(r_e m_w)\\
 &=\sum_w r_e y_w-K\sum_w r_e(1-r_e^2)m_w^3\\
 &\le\sum_w r_e y_w\left[1-\frac\kappa2(1-r_e^2)y_w^2\right]\\
 &\le\sum_w\frac{r_e y_w}{\sqrt{1+\kappa(1-r_e^2)y_w^2}}. \tag{4}
\end{aligned}
\]

Here `y_w<=(1+9K)m_w` and `(1+2t)^(-1/2)>=1-t` for `t>=0`. In particular no limiting posterior-law membership is needed.

For each edge choose `d_e` between zero and the coefficient of `y_w` in the last sum so that `y_v=sum_w d_e y_w`. If that sum is positive, multiply all its coefficients by the ratio of `y_v` to the sum; if it is zero take all coefficients zero. Set `ell_root=1`, `ell_w=ell_v d_e`, `theta(e)=ell_w y_w` and `h_v=ell_v/R_v`. The flow is conserved, including at dead ends, and its mass is `y_root`. The coefficient bound gives

\[
 \kappa(1-r_e^2)(\theta(e)/R_w)^2\le h_v^2-h_w^2.
\]

Every ray telescope is at most `h_root^2=1`. Thus `sqrt(kappa) theta` is admissible, and

\[
 C\ge\sqrt\kappa\,g(m_\infty)\ge\sqrt\kappa\,m_\infty. \tag{5}
\]

This proves necessity and the upper bound. No maximum degree was introduced.

## 3. Sufficiency and the lower bound in (1)

Every finite-depth truncation of a locally finite rooted tree is finite: prove this by induction over levels, taking a finite union of finite child sets. The sufficiency proof in Sections 4–6 of the bounded-degree candidate therefore remains a finite computation at each observation depth. Its constants and the final choice of noise are independent of the number of vertices and children.

For clarity, the places where a hidden degree bound could occur are checked here. The local product estimates use the pair sum `P_2=sum_(i<j) b_i b_j`, the total `S=sum_i b_i<=X_v`, and `P_2<=X_v^2(1-sum_i t_i^2)/2`. These identities hold for every finite number of children. The accumulated third-order remainder is bounded by `7*460*X_v P_2`, so the same universal `C_0=2000` controls (H) and (D). The ray-energy identity uses the exact finite sums `sum t_i=1` and `sum t_i^3`; its bound contains no cardinality. The row, column and terminal kernel estimates are pathwise telescopes and do not involve vertex degrees. All level-flow sums are finite and equal to the root mass by conservation. A positive-flow vertex has a positive-flow child, and hence an infinite continuation; this supplies the pathwise profile bound. The conditioning argument in paragraph 7 of the independent audit remains unchanged.

Take any admissible flow of finite mass `A>0`, set `Q=1+A^2`, and use

\[
 \varepsilon=10^{-4}/\sqrt Q.
\]

The right side of the loss bound (F) is

\[
 (2000+2\cdot2000^2)10^{-8}
       +\frac{4000}{3\sqrt3}10^{-6}
 <0.08002+1/750<1/2. \tag{6}
\]

Also `epsilon sqrt(Q)=10^-4<=1`, so all terminal channels are valid. The degraded finite-depth root information is at least `epsilon A/2`, uniformly in depth. The original observation is more informative, so

\[
 m_\infty\ge\frac{1}{20000}\frac{A}{\sqrt{1+A^2}}. \tag{7}
\]

Take admissible masses tending to `C` when it is finite. When `C` is infinite, take masses tending to infinity. No capacity optimizer is assumed. Equation (7) proves the lower bound of (1) and sufficiency.

## 4. Zero edges can be removed, but local finiteness matters

One may also allow `lambda_e=0` by defining capacity on the connected component of the root after deleting all zero edges, with the displayed positive-edge formula. Every deleted descendant component starts with a fresh uniform spin independent of its parent, and all its later spins depend only on that spin and independent edge randomness. Its observations are therefore independent of both the root and observations in the root component. Removing them leaves the root posterior unchanged. This is a direct corollary, not an additional finding. If the root component is finite, its sufficiently distant level is empty, its information is zero, and it has no positive conserved flow.

The local-finiteness assumption cannot simply be deleted. Let the root have, for each integer `k>=1`, one disjoint child chain of total length `k`, and take every edge perfectly transmitting. There is no infinite ray. Each chain ends in a leaf; conservation forces its flow to be zero backwards all the way to the root. Even with countably additive conservation at the root, every flow has zero mass and capacity is zero. Nevertheless each level `n` contains vertices from all chains of length at least `n`, and any one such spin equals the root. Thus every level has quadratic information `3` and TV advantage `3/4`. This counterexample explains why finite-depth finiteness is a substantive hypothesis, not just a convenience of notation.

## Review and counting boundary

The argument (2) is a new short strengthening within the same proposed capacity result. It does not replace the difficult uniform local-moment and flow-splitting sufficiency argument, and it must not be counted separately. Before promotion, a fresh independent review must check the binary iteration, every claimed degree-free sufficiency step, the quantitative constants, and the zero-edge and nonlocally-finite boundary cases. The ongoing significance audit is still reviewing the original bounded-degree scope; its verdict will not automatically certify this extension. No claim of worldwide priority is made.
