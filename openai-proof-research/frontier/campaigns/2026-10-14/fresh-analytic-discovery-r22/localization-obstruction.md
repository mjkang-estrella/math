# A smooth localized obstruction to broad perceptron universality

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is a prefreeze obstruction and technical deduction. No substantial result is nominated, no independent PASS is asserted, and no scope was frozen. It does not challenge any stipulated theorem. The Gaussian and small Gaussian variance-mixture laws of the pinned source are not the law constructed below.

## 1. Exact model and explicit law

For an M by N matrix A, put H_A(y)=(1/2) sum_mu (-1-A_mu y)_+^2 on the unit sphere S^{N-1}, with normalized surface measure sigma. Write Z_A(beta)=integral exp(-beta H_A(y)) d sigma(y). The sphere convention is exactly equivalent to the source's radius-sqrt(N) sphere after y=x/sqrt(N).

Let W have the even smooth density c exp(-1/(1-w^2)) on |w|<1, and zero otherwise, with c the positive normalizing constant. Put v=E W^2. Independently, let U equal -1/2 with probability 4/5 and 2 with probability 1/5. Define

    X=(U+W/8)/sqrt(1+v/64).

Then E X=0 and E X^2=1. Its density is C-infinity, compactly supported, and bounded. It has all moments and is subgaussian. Its support is contained in [-5/8,17/8], since the normalization is at least one. Set

    a=5/8, B=17/8, delta=1-a=3/8, u=delta/2=3/16,
    s=u/(2B)=3/68.

For every deterministic matrix with entries in this support and every M,N, y=e_1 is strictly feasible: 1+A_mu e_1>=delta for every row. Thus the iid X model has SAT probability exactly one at every size and every density. In contrast, the pinned Gaussian model has finite threshold alpha_c. Even the fair-sign law has y=e_1 feasible for every matrix at margin -1, although without a strict margin. This already refutes unrestricted first-two-moment universality of the feasibility threshold.

## 2. Exponentially large strict-feasibility volume

The obstruction is not confined to isolated points. For N>=2 write d=N-1 and parametrize the positive first-coordinate hemisphere by

    y(z)=(sqrt(1-|z|^2),z),  |z|<1.

Let K be the intersection of the following centered symmetric slabs in R^d:

    |z_j|<=s/sqrt(d), all j;
    |A_{mu,rest} z|<=u, all mu.

Every z in K has |z|<=s<1. Also A_{mu,1} sqrt(1-|z|^2)>=-a, so 1+A_mu y(z)>=1-a-u=u. Hence this entire patch is strictly feasible.

Let Z be a centered Gaussian vector in R^d with covariance (s^2/d)I. Its coordinate slab probabilities equal p_0=P(|G|<=1). Each row projection has variance at most B^2 s^2, so its row slab probability is at least p_1=P(|G|<=2). Gaussian correlation for symmetric convex sets, iterated over these slabs, gives

    P(Z in K)>=p_0^d p_1^M.                                      (1)

This use is the classical strip product inequality (Sidak); full Gaussian correlation also gives it immediately. Degenerate row projections cause no problem; their slab probability is one, and singular covariance is obtained by continuity. Royen's proof and its singular-covariance remark are read and credited below.

The Gaussian density is at most (d/(2 pi s^2))^(d/2). The sphere-chart surface Jacobian is (1-|z|^2)^(-1/2)>=1. Therefore

    sigma{y: min_mu(1+A_mu y)>=u}
      >= c_d (s p_0)^d p_1^M,                                  (2)
    c_d=(2 pi/d)^(d/2)/area(S^d)
       =(2 pi/d)^(d/2) Gamma((d+1)/2)/(2 pi^((d+1)/2)).

No randomness of A is used in (1) or (2). Stirling gives log c_d=-d/2+O(log(d+1)). For M=floor(alpha N), define the finite positive constant

    C_alpha=1/2-log(s p_0)-alpha log p_1.

The deterministic consequence is

    liminf_N inf_A N^(-1) log Z_A(beta)>=-C_alpha                (3)

for every beta>0; indeed the finite-N bound (2) holds uniformly in beta. Here inf_A runs over matrices with entries in [-a,B]. In particular this is a fixed-temperature pressure obstruction, not merely an existence statement at zero temperature.

## 3. A refined replacement bound on spins with small coordinates

This lemma is a technical refinement of the source's ordinary Lindeberg estimate, not a new invariance principle. Let lambda be a deterministic nonzero finite measure on unit spins with max_i |y_i|<=b, 0<b<=1. Let w be C^3 with finite K_j=||w^(j)||_infinity for j=1,2,3. Its values need not be bounded. Let

    L(A)=log integral exp(sum_mu w(A_mu y)) d lambda(y).

Compare iid X and iid standard Gaussian entries. There is a finite constant C_w, depending on the two entry laws and K_1,K_2,K_3 but not on M,N,b or lambda, such that

    |E L(X)-E L(G)| <= C_w M b.                                (4)

Proof. Hold all entries but one A_{mu i}=t fixed, write L(t), and let m_t=<|y_i|^3>_t. Differentiating three times gives the source's exact formula

    L'''(t)=<w''' y_i^3>
             +3 Cov(w'' y_i^2,w' y_i)
             +<(w' y_i-<w' y_i>)^3>.

Holder bounds the covariance by 2 K_1 K_2 m_t and the absolute third cumulant by 6 K_1^3 m_t. Thus |L'''(t)|<=D_w m_t, with D_w=K_3+6K_1K_2+6K_1^3. Changing t from zero changes the Hamiltonian by at most K_1 |t|, so

    exp(-2K_1|t|)m_0 <= m_t <= exp(2K_1|t|)m_0.

Taylor expansion at zero, matching means and variances, bounds the difference between the X and Gaussian expectations in this coordinate by R_w m_0, where

    R_w=(D_w/6)[E|X|^3 exp(2K_1|X|)+E|G|^3 exp(2K_1|G|)].

Both terms are finite. Interpolate all matrix entries simultaneously through their common mixture law nu_t=(1-t) Law(G)+t Law(X), 0<=t<=1. Differentiating the expectation with respect to this mixture parameter is the sum of the one-coordinate replacements with all other entries iid nu_t. This differentiation is legitimate by finite expansion over the MN Bernoulli selectors and integrability of L, which follows from the bounded first derivative and finite entry moments.

Put kappa_w=min(E exp(-2K_1|X|), E exp(-2K_1|G|))>0. Conditional on the other entries, E_{nu_t} m_{A_{mu i}}>=kappa_w m_0. Consequently the absolute derivative of E_{nu_t} L is at most

    (R_w/kappa_w) sum_{mu,i} E_{nu_t}<|y_i|^3>
       <= (R_w/kappa_w) M b,

because sum_i |y_i|^3<=b sum_i y_i^2=b pointwise. Integrating proves (4) with C_w=R_w/kappa_w. Unlike a telescoping estimate with separately maximized derivatives, this simultaneous mixture interpolation retains the sum of the cubic Gibbs moments. There is no unjustified interchange of the Gibbs law at unrelated replacement matrices.

## 4. Concentration for the bounded entry law

For the same w and domain lambda, iid entries X in [-B,B] satisfy

    Var L(A) <= (1/2) K^2 exp(2K) M,  K=2B K_1.               (5)

Indeed replace one entry by an independent copy. Along the interpolating entry segment, the squared change in L is at most K^2 integral <y_i^2>_t dt, by Jensen and the fundamental theorem of calculus. Comparing the interpolated Gibbs density to its initial density gives <y_i^2>_t<=exp(2K)<y_i^2>_A. Efron--Stein and sum_i y_i^2=1 prove (5). This bound applies to any deterministic restricted spherical domain of positive measure and does not require a log-Sobolev inequality for the disconnected smooth mixture density. For M=O(N), L/N therefore differs from its mean by o_P(1).

## 5. Actual fixed-coordinate localization at low temperature

Fix alpha with positive Gaussian ground-energy limit e(alpha)>0. The pinned source proves this for every alpha>alpha_c, after identifying alpha_c=alpha_J. Only the existence of one such finite density is needed for the basic obstruction; the source's elementary net argument already gives it. Let P_G(alpha,beta) be its limiting Gaussian pressure for u_beta(z)=-(beta/2)(-1-z)_+^2. Since Z<=exp(-beta min H),

    P_G(alpha,beta)<=-beta e(alpha).                           (6)

For every beta with beta e(alpha)>C_alpha, there exist constants b>0 and c>0, independent of N, such that for iid X matrices

    P_A( <1{max_i |y_i|<=b}>_{A,beta} <= exp(-cN) ) -> 1.      (7)

The outer probability is over the disorder, and the inner brackets are the actual unrestricted Gibbs law for the original unsmoothed quadratic hinge. Thus its mass lies on spins with at least one coordinate of fixed positive size. The index need not be deterministic and no limit of that index or exact localization profile is asserted.

Proof. Set g=beta e(alpha)-C_alpha>0. Choose a smooth upper tangent cap w of u_beta, with bounded first three derivatives, whose expected Gaussian pressure error is at most g/8 uniformly in N. The source's row-insertion cap proof supplies this: its Gaussian residual-tail bound vanishes as the tangent point tends to infinity; mollification adds an arbitrarily small constant. In particular w>=u_beta and

    limsup_N N^(-1) E log Z_G(w) <= P_G(alpha,beta)+g/8.

Select b in (0,1/2) so that alpha C_w b<g/8. The set D_b={max_i |y_i|<=b} has positive spherical measure for all sufficiently large N. Use normalized sphere measure restricted to D_b as lambda in (4). Restriction decreases the Gaussian partition function, so

    limsup_N N^(-1) E log Z_X,D_b(w)
       <= P_G(alpha,beta)+g/4
       <= -C_alpha-3g/4.

By (5), with probability tending to one,

    N^(-1) log Z_X,D_b(u_beta)
       <= N^(-1) log Z_X,D_b(w) <= -C_alpha-g/2.

The deterministic strict-feasible volume bound gives N^(-1)log Z_X(u_beta)>=-C_alpha-o(1). Hence (7) holds, for example with c=g/4. The order of choices is alpha, beta, cap and smoothing, then b, then N. No estimate uniform as beta tends to infinity or alpha approaches alpha_c is claimed or needed.

## 6. What this does and does not pay

The source already identifies the genuine difficulty: small-coordinate replacement says nothing about localized slices. Its upper proof conditions on variance-mixture marks and pays the localized entropy loss against a row gain on the common susceptibility scale t/chi_q(0), with a small parameter chosen independently of beta. The law above has a one-sided support geometry absent from those mixtures; moment matching cannot substitute for that comparison.

The threshold obstruction alone is immediate. The exponential-volume and fixed-coordinate localization refinements are combinations of a classical Gaussian correlation bound, a standard smooth replacement argument retaining cubic Gibbs moments, Efron--Stein, and the stipulated Gaussian positive-energy premise. They are useful complete technical deductions, not evidence of an accepted substantial result. There is no claim of worldwide novelty, no assertion that arbitrary symmetric smooth disorder behaves this way, and no nomination of a nearby small perturbation or parameter variant. The asymmetry of the smooth law is explicit; the separate symmetric Rademacher example only asserts feasibility, not (2) or (7).
