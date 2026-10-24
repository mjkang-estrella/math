# r233 author proof: arbitrarily small distortion at each regular point

This is a research author-proof submission at the exact unchanged scope in FROZEN-STATEMENT.md. It assigns no correctness, contribution, acceptance, or count. It relies on Source357 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including every operative proof, as stipulated true. All mathematical exposition below is new local working prose; protected source and primary texts remain separately private.

## 1. Statement and the additional operation

For every n>=2, K real, noncollapsed RCD(K,n) space (X,d,H_d^n), every point p with all pointed tangents Euclidean, every eta>0 and every R>0, there is 0<r<R and a pointed (1+eta)-bi-Lipschitz homeomorphism from the ambient ball B_r(p) onto an open subset of R^n. The metric, measure, and other conventions are exactly those in the frozen statement. In particular, no lower injectivity radius, Morrey bound, weighted reference measure, or uniform radius is added.

The supplied source produces a fixed dimensional distortion. Its analytic iteration has leading metric I+2 sum S_i, which is only compared to H_k by a fixed factor C_*. Making its error small does not remove that fixed comparison factor. The additional operation proved here is a positive, localized heat-source interpolation with

  |(I+2 sum_{i<k} S_i(x)-H_k(x))[xi]|
      <= (b_L+C h+o_{L,h}(1)) H_k(x)[xi],                 (1.1)

where b_L tends to zero as L tends to infinity, h is a fixed fine-net spacing, and the last term tends to zero along the source rescalings after L,h have been fixed. This is an accumulated estimate, uniform in x,k,xi, and it allows unbounded, noncommuting H_i. Localizing the heat source is necessary to retain the source's same-scale directional pinching. The original value-space iteration is then paid in full; its compatibility with the new coefficients is checked below.

## 2. Exact paid inputs and notation

Work on the rescaling sequence from co:flat-setup. Distances and measures in this proof are d/s_nu and s_nu^{-n}H_d^n until Section 9. Write r_i=2^{-i}, P_x=u(x), G=Gamma(u,u), and let M be the positive matrix-valued Bochner measure. The harmonic map u is defined on expanding domains and is an open homeomorphism on every fixed interior ball for sufficiently late rescalings. All regions below are fixed interior regions, with x,y in B_1(p), and sources in the expanding support of chi. Increase the original working domain before taking the late rescaling.

The source gives R_i(y)=average_{B_{r_i}(y)} G, Q_i(x)=P_{r_i^2}(chi G)(x)+lambda r_i^2 I, H_i=Q_i^{-1}, and:

(a) R_i,Q_i are positive definite; H_i<=H_{i+1}<=(1+o(1))H_i, H_0=I+o(1). For each fixed a>0, ||H_i||<=C_a 2^{2ai}. We fix a=1/16. All fixed nearby-center/scale comparisons tend to equality. Normalized harmonic distances have additive o(1)r_i errors at any fixed enlargement, and the central H_i-ellipsoid of radius a_c r_i about P_x lies in u(B_{r_i}(x)), with a_c>0 fixed. For y in B_{r_i}(x), H_i(y)<=C_cmp H_i(x), with a fixed C_cmp.

(b) Put N_j(x)=r_j^{2-n}M(B_{r_j}(x)), gamma=1/2, and
  F_i(x)=2^{-gamma i}I+sum_{j<=i}2^{-gamma(i-j)}N_j(x).
For a_i=H_i(x)xi,
  sum_{i<k} F_i(x)[a_i] <= C H_k(x)[xi].                 (2.1)
This is co:weighted-total, obtained by the source's noncommuting inverse-increment and convolution argument, not by an operator-norm telescoping assertion.

(c) For any at most J centers y at each scale with d(x,y)<=r_i, set
  e_{i,y}=R_i(y)^{-1}xi-H_i(x)xi.
The source co:normalization-error proves
  sum_{i<k,y} |e_{i,y}|_{Q_i(x)}^2 <= C_J H_k(x)[xi].    (2.2)
It applies when the centers vary arbitrarily with i and x.

(d) For every fixed L>1, the positive matrices
  D_{i,y}=R_i(y)^{-1}[r_i^{2-n}M(B_{Lr_i}(y))]R_i(y)^{-1}
have uniformly small size relative to H_i at nearby centers and bounded cumulative sums over bounded-overlap choices. Source pi:directional-pinching gives functions E_i>0 on B_4(p) with center-independent positive floors at each i and
  sup_x sum_i E_i(x) -> 0,
  D_{i,y}[P_x-P_z] <= C_L r_i^2(E_i(x)+E_i(z))          (2.3)
whenever x,z are within a fixed multiple of r_i of y. The actual positive Bochner measure, including its singular part, is used.

(e) The continuous heat kernel obeys the Gaussian upper and first spatial gradient estimates co:kernel-bounds. The proof of co:kernel-measures extends spatial difference bounds to every source pole, by Sobolev-to-Lipschitz, symmetry, continuity, and full support. Thus they may be integrated against M. Raw mass growth co:raw-mass-growth gives, for s>=1,
  (chi M)(B_s(x)) <= C s^{n-2} I.                     (2.4)
All constants are independent of the expanding cutoff radius. Finally, the exact identity in the proof of co:heat-matrices reads
  partial_t(P_t(chi G)+lambda t I)=2P_t(chi M)+T_t,
where on fixed testing centers
  0<=T_t<=q_nu I,  sup_{0<t<=1}q_nu ->0.              (2.5)
Indeed T_t=-2kappa P_t(chi G)+P_t E_cut+lambda I; the source choice of lambda makes it nonnegative, and each of these three terms has uniformly vanishing norm. The original bounded gradients and the remote cutoff estimate establish the last assertion.

These are actual labels and proof operations in the authenticated source. No new proof of their truth is claimed.

## 3. Gaussian envelopes and exact heat increments

For any fixed c>0 define the positive matrix
  W_i^c(x)=r_i^{2-n} int exp(-c d(x,z)^2/r_i^2) chi(z) dM(z).
We first prove
  W_i^c(x)<=C_c F_i(x),
  sum_{i<k} W_i^c(x)[H_i(x)xi]<=C_c H_k(x)[xi].        (3.1)
Inside B_1(x), split into B_{r_i}(x) and the shells B_{r_j}(x) minus B_{r_{j+1}}(x), 0<=j<i. The first contribution is at most N_i. With m=i-j>=1, the shell contribution is at most
  2^{(n-2)m} exp(-c 4^{m-1}) N_j.
For fixed c,n this coefficient is bounded by C_c 2^{-gamma m}. Outside B_1, use (2.4) on shells of radii 2^l. Their total contribution is at most
  C r_i^{2-n} sum_{l>=0}2^{(n-2)(l+1)}exp(-c 4^l/r_i^2) I
  <= C_c r_i^gamma I.
The last bound follows by absorbing every fixed power into the Gaussian, uniformly for 0<r_i<=1; it also holds when n=2. This proves the first inequality, and (2.1) proves the second. The estimate is valid for the finite supported measure chi M without any dependence on the support radius.

Set
  C_i(x)=2 int_{r_i^2/4}^{r_i^2} int p_t(x,z)chi(z)dM(z)dt,
  Delta_i=Q_i-Q_{i+1},  B_i=H_{i+1}-H_i.
Equation (2.5) gives Delta_i=C_i+U_i, where
  0<=U_i<=q_nu r_i^2 I.                              (3.2)
The exact inverse formula in co:inverse-increments gives
  H_i Delta_i H_i <= B_i <= (1+o(1))H_i Delta_i H_i.
Summing and using positivity,
  0 <= H_k-H_0-sum_{i<k}H_i C_i H_i <= o(1)H_k.      (3.3)
For completeness, the additional contribution of U_i is bounded in norm by
  q_nu sum_i r_i^2 ||H_i||^2
     <= C_a q_nu sum_i 2^{-(2-4a)i}=o(1).
Since H_k>=H_0>=I/2, this is o(1)H_k. The remaining inverse-linearization error sums to o(1)(H_k-H_0). In particular the conclusion remains valid with no common eigenbasis and with H_k unbounded as k tends to infinity.

## 4. Localizing without losing the accumulated metric

Fix L>=2, later large. Choose a smooth scalar cut-off eta_0:[0,infinity)->[0,1], equal to one on [0,1/2], zero on [1,infinity), with bounded derivative. Define
  C_i^L(y)=2 int_{r_i^2/4}^{r_i^2} int p_t(y,z)
       eta_0(d(y,z)/(Lr_i))chi(z)dM(z)dt.             (4.1)
These are matrices attached to fixed centers; they will not be differentiated as functions of value coordinates. Positivity and the Gaussian bound give
  0<=C_i^L(y)<=C r_i^{2-n}M(B_{Lr_i}(y)).             (4.2)
For sufficiently late rescalings chi=1 throughout this fixed local support, but retaining chi causes no problem.

There is b_L->0, independent of i and the late rescaling, such that
  sum_{i<k}(C_i-C_i^L)(x)[H_i(x)xi] <= b_L H_k(x)[xi]. (4.3)
Indeed the difference is supported where d(x,z)>=Lr_i/2. On that set a Gaussian of exponent c is bounded by exp(-cL^2/8) times a Gaussian of exponent c/2. Integrating in t gives a constant times exp(-cL^2/8)W_i^{c/2}. Apply (3.1). This proof does not use a lower heat-kernel constant for B_{Lr_i}; such a constant might grow exponentially in L and spoil the intended gain.

There is also a C independent of L>=2 and 0<h<=1 such that, if d(x,y)<=h r_i, then for every v,
  |(C_i^L(y)-C_i^L(x))[v]|<=C h W_i^c(x)[v].         (4.4)
To prove this, integrate the source's first spatial heat-gradient bound along a minimizing geodesic from x to y, at t in [r_i^2/4,r_i^2]. The geodesic stays in a fixed testing region. The inequality d(w,z)^2>=d(x,z)^2/2-d(w,x)^2 gives, at every source pole,
  |p_t(y,z)-p_t(x,z)|<=C h r_i^{-n}exp(-c d(x,z)^2/r_i^2).
Here the factor h is retained, rather than replaced by a fixed center-separation constant. This all-pole bound follows by exactly the continuous-pole argument in paid input (e). The two scalar cutoffs in (4.1) differ by at most C d(x,y)/(Lr_i)<=Ch. Decomposing the difference of the kernel-cutoff products therefore gives the same envelope. Integrate against the positive measure M[v] and over a time interval of length at most r_i^2. This proves (4.4). Neither a gradient representative at a singular source pole nor differentiation of the distance cutoff in a nonexistent smooth coordinate system has been used.

## 5. Fine nets and the near-exact accumulated comparison

Fix 0<h<1/16, later small, before taking a late rescaling. Choose a maximal h r_i-separated finite subset Y_i of B_1(p). Use the source Gevrey-2 bump psi, equal to one on the Euclidean ball of radius 2 and supported in the ball of radius 3, to set
  psi_{i,y}(P)=psi((h r_i)^{-1}R_i(y)^{-1/2}(P-P_y)),
  g_i(P)=sum_{y in Y_i}psi_{i,y}(P),
  phi_{i,y}(P)=psi_{i,y}(P)/g_i(P),  P in Omega=u(B_1(p)).
These definitions are legitimate for all sufficiently late rescalings. At each x, a net center within h r_i has normalized coordinate separation at most h r_i+o(1)r_i<2h r_i. Thus g_i(P_x)>=1. Conversely an active bump first satisfies the fixed source support-localization argument (its support is contained in the source radius-3 normalized ellipsoid), so d(x,y)<=C_0r_i for a dimensional C_0. Normalized harmonic approximation on that fixed enlargement then gives d(x,y)<=3h r_i+o(1)r_i<=4h r_i. Uniform almost-Euclidean volume bounds and h r_i-separation bound the number of active centers by J=J(n), independent of h. In particular all active centers are within r_i of x. These arguments concern the closed support too, so they control supports of all derivatives.

We have 0<=phi<=1 and sum_y phi_{i,y}=1 on Omega. In the frozen H_i(x) source norm,
  ||D^m phi_{i,y}(P_x)|| <= C_h^{m+1}(m!)^2 r_i^{-m}. (5.1)
Here and later constants may depend on n,L,h, fixed before the rescaling. To justify division by g_i, its value lies in [1,J], and its mth normalized derivative obeys C_h^{m+1}(m!)^2. The order-m coefficient of 1/g_i is a sum over ordered compositions m_1+...+m_l=m of products (D^{m_j}g_i/m_j!), divided by a power of g_i. Since product m_j!<=m!, and there are binomial(m-1,l-1) such compositions, the sum is bounded by C_h^{m+1}m!. Multiplying back by m! gives Gevrey-2 bounds with one fixed exponential base. The product rule gives (5.1). Thus this one-time partition normalization introduces no scale-dependent loss in derivative order.

Define fixed positive matrices and weighted sums by
  A_{i,y}=(1/2)R_i(y)^{-1}C_i^L(y)R_i(y)^{-1},
  S_i(x)=sum_y phi_{i,y}(P_x)A_{i,y},
  Z_i(x)=sum_{y active at x} A_{i,y}.                 (5.2)
Their unweighted bounds are
  Z_i(x)<=epsilon_nu H_i(x),
  sum_{i<k}Z_i(x)<=C_L H_k(x),                       (5.3)
with epsilon_nu->0 for fixed L,h. This follows from (4.2), domination by a fixed multiple of the source D_{i,y}, and the paid local-mass cumulative upper estimate. Its hypotheses hold with bounded overlap J and active centers at distance <=r_i. To apply the stated cumulative lemma, give all these centers auxiliary weight one, independently of the partition weights in S_i. Any active center has B_{Lr_i}(y) containing B_{r_i}(x), after taking L>=2, so its covering hypothesis holds. Use only the lemma's unweighted upper conclusion. The constants remain fixed.

We now prove (1.1). Fix x,xi,k and put a_i=H_i(x)xi. Write R_i(y)^{-1}xi=a_i+e_{i,y}. By (4.2), the source small normalized Bochner mass, and nearby Gram comparison,
  C_i^L(y)<=epsilon_nu Q_i(x)
for active y, after enlarging epsilon_nu by fixed factors. Equation (2.2) yields
  E_k:=sum_{i<k,y}phi_{i,y}(P_x) C_i^L(y)[e_{i,y}]
      <=C epsilon_nu H_k(x)[xi].                    (5.4)
By (4.4) with 4h in place of h, the partition identity, and (3.1),
  |sum_{i<k,y}phi_{i,y} C_i^L(y)[a_i]
             -sum_{i<k} C_i^L(x)[a_i]|
      <=C h H_k(x)[xi].                             (5.5)
The first sum on the left is at most C H_k[xi], by (3.3), positivity, and (5.5). Cauchy-Schwarz for the positive forms C_i^L(y), first within each summand and then over i,y, now gives
  |2 sum_{i<k}S_i(x)[xi]
            -sum_{i<k,y}phi_{i,y} C_i^L(y)[a_i]|
      <=2 sqrt(C H_k[xi] E_k)+E_k
      <=o_L(1)H_k[xi].                              (5.6)
Combine (5.5), (5.6), (4.3), (3.3), and H_0=I+o(1). This proves (1.1), with uniformity in x,k,xi. The normalization error is not discarded scale by scale: (5.4) is the accumulated noncommuting control needed for (5.6).

## 6. Directional fields and full compatibility with the paid iteration

Use the source E_i for enlargement L and center-separation constant, say, 2. The active-patch set
  T_{i,y}={x in B_1(p): P_x belongs to supp psi_{i,y}}
is nonempty, contains y, and lies in B_{4h r_i}(y). Its infimum of E_i is positive by the source floor. Choose a fixed z_{i,y} in this set with E_i(z_{i,y})<2 inf_{T_{i,y}} E_i, and put c_{i,y}=P_{z_{i,y}}. No parameter-continuous or measurable choice is claimed or needed; the net at each scale is finite. Define the smooth field on Omega
  v_i(P)=sum_y phi_{i,y}(P)A_{i,y}(P-c_{i,y}).        (6.1)
By (4.2) and source directional pinching,
  A_{i,y}[P_x-c_{i,y}]<=C_L r_i^2 E_i(x)              (6.2)
at every point where that patch or one of its derivatives is active. Also |P_x-c_{i,y}|_{H_i(x)}<=C r_i by nearby harmonic normalization.

Enlarge epsilon_nu so that sup_x sum_i E_i(x)<=epsilon_nu and (5.3) holds. This still tends to zero, for fixed L,h. Put r=r_i, H=H_i(x), Q=H^{-1}, q=|xi|_H, E=E_i(x), Z=Z_i(x), S=S_i(x). Positivity gives A Q A<=epsilon_nu A for each active A, and |xi^T A w|^2<=A[xi]A[w]. Equations (5.1), (6.2), and bounded overlap therefore give

  |v_i|_Q <= C sqrt(epsilon_nu) r sqrt(E),
  Dv_i xi=S xi+e_i(xi),
  |S xi|_Q <=sqrt(epsilon_nu Z[xi]),
  |e_i(xi)|_Q <= C sqrt(epsilon_nu E) q,
  |xi^T e_i(xi)| <= C sqrt(Z[xi]E)q,
  r |D^2v_i(xi,xi)|_Q
       <= C(sqrt(Z[xi])q+sqrt(E)q^2),                (6.3)

and, in all orders m>=0,
  r_i^{m-1}||D^m v_i||_{H_i(x)->Q_i(x)}
       <=epsilon_nu C_v^{m+1}(m!)^2.                (6.4)
For the diagonal first-derivative error, explicitly
  e_i(xi)=sum_y Dphi_{i,y}(xi) A_{i,y}(P_x-c_{i,y});
apply matrix Cauchy-Schwarz before summing. The two second-derivative terms are D^2phi(xi,xi)A(P_x-c) and 2Dphi(xi)Axi, giving (6.3). In order m only the mth derivative of the cutoff and the m terms with one derivative on the affine factor occur. Using (5.1), A<=epsilon_nu H, and |P_x-c|_H<=Cr proves (6.4). The dependence on h affects fixed constants, not factorial order or the scale index. These are exactly the field interfaces used in re:field-estimates, now proved for the new fields.

Set h_0(P)=P and iterate on the same open domain Omega:
  h_{i+1}=h_i+J_i^{-T}v_i,  J_i=Dh_i.                (6.5)
We use the source inverse-majorant and all-jet step with rough bootstrap A_boot=2 and sigma=2. All their hypotheses are (6.4), H_i<=H_{i+1}, and the old-level metric bound; no special formula for the original cutoff sums is used in those proofs. Choose the jet constant B after n,L,h. The bounds obtained are
  r_i^{m-1}||D^m h_i||_{H_i(x)->R^n}
       <= B^{m-1}(m!)^3,  m>=2.                     (6.6)
The source's inverse-majorant proof ensures one fixed exponential base B for all orders; the r_{i+1}/r_i factor absorbs the one-derivative loss simultaneously in all orders. No new-level inverse is assumed to prove the jet update.

For clarity, the metric part of this reuse is given explicitly next. Under the rough metric bound through old levels, put b_i=r_i|D^2h_i(xi,xi)|/q_i, q_i=|xi|_{H_i(x)}. Differentiating J_i^{-T}v_i twice and using (6.3), the jet estimates through order three, and frozen norm duality gives
  b_{i+1}<=b_i/2+C(sqrt(Z_i[xi])+sqrt(E_i)q_i), b_0=0.
Convolution on l^2 and (5.3) imply
  sum_{i<k} b_i^2 <= C H_k[xi].                     (6.7)
Also
  |(J_{i+1}-J_i)xi|^2
       <=C epsilon_nu(Z_i[xi]+E_i q_i^2).            (6.8)
The exact differentiated-inverse identity is
  |J_{i+1}xi|^2-|J_i xi|^2
   =2 S_i[xi]+2xi^T e_i(xi)
    -2<D^2h_i(xi,xi),J_i^{-T}v_i>
    +|(J_{i+1}-J_i)xi|^2.
The two linear error sums are bounded by C sqrt(epsilon_nu)H_k[xi]: for the first use Cauchy-Schwarz with sum Z_i[xi]<=C_L H_k[xi] and sum E_i q_i^2<=epsilon_nu H_k[xi]; for the second use (6.7) and that same E_i sum. Sum (6.8) for the quadratic error. Thus
  |(J_k^T J_k-I-2 sum_{i<k}S_i)[xi]|
       <=C_{L,h}(sqrt(epsilon_nu)+epsilon_nu)H_k[xi]. (6.9)
In particular no sum of sqrt(E_i) is required.

Choose L,h so that b_L+Ch<1/8, then a late enough rescaling that the remainder in (1.1) and (6.9) is less than 1/8. These estimates give, with slack, (1/2)H_k<=J_k^T J_k<=2H_k. Initially J_0=I and H_0=I+o(1). At the next step smoothness of the old inverse defines h_{i+1} on all of Omega; (6.9) at k=i+1 uses only old inverses and jets, proving new invertibility, and the paid all-jet step proves (6.6). This closes the simultaneous finite-scale induction. The finite approximants need not be globally injective.

More precisely, by first making L large, then h small, and finally taking the source rescaling late, (1.1) and (6.9) give, for any prescribed 0<theta<1/100,
  (1-theta)H_i(x)<=J_i(P_x)^T J_i(P_x)
                    <=(1+theta)H_i(x)              (6.10)
uniformly for every x in B_1 and every i. The constants B and the late threshold can depend on theta through L,h. This is an arbitrary-accuracy conclusion, not an explicit modulus in the initial GH error.

## 7. From the refined differential estimate to all ambient pairs

By the first line of (6.3) and the rough inverse bound,
  |h_{i+1}(P_x)-h_i(P_x)|<=C_{L,h}epsilon_nu r_i.
Hence F=lim_i h_i o u exists uniformly on B_1, is continuous, and
  sup_{B_1}|F-h_i o u|<=tau_nu r_i,
  tau_nu=C_{L,h}epsilon_nu ->0.                     (7.1)

Fix theta as above. Choose L,h and B as in Section 6. In the central H_i(x)-ellipsoid, each segment point P_y has y in B_{r_i}(x), and (6.6) with m=2 gives
  |D^2h_i(P_y)(zeta,zeta)|
     <= (K_2 C_cmp/r_i)|zeta|_{H_i(x)}^2,
where K_2=8B. Put K_T=K_2 C_cmp/2. Choose a fixed D so large that
  (1+theta)/D<a_c,
  K_T(1+theta)^2/D<=theta.                          (7.2)
Take the geometric rescaling further along the SAME sequence so that every preceding estimate holds and
  ||P_z-P_x|_{H_i(x)}-d(x,z)|<=theta d(x,z)
  whenever r_i/(2D)<d(x,z)<=r_i/D,                  (7.3)
  4D tau_nu<=theta.                                (7.4)
Condition (7.3) follows from the full o_D(1) harmonic pair approximation and Q_i/R_i->I, not merely the weaker 1/2 and 2 constants displayed in the source's final proof. All ratios are fixed before this further rescaling.

Let rho=(16D+4)^{-1}. For any distinct x,z in B_rho(p), put t=d(x,z) and choose i with Dt<=r_i<2Dt. Then r_i<4D rho<1 and B_{r_i}(x) is contained in B_1(p). Set Delta=P_z-P_x. Equation (7.3) gives (1-theta)t<=|Delta|_{H_i(x)}<=(1+theta)t. By (7.2), the entire straight segment from P_x to P_z is in the central ellipsoid, and thus in u(B_{r_i}(x)). Taylor's formula is therefore legitimate on a segment whose every preimage has the needed estimates. It yields
  h_i(P_z)-h_i(P_x)=J_i(P_x)Delta+R_i^T,
  |R_i^T|<=K_T|Delta|_{H_i(x)}^2/r_i<=theta t.        (7.5)
The superscript T denotes a Taylor remainder, not a transpose.

Equation (6.10) implies
  sqrt(1-theta)(1-theta)t<=|J_i(P_x)Delta|
                  <=sqrt(1+theta)(1+theta)t.
By (7.1), (7.4), the two limit tails together are at most 4D tau_nu t<=theta t. Thus
  (1-4theta)d(x,z)<=|F(x)-F(z)|<=(1+4theta)d(x,z)    (7.6)
for all pairs in B_rho(p). For example, the lower bound follows from sqrt(1-theta)>=1-theta and (1-theta)^2-2theta>=1-4theta; the upper follows from sqrt(1+theta)<=1+theta/2 and 3theta/2+theta^2/2+2theta<=4theta for theta<=1. This is a direct ambient-distance argument. No geodesic is required to stay in the final chart ball, and no intrinsic length metric or a.e. differential estimate is substituted for (7.6).

## 8. Openness and choice of distortion

Given eta>0, choose
  0<theta<min(1/100, eta/(8(1+eta))).
Then 1-4theta>=(1+eta)^{-1} and 1+4theta<=1+eta. Equation (7.6) proves injectivity and a continuous inverse on the image. By the paid open-harmonic-coordinate result, u(B_rho(p)) is open in R^n. The continuous injection F o u^{-1} on this open set has open image by invariance of domain. Translating its target by -F(p) makes it pointed and preserves the comparisons.

This argument needs neither a smooth inverse theorem on the RCD space nor regularity of the limit coordinate components. Its only ordinary derivatives are those of the finite smooth h_i on Euclidean value space.

## 9. Return to the original units and the full frozen scope

For the original prescribed R>0, choose the late index also so that s_nu rho<R. Set r=s_nu rho and multiply target coordinates by s_nu. The rescaled Hausdorff reference measure is exactly H_{d/s_nu}^n=s_nu^{-n}H_d^n; it is never replaced by an arbitrary weight. Multiplication of both distance units gives exactly
  (1+eta)^{-1}d(x,z)<=|F(x)-F(z)|<=(1+eta)d(x,z)
on B_r^d(p), with F(p)=0 and open Euclidean image. This proves the whole frozen statement at its original hypotheses and quantifiers.

The order of choices is: n and eta; theta; localization radius L; fine spacing h; rough bootstrap 2 and Gevrey constants; jet constant B; pair-scale constant D; then the late geometric rescaling satisfying all fixed-parameter smallness conditions and the requested original radius R. There is no circular dependence. Point regularity supplies the rescaling sequence; nothing in this proof identifies the open chart domain with the exact regular set. Different eta may require different, smaller domains and different charts. Therefore no nearby singular point is forced to be regular by this conclusion.

## 10. Compatibility, comparison, and limits of the submission

The new accumulated estimate is (1.1). Every difficult source operation listed in Section 2, the directional pinching, inverse-majorant induction, diagonal derivative recurrence, and the segment/invariance-of-domain strategy are credited as supplied. Sections 3–5 give the extra heat-source localization and fine interpolation needed to make the leading metric approach H_k with relative error tending to zero; ordinary rescaling of the supplied L_n chart or shrinking its final Taylor error does not establish that estimate.

The regime is nonempty and the distortion parameter is a real additional request, not a variable secretly fixed by the hypotheses. In every smooth Riemannian n-manifold with a Ricci lower bound, all tangents are Euclidean; local smooth coordinates and continuity of the metric give arbitrarily small distortion on sufficiently small balls. A round sphere satisfies these hypotheses and has nonzero sectional curvature, so the assertion does not force a locally Euclidean isometry. For a direct ambient-distance check in this example, choose a larger normal-coordinate ball with (1+delta)-controlled metric, then a smaller concentric ball such that any ambient minimizing geodesic joining its points cannot exit the larger ball (an exit costs more than an available short interior curve). Integrating in the larger ball gives both bounds. These smooth examples establish compatibility only, not contribution beyond classical work.

The primary comparisons are scoped in semantic-reads.jsonl and primary-comparison.md. The metric Reifenberg product construction works under summability of ordinary dyadic GH errors; its summable regime must be credited. Extrinsic coherent-plane square-summability is also paid classical machinery. Honda–Zhang's analytic criteria require neighborhood nondegeneracy and Laplacian/Morrey hypotheses, which are not silently supplied for the limit F. The present proof does not assert that no other literature proves the conclusion, that an explicit nonsummable RCD example has been separated from every existing theorem, or that the additional estimate deserves a substantial-contribution grade. Those are independent-review questions for the parent.

No downstream formalization or manuscript/release work has been performed. The exact pinned Lean endpoint was unavailable (404), so formal support is none. The author proof is submitted for review, with no self-assigned gate or count.
