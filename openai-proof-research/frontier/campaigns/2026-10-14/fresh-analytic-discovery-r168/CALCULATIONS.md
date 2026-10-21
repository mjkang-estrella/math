# r168 prefreeze calculations — exact reversibility and the surviving scalar noise

Status: feasibility mathematics, no frozen discovery statement and no nominee. These calculations use SOURCE219 as true, including its operative proofs. They are not offered as a separate substantial result. Authoring began after the complete two canonical TeX/Bib sets, the relevant permitted original-history sections, and the selected primary operations recorded in private/READING-LIMITS.md had been read. Provenance: Codex / GPT-6 Astra / high / default service tier, as authorized. No independent review or acceptance is asserted.

## 1. The exact coefficient, not its first-order approximation

Use the Anderson source's conventions: ordinary adjacency, fixed d >= 3, fixed permitted w > 0, a fixed compact clean-band energy E, and rho = rho_{d,w}(E) > 0. Conditional on the tree environment excluding its root potential, put

    m(v) = (v-A-iB)^(-1),  B > 0,
    a(v) = Re m(v),  b(v) = Im m(v),  c(v) = b(v)/(pi rho).

The root potential is uniform on [-w,w]. Let A_good be the source's positive-probability, root-excluded event on which |A| <= C0 and c0 <= B <= C0. In this paragraph A_good denotes an event; A denotes the real intercept. On this event a,c and their first derivatives are uniformly bounded, and c has a positive uniform lower bound. Partition [-w,w] into N intervals of length 2 ell, ell=w/N, and exchange each interval's halves. Off A_good do nothing. Write h(v) for the increment, equal to +/-ell at active roots, and v'=v+h(v). This is an involution preserving the conditional uniform measure.

The source's effective rank-one coefficient is

    beta(v,h) = c(v) h / (1+a(v)h).

For all sufficiently small ell its denominator is bounded away from zero. Set Delta=|1+h m(v)|^2. The exact resolvent identity, with all real and imaginary parts retained, gives

    m(v+h)=m(v)/(1+h m(v)),
    a(v+h)=[a(v)+h(a(v)^2+b(v)^2)]/Delta,
    c(v+h)=c(v)/Delta,
    1-h a(v+h)=(1+h a(v))/Delta.

Consequently

    beta(v+h,-h) = -beta(v,h).                                      (1)

No small-h expansion occurs in (1). The selection event is unchanged under the involution precisely because it excludes the root potential. Change variables v -> v' in the conditional integral. The conditional law of beta is symmetric, so its mean and every odd moment are exactly zero. This holds conditional on each root-excluded environment, not conditional on its already sampled original root value. In particular E s1=0 for s1=sum beta_alpha. The source's stated O(r ell^2) mean bound is compatible but weaker.

This cancellation does NOT imply s1 -> 0. Define

    kappa_A = E[1_{A_good} c(V)^2],  0 < kappa_A < infinity.

Since |beta|<=C ell and beta^2/ell^2 -> 1_{A_good} c(V)^2 uniformly in V on each good environment with a common bound,

    E beta^2 / ell^2 -> kappa_A.                                   (2)

With r independent sampled roots and r ell_r^2 -> t in (0,infinity),

    s1 => Normal(0,t kappa_A),    s2=sum beta_alpha^2 -> t kappa_A

(the second in L2). For s2, Var(s2)<=Cr ell_r^4 ->0. For s1 the centered triangular-array Lindeberg condition follows from |beta|<=C ell_r. One can choose N_r as the nearest positive integer to w sqrt(r/t), so the interval partition imposes no arithmetic obstruction. These limits take place after the graph-size limit, inside the source's independently marked limiting space.

## 2. Joint Gaussian block limit and its covariance

Fix q, independent of r. Let g_alpha be iid N(0,I_q), independent of all environments and potentials. They are the standardized source marks in q fixed spectral coordinates. Define the symmetric q-by-q matrices

    Z_r = sum_{alpha=1}^r beta_alpha g_alpha g_alpha^T,
    Y_r = sum_{alpha=1}^r beta_alpha (g_alpha g_alpha^T-I_q).

Exactly, Z_r=Y_r+s1 I_q. For a symmetric test matrix U,

    Tr(U Z_r)=sum beta_alpha g_alpha^T U g_alpha.

Independence, (1), and Gaussian pairings give

    Cov((Z_r)_{ij},(Z_r)_{kl})
      = r E beta^2 (delta_ij delta_kl + delta_ik delta_jl + delta_il delta_jk).

The bound sum E|beta g^T U g|^3 <= C_{q,U} r ell_r^3 ->0 proves the scalar Lindeberg condition for every U and hence the finite-dimensional multivariate central limit. More specifically,

    Cov(s1,(Y_r)_{ij})=0,
    Cov((Y_r)_{ij},(Y_r)_{kl})
       = r E beta^2 (delta_ik delta_jl + delta_il delta_jk).

Apply the same argument jointly to s1 and all entries of Y_r. The limiting Gaussian blocks are independent because their cross covariance vanishes. Thus

    (s1,Y_r) => sqrt(t kappa_A) (Z,W_q),
    Z_r => sqrt(t kappa_A) (W_q+Z I_q),                            (3)

where Z is standard normal and W_q is raw GOE (off-diagonal variance 1, diagonal variance 2), independently. The source's conditional Gaussian replacement already supplies Y_r's covariance. Averaging over the environments leaves the additional scalar component in (3). The independent scalar is not an error in the replacement and must not be silently deleted in a prospective time theorem.

For comparison, after conditioning on all beta_alpha, E_g Z_r=s1 I and Cov_g(Z_ij,Z_kl)=s2(delta_ik delta_jl+delta_il delta_jk). Averaging this conditional covariance and adding the covariance of its conditional mean recovers all three pairings. This calculation identifies the precise conditioning responsible for the extra component.

The Gaussian environments and marks can be made independent of the original limiting point process nu, as in SOURCE219. Therefore (3) is jointly valid with any bounded observable of nu. It remains a fixed-q matrix assertion. It supplies neither the spectral tail passage q -> infinity at fixed time nor the finite-n, all-site dynamics below. Proving (3) is an elementary central-limit use of an already supplied marked law; it is not nominated.

## 3. Scales and the point at which source insertion stops helping

The full source uses T=r^tau -> infinity, K=r^(1/100), L=r^(100/chi), and ell comparable to sqrt(T/r), after n -> infinity. Its weighted Schur reduction and Lindeberg error K^6 r ell^3 ->0 close that comparison, including the real constants and principal-value tail. This is an actual stronger integrated mechanism than a bare finite-rank resolvent formula. At those scales (1) improves E s1 to zero and implies s1=O_P(sqrt(T)); it does not change the paid universality theorem into a new theorem.

For a candidate finite-time process, T must instead stay of order one and many updates must be compared jointly. One cannot substitute finite T into the source's final long-time DBM relaxation and claim a process law. Neither (3) nor static invariance determines its transition kernel. The source switches have invariance after averaging, whereas its Gaussian comparison is conditional on the old spectrum and environments. These quantifiers must remain distinct.

This observation is consistent with the actual LSY v4 proof, Section 7.2: its multitime conclusion uses the SAME DBM noise and the same homogenized mesoscopic shift at both times. It is not a theorem that every process with GOE one-time marginals is DBM.
