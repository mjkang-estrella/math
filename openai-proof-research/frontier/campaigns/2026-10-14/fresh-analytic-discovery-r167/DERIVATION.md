# r167 — prefreeze integrated quadratic-field calculation

This is a worked reduction, not a frozen discovery nominee or a contribution verdict. Authorized provenance: Codex / GPT-6 Astra / high / default service tier. The entire pinned source theorem/proof package is stipulated true. The principal walk and spectral operative proofs were read before this development; primary and companion reading limits are in private/READING-LIMITS.md. All assertions below concern the ordinary unit-area sqrt(3) sphere, the original q=2 all-edge maps, degree measure, and the source's canonical three-mark coordinate. No uniformity in q, annealed moments, microscopic rate, or nonstationary path theorem is inferred.

## 1. Exact operator and geometric interface

Write mu_n(v)=deg(v)/(2n), P_n for one half-edge attempt, A_n=n(I-P_n), and B_n=2A_n. Then

    <u,A_n u>_mu_n = (1/2) sum_e (u(e+)-u(e-))^2.

A loop is a possible holding attempt and contributes zero energy; parallel edges retain multiplicity. The raw source inverse is K_n=B_n^dagger on mean-zero functions, not A_n^dagger. Embed it by the source's first corner tour in H=L2([0,1],dt), and extend it by zero on constants and on the orthogonal complement of the vertex subspace. The source proves

    ||K_n-K||_S2 -> 0,
    K(t,u)=G_mu(eta(t),eta(u)),
    G(x,y)=-(1/(2pi)) log ch(x,y)+c,

where G_mu is G centered in both mu variables. The limiting tour identifies H unitarily with L2(mu): its fibers are singletons mu-almost everywhere, not everywhere. On a common source extraction, for each f continuous on S2,

    f_n(t)=f(z_n(v_n(t))) -> f(eta(t))=f_infty(t)

uniformly. The canonical coordinate comes from actual fresh area marks after the reference homeomorphisms; the same possible global reflection acts on every retained object. No conditional independence of that reflection is needed here.

The source's mechanisms behind this interface are stronger than eigenvalue convergence alone: exact incidence reconstruction and conditional local laws; noncollapsing primal/dual flows; scalar electrical identification by complementary conductances; uniform energy compactness at all levels; exclusion of a diverging first inverse eigenvalue; and identification by arbitrary four DISTINCT limiting positions. Its p=7/10 eigenvalue bound supplies square-summable inverse tails. The distinct-position qualification is material below.

Fix a>0. Introduce the killed Brownian-clock resolvent, embedded and zero on the extra discrete complement:

    C_n = a^-1 Pi + 2K_n(I+2aK_n)^-1,
    C   = a^-1 Pi + 2K  (I+2aK  )^-1.                 (1)

Pi is the common rank-one projection onto constants. Both operators are positive, self-adjoint and Hilbert–Schmidt. The zero-complement convention is essential: (A_n+a)^-1 is taken on the vertex subspace before embedding; it is not a^-1 on its orthogonal complement.

If R_n=(I+2aK_n)^-1 and R=(I+2aK)^-1, the algebraic identity

    K_n R_n-K R = R_n(K_n-K)R

is valid without commutation between K_n and K. Since ||R_n||,||R||<=1,

    ||C_n-C||_S2 <= 2||K_n-K||_S2.                   (2)

The bound is uniform for a in a compact positive interval; the constant mode remains finite there. In what follows a is fixed.

## 2. Finite loop normalization and the primary operation

For the accelerated walk killed at rate a in accelerated time, use its symmetric heat density with respect to mu_n. A loop's occupation measure is integral_0^T delta_{X_s} ds; the vertex density is occupation time divided by mu_n(v). For a Poisson ensemble of Markov loops of intensity alpha>0, subtract its mean alpha c_n(v,v) from this density. Denote the resulting signed measure by Z_n:

    Z_n(f)=sum_v mu_n(v) f(z_n(v))
                   [L_n(v)-alpha c_n(v,v)].          (3)

The finite mean is retained exactly, however large. Replacing it by a universal logarithm is not justified. Constant killing makes long loops integrable; the trivial-loop convention is included by the standard continuous-time loop measure. It does not depend on whether self-loops are represented as explicit attempts or suppressed holding events, since the generator and actual-time occupation agree.

Le Jan, arXiv:0802.2478v3, Sections 3–5 and 9, supplies the operative mechanism. Here is its calculation in the current normalization. For l(f)=integral_0^T f(X_s)ds, the ordered m insertion times in a rooted loop, cyclic re-rooting, and the dt/t factor give

    loop_measure(l(f)^m)=(m-1)! Tr((M_f C_n)^m), m>=2. (4)

Indeed split the loop into m successive time intervals, integrate each killed transition density over its interval to obtain C_n, and use cyclicity to remove the choice of root. The m! orderings divided by m give (m-1)!. This proves (4) initially for f>=0 by Tonelli; domination by ||f|| times the duration proves the signed version. For m=2 it is the nonnegative integral of f(x)f(y)c_n(x,y)^2. The compensated Poisson exponential therefore has, near t=0,

    log E exp(t Z_n(f))
       =alpha sum_{m>=2} t^m Tr((M_fn C_n)^m)/m.      (5)

Equivalently for f>=0 its Laplace transform is det_2(I+t M_sqrt(f) C_n M_sqrt(f))^-alpha. The variance is

    Cov(Z_n(f),Z_n(g))
       =alpha integral f_n(t)g_n(u)c_n(t,u)^2 dt du.  (6)

At alpha=1/2, Gaussian integration gives exactly

    Z_n = (1/2) [Phi_n^2-E Phi_n^2] mu_n,
    E Phi_n(v)Phi_n(w)=c_n(v,w).                     (7)

Thus there are TWO distinct factors of two: C_n is the inverse of the half-energy generator; the loop intensity one-half corresponds to one-half of its Gaussian Wick square. No additional factor n or 2n belongs in (3).

The primary PDF itself has minor inconsistent intermediate displays on page38 (a missing alpha in a variance line and a sign in the prose exponential). The Poisson exponent, Theorem26 and final covariance on that page determine the correct signs and alpha used above. These are not allegations about the stipulated upstream source. The page image was inspected rather than treating text extraction as an authoritative formula.

## 3. Continuum construction without a trace-class assumption

The source has a regular conservative symmetric LBM and an L2 Green kernel. Killing at a supplies a transient resolvent C. Its positive-time semigroup is trace class by the source eigenvalue lower bound. Transition densities can be obtained spectrally in L2(mu x mu); the regular diffusion supplies the usual bridge loop construction at almost-everywhere endpoints. The same ordered-time calculation (4), with Tonelli, gives

    loop_measure(l(1)^2)=Tr C^2<infinity.

For every cutoff epsilon>0, loops of duration at least epsilon have finite intensity, since integral_epsilon^infinity e^-at Tr(P_t)dt/t<infinity. Their centered occupation measures converge on each bounded test in L2 as epsilon decreases to zero: the squared difference is alpha times the loop integral of l(f)^2 on the omitted durations, which tends to zero by integrability. This defines Z. Formulae (5) and (6) pass to it. This replays the operative proof of Le Jan Lemma25/Theorem26; that theorem's printed polar-point setting is killed ordinary Brownian motion in domains in dimensions2/3, so it is not cited verbatim as a theorem about the quantum sphere. The semigroup cycle argument above is the required compatibility extension.

One can avoid all bridge conventions at alpha=1/2. Let e_i be eigenvectors of C with eigenvalues c_i, and take independent standard normal xi_i. Finite sums Phi_N=sum_{i<=N} sqrt(c_i)xi_i e_i have well-defined squares as distributions against mu. Put W_N(f)=integral f(Phi_N^2-E Phi_N^2)dmu. Wick's elementary Gaussian pairing yields

    E W_N(f)W_M(g)=2 integral f(x)g(y)c_min(N,M)(x,y)^2 dmu(x)dmu(y).

As c_N -> c in L2, c_N^2 -> c^2 in L1, because

    ||c_N^2-c^2||_1 <= ||c_N-c||_2(||c_N||_2+||c||_2).

The displayed covariance identity makes W_N(f) Cauchy in L2. This defines W(f)=:Phi^2:(f). The finite Gaussian determinant and (5) identify Z at alpha=1/2 with W/2. This proof needs no unproved Schatten square-root continuity result and no pointwise continuum variance.

## 4. Convergence of every finite family of tests

Set D_n=M_fn C_n and D=M_f C on the common tour Hilbert space. Operator-norm convergence of the multipliers and (2) give D_n -> D in S2. These operators need not be self-adjoint for signed f; this causes no trace difficulty. If R bounds their operator norms and H bounds their S2 norms, telescoping gives for m>=2

    |Tr(D_n^m-D^m)|
       <= m ||D_n-D||_S2 H R^(m-2),                 (8)

with H increased to bound both norms. Each summand is a product of two Hilbert–Schmidt factors and bounded intervening factors, hence trace class. Also

    |Tr(D_n^m)| <= H^2 R^(m-2).

Thus (5) converges uniformly for t in a sufficiently small real or complex neighborhood of zero. These bounds provide a uniform two-sided exponential moment there, so second-moment tightness and moment determinacy identify the limiting law. Applying the argument to each real linear combination of finitely many continuous f_i proves joint convergence of Z_n(f_i) to Z(f_i). This is stronger than an argument based only on eigenvalues, because multiplication by spatial tests does not commute with C_n; the tour multiplier convergence handles that compatibility.

Alternatively the determinant is defined by its eigenvalue product after symmetrization C_n^(1/2)M_f C_n^(1/2). Its S2 norm is bounded by ||f||_infty ||C_n||_S2, using two Schatten4 factors. Equation(8) proves the needed convergence without invoking a square-root perturbation theorem.

## 5. Tightness as spatial distributions, all s>1

Use real round spherical harmonics Y_lm orthonormal for round area, and the H^-s norm defined by weights (1+l(l+1))^-s. Regard Z_n as a signed atomic distribution in the canonical coordinate, not as a density with respect to round area. The addition formula gives

    |sum_{m=-l}^l Y_lm(x)Y_lm(y)| <= (2l+1)/(4pi).

Apply (6), sum over m first, and use positivity of the squared kernel to obtain

    E ||Z_n||_H^-s^2
      <= alpha ||C_n||_S2^2/(4pi)
             sum_{l>=0} (2l+1)(1+l(l+1))^-s.         (9)

The sum is finite exactly when s>1. The same calculation applies to continuum duration cutoffs; dominated convergence of their loop second moments makes them Cauchy in L2(H^-s). It also applies to the spectral Gaussian construction by the L1 convergence of squared covariance kernels. Hence these constructions define actual H^-s-valued random variables, not just a cylindrical family.

For fixed s>1 choose 1<s'<s. Uniform conditional bounds in H^-s' from (2),(9), and the compact embedding H^-s' into H^-s, prove tightness. Finite harmonic coefficients converge by Section4, identifying every limit. We have proved on each source coupling

    Law(Z_n | map and coordinate data)
        -> Law(Z | limiting surface data) in H^-s, s>1. (10)

No averaging of the random HS bounds is required. For joint random-environment convergence, first restrict to the events where those bounds are <=R, whose probabilities tend to one as R increases on an almost-sure source extraction; use conditional weak convergence and bounded test functions, then remove that restriction. The source's subsequence principle yields the corresponding full-sequence law. This is not convergence in conditional total variation, a quenched almost-sure theorem for an originally specified coupling, or convergence of annealed second moments.

## 6. Why this closed calculation is not offered as the remaining discovery

The source pays the exact spatial HS inverse interface. Le Jan pays compensated occupation, determinant cumulants and the half-intensity Wick-square correspondence. Trace-ideal continuity, Cramer–Wold, and the spherical-harmonic addition formula finish (10). None supplies a new microscopic probabilistic estimate. The construction is retained to show the strongest integrated reduction was carried to an actual distribution-valued conclusion; it is not submitted for a desired substantial grade.

Higher renormalized powers differ. Their covariance contains c(x,y)^(2k), as Le Jan's actual Laguerre cancellation proof in Section10 shows. At k=2, the discrete fourth kernel moment already appears. The finite-polynomial cancellation is paid; uniform integrability of those kernel powers at merging discrete positions is not proved here. OBSTRUCTION.md computes this distinction with exact finite Markov networks and identifies what the stronger source operations do and do not control.
