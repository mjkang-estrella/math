# Radial spin fluctuations in a diffusive low-temperature window

Myeongjin Kang — no affiliation. Original prose: CC BY 4.0.

Status: author proof of frozen target RF; independent proof and contribution reviews pending. This document does not award a campaign count or claim demonstrated novelty to the literature.

## 1. Statement and antecedents

Fix S in {1/2,1,3/2,...}. On the even periodic cubic torus Lambda_L=(Z/LZ)^3, L>=4, write V=L^3 and

    H = sum_{unordered nearest-neighbor xy} (S^2-S_x dot S_y).

The physical zero-field Gibbs law is the normalized trace of exp(-beta H). Let J be the total-spin label, D=SV-J, and set

    epsilon(k)=2S sum_{j=1}^3(1-cos(2 pi k_j/L)),
    mu=sum_{k != 0}(exp(beta epsilon(k))-1)^(-1),
    a=beta/L^2.

Mode representatives always belong to [-L/2,L/2)^3 intersect Z^3. For EVERY sequence beta -> infinity and even L with

    beta^(501/1000) <= L <= beta^(51/100),                         (1.1)

we prove

    a(D-mu) => W_S=sum_{k in Z^3\{0}} (E_k-1)/(4 pi^2 S |k|^2),  (1.2)

where the E_k are independent mean-one exponentials and the centered series converges in L^2. Moreover, for every real lambda>=0,

    E_phys exp[-lambda a(D-mu)]
      -> product_{k != 0} exp(lambda/c_k)/(1+lambda/c_k),
    c_k=4 pi^2 S |k|^2.                                       (1.3)

The limit has positive variance and is non-Gaussian. The centering in this statement is precisely the finite ideal-mode sum mu. No assertion about the interacting mean or all its moments is made.

The classical inputs are from Correggi–Giuliani–Seiringer (CGS), *Validity of the spin-wave approximation for the free energy of the Heisenberg ferromagnet*, arXiv:1312.7873v2, §§3–6.1. Their Holstein–Primakoff formulation, projected trial state, entropy inequality, Casimir bound, rough finite-box partition bound, interaction inequality, and local two-particle subsolution are credited below. Chatterjee–Diaconis (CD), *Fluctuations of the Bose–Einstein condensate*, arXiv:1306.3625v2, Theorems 2.2–2.3 and the proof for 1<alpha<2, already provide the centered geometric/exponential-series limit mechanism. We reproduce the elementary changing-lattice version solely to finish the deduction.

Family271's pinned Bloch/spherical-magnetization papers motivate the question and identify the total-spin observable. Their fixed-temperature thermodynamic concentration is not used to infer a fluctuation estimate. The load-bearing prior estimates here are classical CGS. The steps needing separate verification are the periodic two-particle estimate, absolute partition comparison uniform down to a vanishing auxiliary field, and exact removal of the SU(2)/boson zero-mode factors. A contribution judgment about those steps is reserved for independent review.

All constants below may depend on fixed S; constants with a subscript B may also depend on a fixed finite upper bound B for lambda. None depends on beta or L. Assertions called uniform concern (1.1).

## 2. Classical inputs and conventions

Choose the spin axis so that the Holstein–Primakoff particle number is N=SV-M^3. A rotation changes CGS's opposite axis convention without changing H. The spin space embeds into bosonic Fock space as the subspace P_S with 0<=n_x<=2S. The unconstrained kinetic energy is

    T=S sum_{xy}(a_x^dagger-a_y^dagger)(a_x-a_y)
      =sum_k epsilon(k)n_k.

CGS's local algebra applies bond by bond, so its following identities and inequalities apply to the torus with the same constants.

(A) On the physical space H=P_S T P_S-K, and CGS Lemma 5.4 gives

    K <= (1/2)sum_{xy}[4 n_x n_y+n_x(n_x-1)+n_y(n_y-1)].        (2.1)

(B) Let P project onto n_x<=1 at every site. CGS Lemma 4.2 gives, as an inequality on full Fock space,

    P(H+hN)P <= T+hN+(2S-1)sum_{xy}n_xn_y,  h>=0.             (2.2)

Indeed its local proof is unchanged by periodic bonds, and PhNP<=hN.

(C) CGS Proposition 5.2 and Lemma 5.3, first on the open cube and then by adding nonnegative wrap-around bonds, give

    H >= c_S L^-2 D,                                         (2.3)
    log Tr_spin exp(-bH) <= C_S L^3 b^-3/2 (log b)^(5/2)       (2.4)

for large b and L>=sqrt(bS). An adjustment of the fixed constants absorbs log(bS). The deficit operator commutes with both the open and periodic Hamiltonians. To pass the trace bound to the torus, the min-max principle suffices; operator monotonicity of the exponential is not presumed. We use (2.4) only for b=beta/2 and (1.1), where its side-length condition holds eventually for every fixed S.

(D) If psi is a normalized simultaneous H,N eigenvector, of eigenvalues E,n, define

    rho(x,y)=<psi,a_x^dagger a_y^dagger a_y a_x psi>.

It is nonnegative and sum_{x,y}rho(x,y)=n(n-1). Put w(x,y)=1-delta_xy/(2S). For S>=1 let sigma=rho/w on all ordered pairs; for S=1/2 use only ordered distinct pairs and sigma=rho there. On this state space define

    A f(z)=sum_{z'~z} w(z')[f(z')-f(z)],                       (2.5)

where one coordinate moves along one torus edge. For S=1/2, w=1 on the state space, and moves onto its removed diagonal are omitted. CGS Lemma 6.1, specifically (6.9)–(6.11), is exactly

    -A sigma <= (2E/S)sigma.                                 (2.6)

Its proof sums positive local bond squares and uses the eigenvector equation; it requires neither an open boundary nor E>0. The reversible measure for (2.5) is w(z), and its edge conductances are w(z)w(z').

These four classical inputs are the only external spin estimates used. The entropy estimate used below is proved directly in §5, following CGS Lemma 4.4.

## 3. A periodic two-particle bound, including zero energy

We prove for every simultaneous eigenvector as above

    ||rho||_infinity <= C_S (E+L^-2)^3 n(n-1).                 (3.1)

First the semigroup P_t=exp(tA), with kernel relative to measure w, satisfies

    ||P_t||_(1->infinity) <= C_S(t^-3+L^-6), t>0.             (3.2)

Here and below these norms use counting measure when S=1/2. We give the finite-graph details that permit use of (3.2) uniformly in L.

On the full six-dimensional discrete torus, Fourier splitting proves the finite-volume Nash inequality

    ||f||_2^(8/3)
       <= C [sum_edges |f(z)-f(z')|^2+L^-2||f||_2^2]
                ||f||_1^(2/3).                              (3.3)

For completeness, split Fourier modes at radius r, with L^-1<=r<=1. The low-frequency contribution to u=||f||_2^2 is at most C r^6 v^2, where v=||f||_1; the remaining contribution is at most C r^-2 times the edge energy, since the discrete Laplacian eigenvalues are bounded below by a constant times squared frequency. For nonzero f choose r=(u/(2C v^2))^(1/6), increasing the fixed C so that r<=1 because u<=v^2. If r>=L^-1, the low modes consume at most u/2 and rearranging the high-mode bound gives u^(4/3)<=C energy(f) v^(2/3). If r<L^-1, then u^(1/3)<=C L^-2 v^(2/3), so the L^-2 term in (3.3) proves it directly. For S>=1 the measures and conductances in (2.5) are between fixed positive constants and 1, so (3.3) transfers immediately.

For S=1/2 let Omega be the ordered-pair graph with the diagonal removed. Extend f from Omega to the full torus by retaining f off the diagonal and defining F(x,x) to be the average over the twelve neighbors

    A_e=(x,x+e), B_e=(x+e,x), e in {+/-e_1,+/-e_2,+/-e_3}.

Then ||F||_1<=C||f||_1, ||F||_2>=||f||_2, and ||F||_2^2<=C||f||_2^2. Each off-diagonal vertex enters at most two such averages. Moreover,

    energy(F) <= C energy_Omega(f).                           (3.4)

To verify the last assertion, every edge newly added is incident to a removed diagonal vertex. The sum of its squared differences from the neighbor average is bounded by a constant times the sum of squared pairwise differences among these twelve neighbors. These differences can all be paid by uniformly short paths in Omega. If e and f are distinct and f!=-e, A_e connects to A_f by moving its second coordinate along e,e+f,f. Opposite unit vectors connect by using an intermediate perpendicular unit vector. For a perpendicular unit vector q, A_e connects to B_e by

    (x,x+e), (x+q,x+e), (x+q,x), (x+q+e,x), (x+e,x).

All displayed pairs have distinct coordinates, including for L=4. These paths and their concatenations have bounded length and stay a bounded distance from (x,x). Translations of the finitely many patterns have bounded edge congestion, independently of L. Cauchy–Schwarz along the paths proves (3.4). Applying (3.3) to F transfers (3.3) to Omega.

Here is the standard semigroup step explicitly. Positivity and conservation make P_t an L^1 contraction. If ||f||_1=1 and u(t)=||P_t f||_2^2, the Nash inequality and u'=-2 energy(P_t f) imply

    u' <= -c u^(4/3)+C L^-2 u.

Multiplying by exp(-CL^-2 t) and integrating gives u(t)<=C t^-3 for 0<t<=L^2. Self-adjointness and the semigroup identity yield the 1->infinity estimate C t^-3 on that interval. For t>=L^2, compose with P_(L^2) and use L^1 contractivity to obtain C L^-6. This proves (3.2).

From (2.6), positivity gives

    sigma <= exp(2Et/S) P_t sigma.                            (3.5)

Indeed the derivative of exp(2Et/S)P_t sigma is nonnegative pointwise. Choose t=min{L^2,S/(2E)}, with t=L^2 if E=0. Then (3.2) and (3.5) give

    ||sigma||_infinity <= C_S(E+L^-2)^3 ||sigma||_(1,w).

The weighted norm equals sum rho=n(n-1); and rho=w sigma<=sigma. This proves (3.1). The n=0,1 cases follow directly because rho=0.

## 4. Uniform Gaussian sums and scales

Set

    M=L^3 beta^-3/2, ell=log beta, lambda_0=beta^-1/20,
    h=lambda/L^2, lambda_0<=lambda<=B, B fixed positive,
    T_h=T+hN,
    F(h)=Tr_Fock exp(-beta T_h),
    F_exc(h)=product_{k!=0}(1-exp[-beta(epsilon(k)+h)])^-1.

Thus F(h)=(1-exp(-beta h))^-1 F_exc(h). The following estimates are uniform for the stated interval:

    r:=E_free n_x <= C[beta^-3/2+(beta h V)^-1],               (4.1)
    A_1:=E_free(beta T_h) <= C(M+1),                          (4.2)
    A_2:=sum_k beta(epsilon(k)+h)m_k(1+m_k)
                    <= C[M+(beta h)^-1],                    (4.3)
    mu <= C M,                                              (4.4)

where m_k=(exp[beta(epsilon(k)+h)]-1)^-1 and E_free denotes its normalized Gaussian state. Translation invariance makes r independent of x.

Here are sufficient elementary sum bounds. For representatives k!=0,

    c_S |k|^2/L^2 <= epsilon(k) <= C_S |k|^2/L^2.

For t>0 the nonzero Gaussian sum obeys

    sum_{k!=0} exp(-ct|k|^2) <= C t^-3/2.

For 0<t<=1 this follows by enclosing unit cubes and radial integration; for t>=1 extract exp(-ct/2) and bound the remaining sum at t/2, which is stronger. Expanding (exp u-1)^-1 as sum_{j>=1}exp(-ju) therefore proves (4.4), since sum j^-3/2<infinity. Dividing by V and adding the zero mode proves (4.1). For u>0, u/(exp u-1)<=C exp(-u/2), giving (4.2) from the same Gaussian sum, with the zero-mode contribution at most 1. Also u exp u/(exp u-1)^2 <= C/(exp(u/2)-1), giving (4.3) for nonzero modes from (4.4) at beta/2; its zero mode is bounded by C/(beta h). These arguments also cover bounded B because beta h->0 uniformly.

Useful deliberately loose consequences of (1.1) are

    beta^.003 <= M <= beta^.03,
    r <= C beta^-1.451,
    V r^2 <= C beta^-1.372,
    beta V r^2 <= C beta^-.372,
    (beta h)^-1 <= beta^.07.                                 (4.5)

For example (beta h V)^-1=(beta lambda L)^-1<=beta^-1.451. Fixed logarithmic factors do not affect any strict negative powers below.

## 5. Absolute, uniform partition comparison

The main analytic assertion is

    sup_{lambda_0<=lambda<=B}
          |log Z(h)-log F(h)| -> 0,
    Z(h)=Tr_spin exp[-beta(H+hN)].                            (5.1)

### Upper bound on Z

Choose once a sufficiently large constant A depending on S and put

    E_0=A L^3 beta^-5/2 ell^(5/2)=A M beta^-1 ell^(5/2).

Since H,N commute and N>=0, (2.4) implies, uniformly in h>=0,

    Tr 1_{H+hN>E_0} exp[-beta(H+hN)]
      <= exp(-beta E_0/2) Tr exp[-(beta/2)H]
      <= exp[-c M ell^(5/2)] =: delta_beta ->0.               (5.2)

Increase A to obtain the positive constant c. The same bound holds with H alone in both places. In particular delta_beta is smaller than every fixed inverse power of beta eventually.

Let Q=1_{H+hN<=E_0}. Choose a simultaneous eigenbasis of H,N on its range. Every basis vector has E<=E_0 and n<=E_0/h. By (2.1) and (3.1),

    <K> <= C V(E_0+L^-2)^3(E_0/h)^2.

Since E_0 L^2>=A beta^.005 ell^(5/2), E_0+L^-2<=2E_0 eventually. Therefore

    beta <K> <= C beta V E_0^5 h^-2
      = C L^22 beta^-23/2 lambda^-2 ell^(25/2)
      <= C beta^-.18 ell^(25/2)=:eta_beta ->0.                (5.3)

The same bound holds for the Q-restricted Gibbs average. Peierls–Bogoliubov, on range Q, gives

    Tr_Q exp[-beta Q(H+hN)Q]
       <= Tr_Q exp[-beta Q(P_S T P_S+hN)Q] exp(eta_beta)
       <= F(h) exp(eta_beta).                                (5.4)

The second inequality follows from the Gibbs variational principle: density matrices supported in range Q are a subset of all Fock-space density matrices, and their energy for the compressed operator is their energy for T_h. This avoids any commutation assumption between Q and T. Adding (5.2), using F(h)>=1, proves log Z(h)<=log F(h)+o(1) uniformly.

### Lower bound on Z

Let q=E_free P and use the physical trial density matrix

    Gamma=P exp(-beta T_h)P/(qF(h)).

Wick's rule and 1-P<=(1/2)sum_x n_x(n_x-1) yield

    q>=1-Vr^2=1-o(1).                                       (5.5)

For distinct x,y, Wick's rule and Cauchy–Schwarz give E_free n_xn_y<=2r^2. Hence (2.2) gives

    beta Tr Gamma(H+hN) <= A_1/q + C_S beta V r^2/q.          (5.6)

For the entropy, the nonzero spectra of P exp(-beta T_h)P and exp(-beta T_h/2)P exp(-beta T_h/2) agree. The latter operator is bounded above by exp(-beta T_h). Operator monotonicity of log, with regularization if necessary at zero, gives the CGS entropy inequality

    Tr Gamma log Gamma
       <= -log(qF(h)) - A_1/q
                    + beta E_free[T_h(1-P)]/q.               (5.7)

Although T_h and P need not commute, the trace inequality used here is valid; it is precisely the spectral interchange and logarithm argument of CGS (4.21)–(4.23).

The last expectation is bounded by

    beta E_free[T_h(1-P)] <= V r^2 A_1+2r A_2.               (5.8)

To check this without a commutation shortcut, multiply the diagonal inequality 1-P<=(1/2)sum n_x(n_x-1) inside the trace by the positive operator T_h exp(-beta T_h). At fixed h and L,

    E_free[n_x(n_x-1)]=2r^2,
    -d_beta r=(1/V)sum_k(epsilon(k)+h)m_k(1+m_k),
    E_free[T_h B]=E_free[T_h]E_free[B]-d_beta E_free[B]

for B=n_x(n_x-1). Summing the resulting identity proves (5.8). Differentiation holds with h fixed; its later chosen beta dependence does not alter this identity at each parameter value.

Equations (4.2)–(4.5) show that beta V r^2, V r^2 A_1, and r A_2 all tend to zero uniformly; respectively one may bound them by

    C beta^-.372,
    C beta^-1.342,
    C beta^-1.381.

Applying the Gibbs variational principle to Gamma in (5.6)–(5.8) yields

    log Z(h)>=log F(h)+log q
                   -[C_S beta V r^2+V r^2 A_1+2rA_2]/q
             =log F(h)-o(1).

This completes (5.1). It is an absolute logarithmic estimate: no volume normalization has been taken.

## 6. Exact cancellation of the zero mode

The finite-dimensional SU(2) decomposition permits H to be diagonalized on each multiplicity space. Index a basis of those multiplicity spaces by i, and denote its energy, spin and deficit by E_i,J_i,D_i=SV-J_i. Each i has exactly 2J_i+1 magnetic states. Define the highest-weight trace

    Q(h)=sum_i exp(-beta E_i-beta h D_i).                     (6.1)

This is a scalar partition sum; it is not the spectral projection Q of §5. The all-aligned multiplet supplies Q(h)>=1. Since N takes the consecutive values D_i,D_i+1,...,D_i+2J_i on that multiplet, its exact character gives

    (1-e^-beta h) Z(h)=Q(h)-R(h),
    R(h)=sum_i e^-beta E_i-beta hD_i e^-beta h(2J_i+1).        (6.2)

We must bound R rather than discard it. On E_i<=E_0, (2.3) gives

    D_i<=D_0=C_S L^2 E_0.                                   (6.3)

Uniformly D_0/(SV)->0, since L^2 E_0/V=C L^2 beta^-5/2 ell^(5/2). In particular J_i>=SV/2 eventually. For h>=h_0=lambda_0/L^2,

    beta h(2J_i+1)>=c_S beta lambda_0 L>=c_S beta^1.451.

Consequently the low-energy part of R is at most exp(-c_S beta^1.451)Q(h). The high-energy part is at most

    sum_{i:E_i>E_0} e^-beta E_i
       <=Tr_spin 1_{H>E_0}e^-beta H <=delta_beta.              (6.4)

Here the omitted multiplicities are >=1, so the inequality has the required direction. Since Q(h)>=1, (6.2) implies

    Q(h)=(1-e^-beta h)Z(h)[1+o(1)]
         =F_exc(h)[1+o(1)]                                  (6.5)

uniformly for lambda_0<=lambda<=B, using (5.1). This is a relative comparison and does not leave a polynomial prefactor.

We next identify Q(0). On E_i<=E_0,

    0<=beta h_0 D_i<=C lambda_0 beta E_0
      <=C beta^-.02 ell^(5/2) ->0.                           (6.6)

The high-energy part is bounded by (6.4). Since Q(0)>=1 and Q(h_0)<=Q(0), it follows that Q(h_0)/Q(0)->1. For the free modes,

    0<=log F_exc(0)-log F_exc(h_0)
      =integral_0^(beta h_0) sum_{k!=0}(e^(beta epsilon(k)+u)-1)^-1 du
      <=beta h_0 mu
      <=C lambda_0 L beta^-1/2 <=C beta^-.04 ->0.             (6.7)

Combining (6.5)–(6.7) proves

    Q(0)/F_exc(0)->1.                                       (6.8)

Finally restore physical multiplicities. Write B(h)=sum_i(2J_i+1)exp(-beta E_i-beta hD_i), so B(0)=Z(0). On the low-energy set,

    (2J_i+1)/(2SV+1)=1-2D_i/(2SV+1)=1+o(1)

uniformly. On its complement both Q(h) and B(h)/(2SV+1) are bounded by delta_beta for h>=0. Since Q(h)>=1, for all h>=0 we have the relative comparison

    B(h)/[(2SV+1)Q(h)]=1+o(1).                               (6.9)

The error is uniform in h>=0. This relative statement is needed: total-variation proximity by itself would not justify the unbounded centered Laplace transforms.

For each fixed lambda>0, h=lambda/L^2 lies in the interval of (6.5) eventually. Equations (6.5), (6.8) and (6.9) give

    E_phys exp[-lambda a(D-mu)]
      =e^(lambda a mu) B(h)/B(0)
      =[1+o(1)] e^(lambda a mu) F_exc(h)/F_exc(0).             (6.10)

All o(1) factors in this expression are relative. The case lambda=0 is exactly 1. This step removes both the magnetic multiplicity and the free boson zero mode before taking the fluctuation limit.

## 7. The ideal limit and weak convergence

Under the product measure with independent geometric occupation numbers G_k of parameter exp(-beta epsilon(k)), k!=0, the last expression of (6.10) is the Laplace transform of a sum_k(G_k-E G_k). We record the CD calculation with changing finite eigenvalues.

Put c_L(k)=L^2 epsilon(k). For each fixed nonzero integer k, c_L(k)->c_k=4pi^2S|k|^2, while uniformly c_L(k)>=c_S|k|^2. Also a=beta/L^2->0 by the lower endpoint of (1.1). A single centered mode contributes the log transform

    f_(a,c)(lambda)
       =lambda a/(e^(ac)-1)+log(1-e^-ac)
                            -log(1-e^-a(c+lambda)).          (7.1)

It has f(0)=f'(0)=0 and, for lambda>=0,

    0<=f''(lambda)=a^2 e^(a(c+lambda))/(e^(a(c+lambda))-1)^2
                  <=1/(c+lambda)^2<=1/c^2.                 (7.2)

The inequality follows from 2sinh(u/2)>=u. Thus 0<=f(lambda)<=lambda^2/(2c^2). Its pointwise limit is lambda/c-log(1+lambda/c). Extend the finite summands by zero outside their mode cube. Since sum_{k!=0}|k|^-4<infinity in dimension three, dominated convergence gives

    log[e^(lambda a mu)F_exc(lambda/L^2)/F_exc(0)]
      ->sum_{k!=0}[lambda/c_k-log(1+lambda/c_k)].              (7.3)

The centered independent exponential series in (1.2) converges in L^2 because its variances sum to sum c_k^-2<infinity. It also has the asserted Laplace transform. For example its finite partial products are uniformly bounded at 2lambda by (7.2) with the limiting summands, so exp(-lambda times the partial sum) is uniformly integrable. L^2 convergence, a subsequence argument, and this uniform integrability identify its expectation with the product. This proves (1.3) using (6.10).

For clarity, one-sided Laplace convergence here also implies the stated weak convergence even though the lower bounds on the centered variables drift. The following argument avoids an unstated nonnegative-variable assumption. Let P_n denote their laws and phi_n(lambda) their Laplace transforms; by what was proved, phi_n(lambda)->phi(lambda)=E exp(-lambda W_S) for every lambda>=0. Tilt at lambda=1:

    dnu_n(y)=e^-y dP_n(y)/phi_n(1),
    dnu(y)=e^-y dLaw(W_S)(y)/phi(1).

Their moment generating functions for |t|<1/2 are phi_n(1-t)/phi_n(1), converging to that of nu. The usual moment-generating-function continuity theorem implies nu_n=>nu. One may prove that theorem directly here by uniform exponential tail bounds from t=+/-1/2, subsequential tightness, and uniqueness of the mgf on an interval. Moreover

    integral e^y dnu_n=1/phi_n(1)->1/phi(1)=integral e^y dnu.

Together with weak convergence, convergence of these nonnegative continuous-function integrals implies uniform integrability of e^y: first use min(e^y,R), then take R->infinity, and use e^y 1_{e^y>2R}<=2(e^y-R)_+. Truncation now yields, for every bounded continuous g,

    integral g dP_n=phi_n(1)integral g(y)e^y dnu_n(y)
         ->phi(1)integral g(y)e^y dnu(y)=E g(W_S).

This proves (1.2).

Finally Var(W_S)=sum c_k^-2>0. Its log mgf is analytic near zero, since for |t|<min_k c_k/2 the centered summands and their first three derivatives are bounded by summable multiples of c_k^-2 or c_k^-3. Its third cumulant is 2sum c_k^-3>0, so W_S is not Gaussian. This completes RF in all its frozen quantifiers.

## 8. Scope, validation and limits

The argument treats every fixed half-integer spin, every even sequence in (1.1), the physical zero-field radial observable, the specified finite-volume centering, weak convergence, and every nonnegative Laplace parameter. It does not infer actual-mean convergence from Laplace convergence and does not claim the fixed-temperature limit. The small field is an auxiliary step, not a replacement target.

The bound in §3 is proved on the periodic pair graph and explicitly includes zero-energy descendants. The projection in §5 is the spectral projection of H+hN; this prevents uncontrolled large magnetic particle numbers. Section 6 instead uses the H-only cutoff and the Casimir deficit, which are the quantities needed for the exact character and highest-weight normalization. These distinct roles are essential.

Validation at author stage consists of algebraic checks against the full indicated CGS proof bodies, explicit finite-graph paths, and uniform exponent accounting. No numerical experiment or source's pressure theorem is being used as a substitute for a proof. Independent proof review and contribution review are still required. The proof's classical dependencies and the ideal-limit antecedent must remain in any public version.

Primary URLs: https://arxiv.org/abs/1312.7873v2 ; https://arxiv.org/abs/1306.3625v2 . Private downloaded PDFs are verification inputs and are not licensed as original prose or proposed for redistribution with a public artifact.
