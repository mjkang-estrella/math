# Independent full-proof review O217, round 1

**Verdict: PASS_FULL_O217.** The complete unchanged frozen scope is proved by the submitted argument, conditional only on the stipulated pinned Gaussian source for its limiting-law consequence. No mathematical correction or narrower replacement is required. This verdict concerns proof, not substantiality, eligibility, formalization, publication or campaign count.

Reviewed author manifest: `1d299a1840795fe279f89aa04fd4ca55cb58d283b3f7ed2fb5001c136d97d48f`.
Candidate: `a2aca38071a48fba5cccad7df731626202c6a8ca778ade57f76759c1d321cf37`.
Frozen scope: `78fc15d24a91bbc2a8e27f679b78c4e551ef0c25d84214dd5dcc48e14ee99584`.

The reviewer authored none of O217's candidate, variance note or implementation. The parent's variance note and preliminary reading are author-side assistance, not independent evidence. No live contribution draft was read. The author package was authenticated with its externally supplied anchor; all111 payloads,58 pinned source blobs,8 primary PDF extraction replays and18 input snapshots passed. A wrong external anchor was rejected. Those checks establish identity, not this proof verdict.

## 1. Exact target and constants

For every fixed beta>0 and K>=1, every n>=2, and every independent, centered, variance-one real edge family with fourth absolute moments at most K, the submitted proof gives all three finite-size comparisons: an absolute O_(beta,K)(1) mean difference, variance difference O_(beta,K)(1+sqrt(V_G)), and the stated C6 smooth-test difference bounded by C_(beta,K) a^(-1) times the sum of six derivative norms for all a>=1 and every real c. Edges may have different laws. Neither symmetry nor vanishing third moments is introduced.

For beta>1 it additionally gives the source's exact positive n^(1/3) variance prefactor and the source's standardized weak limit using the non-Gaussian model's own mean and variance, along every triangular array with one finite uniform K. Positivity is only eventual. The proof does not transfer all moments or exponential integrability. All constants can be chosen uniformly in n, individual laws, a,c and the test. Their possible dependence on beta is essential and permitted.

## 2. Mixed derivatives, test composition and integrability

For k labeled edge occurrences, differentiation of the finite Gibbs sum gives q^k times their joint cumulant, q=beta/sqrt(n). The partition formula bounds the cumulant by the finite sum of (number of blocks minus one) factorial. It does not require distinct spin variables or distinct edge indices, so repeated derivatives, in particular e,e,e,f,f,f, are covered. No disorder differentiation under an infinite integral is used here.

The partition form of the multivariate chain rule for phi((F-c)/a) gives a product of F derivatives whose total order is k, multiplied by a^(-r)phi^(r). For 1<=k<=6 and a>=1, every a^(-r)<=a^(-1). Thus the common bound C_k q^k a^(-1) A_phi is valid and independent of c; A_phi contains derivative orders1–6 only. Bounded phi itself supplies integrability, but need not occur on the right-hand side.

The coordinate Lipschitz constant is q, since the first Gibbs derivative is q times a spin product mean. The crude bound |F(x)|<=n log2+q sum_e|x_e| ensures finite first and second moments for every finite array in the proof. It therefore establishes finiteness of the hybrid maximum before the bootstrap. Large but finite growth in n in this crude bound is harmless: it is used only for existence, not as the final estimate.

## 3. Gauge sign and inner replacement

Negating vertex i in the spin sum negates precisely its incident edge coordinates, proving the deterministic identity U(T_i x)=U(x) for every observable U=Psi(F). Three differentiations with respect to e={i,j} give (D_e^3 U)(T_i x)=-(D_e^3 U)(x). At x_e=0 this is oddness under the other n-2 star edges, with all exterior coordinates fixed. It is not the claim that an asymmetric product law is invariant under that reflection.

Reflect the star coordinate laws one at a time. Each intermediate law remains a product law; no common random gauge is inserted. At a currently replaced f, the deleted-edge cubic derivative has third f-derivative D_f^3D_e^3U bounded by Cq^6L. Taylor expansion through degree2 and matching first two moments cancel the polynomial terms. The remainder uses only E|x_f|^3, bounded by K_0^(3/4), where K_0=max(K,3). The two endpoint expectations are opposites by the deterministic sign identity, hence their difference is twice the original expectation. This proves |E D_e^3U|<=C(n-2)q^6L, and the weaker displayed Cnq^6L. At n=2 the empty-star sign identity directly forces the derivative to be zero.

The entire star comparison can be done with exterior variables fixed and then averaged for bounded derivatives. At no stage is a nonproduct conditional disorder law used.

## 4. Outer comparison and exact powers

At a replaced edge e the degree3 Taylor polynomial has cubic coefficient D_e^3U/6, evaluated at the deleted edge. The other coordinates are independent of either replacing variable. This independence allows the third moment difference to multiply the expectation of that coefficient. The fourth remainder is uniformly Cq^4L|x_e|^4. Thus one edge costs C L(q^4+nq^6).

With m=n(n-1)/2,

    m q^4 = beta^4 (n-1)/(2n) <= beta^4/2,
    m n q^6 = beta^6 (n-1)/(2n) <= beta^6/2.

No factor in either comparison grows with n. Applied to F, this proves the mean bound uniformly over every reflected/Gaussian hybrid, not just the original disorder. Applied to the composed test it proves the full a,c,phi statement. Sixth derivative order is unrelated to a sixth random-variable moment; the inner and outer Taylor variables are distinct independent coordinates.

## 5. Finite hybrid maximum and deleted-edge restoration

The class H has at most3^m product laws, choosing separately for each edge its original law, its reflected law, or Gaussian law. It is closed under every reflection and replacement used. Define M as the maximum of E(F-c_G)^2 over these actual nondeleted laws. M is finite by Section2 above; no variance estimate for a hybrid is assumed.

For an array with one or two prescribed zero coordinates, independently restore those coordinates with compatible laws. Its restored law belongs to H. Lipschitz continuity, Cauchy–Schwarz, and E|x_e|<=1 then give

    E|F_deleted-c_G| <= sqrt(M)+r q,  r<=2.

The estimate is unconditional. Crucially, each deleted base value is independent of the currently Taylor-expanded variable. This is sufficient for factoring E(|H_0||z|^k), and the proof never upgrades the bound to a false uniform conditional assertion. The cardinality3^m does not enter any union bound or constant; only a finite maximum is taken.

## 6. Fourth-moment square remainder

Writing H(z)=H_0+u(z), b_j=u^(j)(0), independently expanding the submitted algebra gives exactly

    u^2-b_1^2 z^2-b_1 b_2 z^3
      =2 b_1 z(u-b_1z-b_2z^2/2)+(u-b_1z)^2.

The first bracket is O(q^3|z|^3), the second O(q^2|z|^2), and |b_1|<=q. Both terms on the right are therefore O(q^4|z|^4). Combined with the degree3 expansion of u, this gives the degree3 expansion of H^2 with remainder bounded by Cq^4|z|^4(|H_0|+1).

H_0 is independent of z. The one-deletion restoration estimate therefore bounds the expected remainder by Cq^4K_0(sqrt(M)+q+1). There is no |z|^5 term. Polynomial terms are integrable too: H_0^2 has finite expectation, and each remaining coefficient grows at most linearly in |H_0| while the corresponding moment of z is of order at most3. Conditional cancellations and their subsequent averaging are justified.

## 7. Unbounded cubic square coefficient

Let H=F-c_G and B=D_e^3(H^2)|_(x_e=0). Gauge oddness still applies. For distinct star edge f, the full product formula before restriction is

    D_e^3 D_f^3(H^2)
      = sum_(a,b=0)^3 binom(3,a)binom(3,b)
          (D_e^a D_f^b H)(D_e^(3-a)D_f^(3-b) H).

Only (a,b)=(0,0) and (3,3) retain an undifferentiated H. Together they contribute2H D_e^3D_f^3F. Every other term has positive-order derivatives in both factors, totaling six. The cumulant bounds thus yield Cq^6(|H|+1), including all repeated-edge occurrences.

Along z=x_f with e deleted, |H(z)|<=|H(0)|+q|z|. The order2 integral Taylor remainder for B is consequently bounded by

    Cq^6[(|H(0)|+1)|z|^3+q|z|^4].

Here H(0) has precisely two deleted coordinates. Independence and restoration give an expected bound C_(beta,K)q^6(sqrt(M)+1), since q<=beta/sqrt(2). Replacing the n-2 star coordinates and applying the sign identity gives the asserted bound on EB. The fourth moment pays the last term; no fifth/sixth moment or exponential tail assumption is hidden. Coefficients of the canceled quadratic polynomial have integrable linear growth in the deleted H(0), so the cancellation itself is legitimate.

## 8. Noncircular bootstrap and centering

Outer square replacement uses the preceding cubic bound and the separate fourth remainder. Summing gives, for every P in H,

    |E_P(F-c_G)^2-V_G| <= C(sqrt(M)+1).

Take the maximum to obtain M<=V_G+C sqrt(M)+C. With y=sqrt(M)>=0, the positive root bounds y by C/2+sqrt(V_G+C+C^2/4)<=sqrt(V_G)+C_1. The maximum was already finite; this is an algebraic inequality, not an iteration assuming the conclusion.

Substitution bounds every hybrid square comparison by C_2(1+sqrt(V_G)). The exact variance identity subtracts (E_PF-c_G)^2, bounded uniformly by the separately proved mean comparison. This proves the variance statement at full scope.

## 9. Gaussian source and full-sequence transfer

The actual pinned limiting-law introduction defines F=log sum_sigma exp[(beta/sqrt(n))sum_(i<j)g_ij sigma_i sigma_j], with counting prior and no field. Its `thm:main` gives exact finite-size standardization, through all integers, at each fixed beta>1. Its `thm:moments` gives the positive a_2 prefactor for the completed pressure; its completion has independent variance beta^2/2. Subtracting that constant variance and removing deterministic n log2 give exactly Var(F_G)/n^(1/3)->a_2>0 for the uncompleted F used here. The relevant `red:prop-moments` ending was checked directly. The scale companion alone gives only n^(1/3+o(1)); it is not substituted for the stronger source theorem.

Therefore V_G diverges. The variance comparison gives Var(F_J)/V_G->1 uniformly over the allowed array laws and implies eventual positivity. Set a=sqrt(V_G), c=c_G in the smooth comparison; a>=1 eventually. For each fixed t, cos(tx) and sin(tx) satisfy all test hypotheses. Their comparison errors tend to zero, so Lévy's continuity theorem gives the Gaussian-defined weak limit under Gaussian centering/scaling. The mean comparison shifts the center by o(sqrt(V_G)); the variance ratio corrects the scale by1+o(1). Slutsky proves the requested own-mean/own-variance law. No coupling across n is used.

## 10. Adversarial boundaries and disposition

At n=2, symmetric two-point disorder can give zero variance, but the finite comparisons remain valid and no finite-n standardization is claimed. Nonidentical laws and arbitrary edgewise signs of third moments do not affect any constant. Fixed beta>0, not low temperature, suffices for the finite comparisons. Low temperature and fixed beta>1 are used only for the stipulated divergent Gaussian variance and law.

As a heavy-tail audit, take Z with Pareto tail P(Z>t)=t^(-9/2) for t>=1 and standardize Z-EZ. Its fourth moment is finite, its fifth absolute moment infinite, and its third centered moment is positive (E(Z-EZ)^3=528/1715). Every expectation required above remains finite for this asymmetric example. This is an analytic integrability check, not a numerical universality test.

Required repairs: none. For later exposition, it is useful to retain the explicit mixed product formula in Section7 and the distinction between unconditional restoration and conditional moment cancellation. These clarify already valid steps and impose no new hypothesis. The independent contribution gate must judge the operation relative to classical replacement and gauge symmetry; this proof verdict does not decide that question.

Original review prose: CC BY4.0; original verification code: MIT. Author attribution follows the project convention Myeongjin Kang, no affiliation. Third-party retained inputs remain private and are not relicensed. Exact reading limits and dependency hashes accompany this report.
