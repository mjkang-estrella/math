# Strongest reduction, attempted quantitative bridge, and decision

PREFREEZE only. Nothing below is a frozen author theorem. All source proofs are stipulated true; the analysis concerns new quantitative conclusions and their exact applicability.

## 1. What integrality actually adds

Retain B_1=Delta_1/L and probability measure mu from note02. Suppose first Gamma is residually finite. Choose a residual normal tower solely to analyze the FIXED universal spectral measure. Let mu_i be the normalized eigenvalue measure of B_1 on its d_i-sheeted cover, total mass one, and let z_i=mu_i({0}). Polynomial traces converge, hence these measures converge weakly. Lueck's integer argument and approximation, with source vanishing, give z_i->0.

Delta_1,i is an integral positive semidefinite matrix. The product of its NONZERO eigenvalues is the absolute value of the first nonzero coefficient of its monic integral characteristic polynomial, and is therefore at least one (the empty product is one). In the probability normalization this implies

  integral_(0,1] log x dmu_i(x) >= -(1-z_i)log L >= -log L.

For 0<epsilon<1, the continuous function f_epsilon(x)=log(max(x,epsilon)) obeys

  integral f_epsilon dmu_i >= -log L + z_i log epsilon.

Take i->infinity at FIXED epsilon. Weak convergence and z_i->0 imply integral f_epsilon dmu >= -log L. Then let epsilon decrease to zero. Monotone convergence applied to -f_epsilon proves

  integral_(0,1] |log x| dmu(x) <= log L.                        (10)

This proves integrability of the single limiting measure. It does NOT prove uniform integrability of the finite measures, nor convergence of finite logarithmic determinants or torsion. The source has no such consequence; Lueck2016 Section17.4 explicitly distinguishes the uniform log-power>1 condition from the insufficient uniform 1/|log x| bound.

From (10), for 0<z<1,

  mu([0,z]) <= [integral_(0,z] |log x| dmu(x)]/|log z|,

and the numerator tends to zero. Hence mu([0,z])=o(1/|log z|). The k=1 filter of note02, split at x=1/m, gives

  integral A_m dmu <= mu([0,1/m])+1/m = o(1/log m).               (11)

For any cover, not necessarily normal, equations(1)--(3) consequently give

  E_H <= 2c [mu([0,1/m])+1/m+beta_H((m-1)R)].                   (12)

For normal covers, choose m=floor((short(H)-1)/R)+1, when m>=2. The beta term vanishes. As short(H)->infinity, the corrected middle defect and b1/d,b3/d are o(1/log short(H)). The little-o modulus depends on Q and its fixed matrices; it is not a computable universal numerical constant or a new substantial claim. It is a direct refinement of the determinant-class and polynomial operations already read. The explicit finite bound mu([0,z])<=log L/|log z| also recovers the older logarithmic estimate.

If Gamma is not residually finite, its nontrivial finite residual contains an element lying in EVERY finite-index subgroup. (It lies in every normal core, hence in each subgroup.) That element fixes every coset in every finite cover. Thus beta_H(t)=1 once t reaches its word length; arbitrarily deep normal covers do not exist. This is a statement about the local-unrolling parameter, not a reduction of the source's full scope to residually finite groups. Equations(1)--(9) still hold for every source Q and every finite cover. A Farber sequence would itself force residual finiteness by detecting each nonidentity group element in a finite permutation quotient.

## 2. Degree alone cannot replace local unrolling

Let Q=Sigma_g x Sigma_h, g,h>=2, a source-scope closed oriented aspherical four-manifold. Take a d-sheeted connected cover only in the first factor. Its genus is g_d=1+d(g-1), and

  b1(Q_d)=b3(Q_d)=2g_d+2h,
  b2(Q_d)=2+4g_d h,
  chi(Q)=4(g-1)(h-1).

Therefore b1(Q_d)/d tends to 2(g-1)>0, and

  b2(Q_d)/d-chi(Q) -> 4(g-1)>0.

This is compatible with source b1^(2)=0, because the second factor never unrolls: fixed nonidentity elements in it stabilize every coset. This concrete example prevents an unqualified index-only power/sublinear conclusion over ALL finite covers. It does not refute a residual-tower result or a local-radius result. The source already preserves the necessary trivial-intersection hypothesis in its normal-tower corollary.

## 3. Attempt to obtain a power estimate from the OPERATIVE boundary proof

The attempted full-scope quantitative question is: for each Q in the entire source class, can one obtain constants a_Q>0,C_Q<infinity and a fully specified radius-dependent power bound on the corrected defect for every sufficiently deep finite cover, with beta_H retained for nonnormal covers? Note02 closes the transfer once a suitable small-spectrum estimate is actually proved. It does not prove that estimate.

For a vector u in the spectral subspace E_(Delta_1)([0,lambda]),

  ||D_1u||^2+||D_2^*u||^2 <= lambda ||u||^2.

In the cochain convention, this says the edge vector is nearly coclosed and nearly closed. Source found:gradient begins instead with an EXACT closed cochain: D=ker d_1, and positivity of the REDUCED quotient D/closure(im d_0). That positive quotient provides a nonzero Riesz minimizer outside D_0. Source compact:potential then uses scalar truncation and exact integration along every relator to obtain connected level sides. A low-eigenvalue vector need not be an exact gradient on the Cayley two-complex. Correcting its small curl with a uniformly bounded or polynomially controlled inverse of d_1 is precisely additional filling/spectral information; exact H^1 vanishing does not bound that inverse.

The new finite-propagation homotopy in note02 makes this loss explicit rather than merely naming it. It produces an approximate inverse with propagation O(kmR) and norm O(km^2), and residual P(B_1). Source vanishing makes that residual tend strongly to zero. Its trace is still integral P dmu, the very quantity that requires a rate. Iterating the homotopy does not remove the dependence on mu. In particular, the bound ||P(B_1)||<=1 is not a strict contraction bound when positive spectrum accumulates at zero.

Further source operations remain qualitative at this interface:

* compact:good-boxes selects almost-everywhere regular levels from integrability; it does not quantify the size of the chosen box or its number of components in terms of spectral mass near zero.
* dyn:length proves translated pairings of two l2 functions tend to zero by finite-support approximation. It gives a modulus for given functions if their tails are known, but those tails are not controlled from the size of a small spectral interval.
* pret:invariant-class is an ordinal/finite-generation argument, with no numerical bound on a metric depth or a finite quotient.
* push:majority proves that SOME M(A,Z,S) works for all sufficiently deep paths by a compactness contradiction. It does not bound M from the Laplacian or an eigenvalue. Hruska--Ruane's length bound uses proper hyperbolicity and cocompact geometric action, which are not assumptions on every Q or on the source's block graph.

Thus transplanting the hyperbolic primary length constants to the full source class is not justified. Nor can the contradiction boundary be treated as an unconditional boundary for Gamma: it was constructed under the false assumption b1^(2)>0. Its nonexistence is the mechanism of the stipulated proof.

## 4. Duality and determinant bounds alone do not supply the missing rate

Here is an explicit limited model of the reduced analytic interfaces. It is NOT a group-ring complex, NOT an aspherical Poincare complex, and NOT a counterexample to any possible full-scope theorem.

Let A=L-infinity((0,1),dt), with its usual finite trace, and let T be multiplication by exp(-1/(2 sqrt(t))). Form a Hilbert A-chain with ranks (1,2,2,2,1) and coordinates

  C0=(x), C1=(a,c), C2=(b,e), C3=(d,g), C4=(f),
  D1(a,c)=T a, D2(b,e)=(0,T b),
  D3(d,g)=(0,T d), D4(f)=(0,T f).

The boundary squares are zero. All Laplacians are multiplication by T^2 on every coordinate. T is injective with dense range, so every reduced homology group is zero. Pair each two-term summand with its reverse-dual summand: in the sign-free reverse-dual convention, J0=J4=identity and J1=J2=J3=the two-coordinate swap give explicit unitary chain isomorphisms. Conventional dual differential signs can be absorbed in the summand identifications. This asserts a reverse-dual chain isomorphism, not an integral symmetric Poincare structure. Nevertheless the probability spectral distribution is, for 0<x<=exp(-1),

  mu([0,x]) = 1/(log(1/x))^2,
  integral |log x| dmu = integral_0^1 t^(-1/2)dt = 2.

It obeys no bound C x^a for ANY a>0. Scaling all differentials by e makes integral log Delta equal zero and norm Delta at most e, so even a nonnegative logarithmic determinant is compatible with this slow tail. This model only shows why zero reduced homology, finite-chain duality and a determinant lower bound, considered as isolated analytic statements, cannot imply the desired power law. It says nothing about realizability by integral cellular matrices of a source Q. Closing or bypassing THAT extra structural interface remains necessary.

## 5. Exact unpaid operation and freeze decision

The most concrete attempted bridge is a full-scope bound

  tr_Gamma E_(Delta_1)([0,lambda]) <= A_Q lambda^(a_Q),
  a_Q>0, 0<lambda<=lambda_Q,

or, more weakly and more directly, a polynomial decay estimate for the traces of the admissible finite-propagation positive filters P_m(Delta_1/L). The displayed spectral bound is SUFFICIENT, not asserted necessary, for polynomial cover-kernel bounds. Clair--Whyte's abelian discussion itself warns that spectral invariants and actual kernel growth need not have equivalent exponents. A direct integrality/duality operation controlling finite-cover kernels could bypass this spectral route, but none is constructed here.

No such full-scope bridge has closed. The concrete local-coset trace calculation, sign-twisted orientation compatibility, exact corrected Euler identity, log-free conditional Fejer bound, and chain homotopy with explicit norm/propagation costs survive as feasibility work. They are all source/classical compositions and are not submitted as a substantial nominee, a parameter-renamed target, or a restricted substitute. No frozen theorem or AUTHOR-PROOF file is produced.

This is PREFREEZE / no nominee, not exhaustion and not a global impossibility theorem. All old full targets and supplied dispositions, including S176A, remain unchanged. There is no self-grade, acceptance or count claim. Parent alone integrates and adopts those decisions.
