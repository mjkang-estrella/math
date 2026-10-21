# Finite covers, positive filters, and a compatible chain homotopy

Prefreeze feasibility calculations only. No mathematical grade or substantial nominee is assigned. Q has the entire source scope in note01. These calculations are original explanatory derivations of source/classical compositions, not a claim to new literature.

## 1. Finite matrices and a local defect for EVERY finite cover

Choose the source's finite four-dimensional CW model F of Q. Fix lifts of its cells, a finite symmetric generating set of Gamma and the associated word length. Write C_j=l2(Gamma)^{c_j}, with cellular differential D_j:C_j -> C_(j-1). The matrices are over ZGamma. Let

  Delta_j = D_j^* D_j + D_(j+1) D_(j+1)^*.

Choose a common real L>1 bounding the operator norms of all Delta_j on the regular representation and on EVERY finite permutation representation, including their sign twists. Such an L is obtained from the finite coefficient sums of the D_j, so it requires neither residual finiteness nor an analytic conjecture. Put B_j=Delta_j/L. Let R>=1 bound the word lengths in every entry of every Delta_j, and put c=c_1. Let mu be the probability spectral measure c^(-1)tr_Gamma E_(B_1), supported on [0,1]. Source thm:main and found:comparison give mu({0})=0. If a cell count is zero its entire corresponding assertion is trivial; here c>0 since Gamma is infinite.

For H<=Gamma of finite index d, use right multiplication on H\Gamma, in the same right-matrix convention for all chains. Define

  beta_H(t) = d^(-1) #{Ha: some 1!=g in Gamma with |g|<=t fixes Ha}.

The condition is that a^(-1)Ha contains a nonidentity element of length <=t. Thus this definition is invariant under the conjugacy ambiguity in an unbased cover. It is a union-of-short-stabilizers statistic, not the maximum fixed-point proportion of one element. It is defined whether H is normal or not. Good cosets have no such short stabilizer.

Let P be a real polynomial of degree n, with P(0)=1 and 0<=P(x)<=1 on [0,1]. On a good coset for t=nR, the j-th diagonal entry of P(B_1,H) is EXACTLY the identity coefficient of the j-th diagonal group-ring entry of P(B_1). Every nonidentity word in that entry has length <=nR and moves the coset. On bad cosets each diagonal entry of the positive contraction P(B_1,H) lies in [0,1]. Therefore

  b1(Q_H;Q)/d <= c integral P dmu + c beta_H(nR).                 (1)

More explicitly, the trace on all good cosets is their number times tr_Gamma P(B_1), and the trace on all bad cosets is at most c times their number. Dividing by d gives (1), even the slightly sharper c[(1-beta)integral P dmu+beta]. The kernel contributes one for each harmonic vector because P(0)=1. Finite chain Hodge theory identifies that kernel with ordinary characteristic-zero homology. No claim for finite-field coefficients is made.

For normal H with short(H)>nR, beta=0, giving Clair--Whyte's exact moment identity. For a Farber sequence (the fixed-point proportion of each nonidentity element tends to zero), beta_H(t)->0 for every fixed t, since the word ball is finite. Only this local convergence, not index growth alone, permits the limiting inference.

## 2. Orientation and the corrected middle-dimensional defect

Apply the ring automorphism g -> w(g)g to every entry of Delta_1, obtaining Delta_1^w. On l2(Gamma), multiplication of the standard vector at g by w(g) is a unitary conjugacy between the two operators. Their spectral measures are equal and support lengths/coefficient norms are identical. On H\Gamma the twist is a signed permutation representation of Gamma, giving the local coefficient system Q^w on Q_H. Its norm obeys the same L bound. At a good coset the identity coefficient is still the entire diagonal trace: nonidentity short words contribute zero regardless of their signs. Thus the identical bound (1) holds for b1(Q_H;Q^w).

Finite-dimensional Poincare duality and duality of homology/cohomology over Q identify

  b3(Q_H;Q) = b1(Q_H;Q^w).

This does not assume that w|H is trivial. In the orientable case the twist is trivial and b3=b1. Put e_H=1 if w|H is trivial, and e_H=0 otherwise. Connectedness and top-dimensional twisted duality give b0=1 and b4=e_H. Euler characteristic of the finite cover gives the EXACT identity

  E_H := (b2(Q_H;Q)+1+e_H)/d - chi(Q)
       = (b1(Q_H;Q)+b3(Q_H;Q))/d >=0.                           (2)

Combining the two signed/unsigned traces proves

  E_H <= 2c [integral P dmu + beta_H(nR)].                       (3)

For the uncorrected middle defect, subtract (1+e_H)/d. In particular it need not be nonnegative. The same conclusions apply to all source TOP manifolds by lifting the finite homotopy equivalence to every cover. There is no restricted orientable/smooth replacement.

## 3. The strongest immediate spectral filtering payment

The actual Clair--Whyte construction gives, for 0<z<1,

  P_(n,z)(x) = [T_n((1+z-2x)/(1-z))+1]
               /[T_n((1+z)/(1-z))+1].

It obeys 0<=P<=1, P(0)=1, and P(x)<=4 exp(-2n sqrt(z)) for z<=x<=1. On [0,z] it decreases from one and stays nonnegative; on [z,1] use |T_n|<=1. Consequently

  integral P_(n,z) dmu <= mu([0,z])+4 exp(-2n sqrt(z)).            (4)

Equations(1)--(4) are compatible at the SAME n, z, word radius and finite cover; orientation does not require a different measure. This already extends the basic normal-cover calculation to the explicitly measured bad cosets without any coefficient explosion from monomial expansions.

As mu({0})=0, first taking n large with z fixed and then z small proves convergence for Farber covers. The source's absence of a kernel supplies no numerical function bounding mu([0,z]) as z decreases. A definition eta(n)=inf integral P dmu is a valid modulus but is not an explicit new bound.

## 4. A log-free endpoint filter under an ACTUAL power law

The Chebyshev split estimate loses log n at a fixed power-law spectral endpoint. One can remove this loss by integrating a classical positive trigonometric filter instead of cutting its spectrum into only two pieces. This elementary filter operation is retained, not nominated as a new substantial theorem.

For m>=2 and x=sin^2(theta/2), define

  A_m(x) = [sin(m theta/2)/(m sin(theta/2))]^2
         = [m+2 sum_(j=1)^(m-1)(m-j) T_j(1-2x)]/m^2,

with A_m(0)=1. It is a polynomial of degree m-1, independent of the choice of theta. The geometric sum of m unit complex numbers proves both positivity and the bound by one; bounding the numerator sine by one gives

  0<=A_m(x)<=min(1,1/(m^2 x)).

For an integer k>=1 put P=A_m^k, of degree n=k(m-1). Its integral satisfies

  integral P dmu <= integral min(1,(m^2 x)^(-k)) dmu.             (5)

If, and ONLY if, one has proved mu([0,x])<=C x^a for all 0<x<=1 with a>0, C>=1, then for any integer k>a, layer-cake integration gives

  integral P dmu
   <= integral_0^1 mu([0,m^(-2)t^(-1/k)]) dt
   <= C m^(-2a) integral_0^1 t^(-a/k) dt
    = C k/(k-a) m^(-2a).                                      (6)

For arguments >=1 interpret mu as one; C>=1 makes the last bound valid there too. A power estimate initially on [0,x0] extends to all [0,1] after increasing C to at least x0^(-a).

Thus, conditional on that concrete spectral input, EVERY finite cover satisfies

  E_H <= 2c [C k/(k-a) m^(-2a)+beta_H(k(m-1)R)].                 (7)

This has the exact endpoint exponent 2a, without log or epsilon losses. For normal H with short(H)>k(m-1)R the beta term is zero. If an independently established spectral gap x0 exists, (4) gives the stronger exponential estimate and should be used instead. We do not substitute the weaker filter for the strongest available payment.

Neither (6) nor (7) asserts that a power law holds for every Q. The filter is the classical Fejer kernel normalized at zero and raised to an integer power; its use is polynomial approximation, not a newly closed Singer-specific bridge. The precise full-scope missing input is discussed in note03.

## 5. A chain homotopy realizing these filters simultaneously

The filtering is compatible with cellular boundaries, not merely a trace trick. Since D_j Delta_j=Delta_(j-1) D_j, every polynomial in the common rescaled Laplacians commutes across chain degrees. Put P=A_m^k and h(x)=(1-P(x))/x, a polynomial (since P(0)=1). Define

  K_j = L^(-1) D_(j+1)^* h(B_j): C_j -> C_(j+1).

Then, on the regular Hilbert complex AND on each finite signed or unsigned cover complex,

  D_(j+1)K_j + K_(j-1)D_j
     = L^(-1)(D_(j+1)D_(j+1)^*+D_j^*D_j)h(B_j)
     = I-P(B_j).                                               (8)

The finite polynomial makes K an actual bounded finite-propagation operator. If s bounds the differential support lengths, its propagation is at most s+(n-1)R. The coefficients need not be integral, and this is not an integral filling operation.

Its norm cost is explicit. Since 1-T_j(1-2x)=2 sin^2(j theta/2)<=2j^2 x,

  1-A_m(x) <= (4x/m^2) sum_(j=1)^(m-1)(m-j)j^2
            = (m^2-1)x/3.

Since 0<=A_m<=1, 1-A_m^k<=k(1-A_m). Therefore

  0<=h(x)<=k(m^2-1)/3,
  ||K_j|| <= ||D_(j+1)|| k(m^2-1)/(3L).                          (9)

The value h(0) is exactly k(m^2-1)/3, obtained by differentiating the polynomial. The quadratic growth in m has not disappeared.

For j!=2 on the universal cover, the source kills the spectral atom at zero, so P(B_j) tends strongly to zero as m increases with k fixed, by dominated convergence. For every fixed cycle z, (8) supplies L2 approximate fillings with error P(B_j)z tending to zero. It supplies neither a uniform decay rate over the unit sphere nor an integral finite-chain filling. At degree2 it converges to the harmonic projection of dimension chi(Q); one must retain that middle term. A finite cover also retains its actual harmonic kernel. Treating (8) as a contraction on either of those kernels would be an error.
