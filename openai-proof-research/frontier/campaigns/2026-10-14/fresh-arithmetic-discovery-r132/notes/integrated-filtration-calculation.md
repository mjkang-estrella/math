# Integrated below-endpoint calculation — PREFREEZE

This is a working reduction, not a frozen nominee or a claim to an independent contribution. The pin and its operative proofs are stipulated true. Throughout, the incoming germ is normal, complex algebraic, boundary-zero klt, singular, of dimension n=N+1>=5; analytic ODP means analytic isomorphism of germs. Write V=normalized volume, d=V/n^n, p_n=2((n-1)/n)^n. There is no boundary, field, normality or analyticity extension.

## Compatible operations before the obstruction

The complete all-dimension source proof supplies stable degeneration to a K-polystable cone with the same density and nondecreasing embedding dimension. Define

    C*=3 exp(4/3)/4-exp(1)/3 < 3879/2000 < 2,
    b_n=max{p_(n-1), C*(N/n)^n, ((N+1/2)/n)^n, 5p_n/6}.

Each entry is strictly smaller than p_n. In the regime d>b_n, the source's puncture argument makes the cone isolated; p_(n-1)>1/2 also makes it Gorenstein by the canonical-index cover. Use the source's fast primitive integral gradings zeta_i=(r_i/n)xi+epsilon_i with absolute epsilon_i tending to zero, where A(xi)=n. This is a fixed-cone statement, not a uniform assertion over a bounded family.

The small-stabilizer branch m_max<=r/N already gives the smooth/ODP classification. In the large branch, the transverse Taylor semigroup and local-unit/canonical shift argument apply unchanged. The moment-envelope proof only needs V/N^n>C*: with s=r/(Nm)<=1 and H the source integral, V<=N^n sH, while failure of interiority implies (1-eta/u)H<=C*, eta tending to zero. The strict margin therefore forces the canonical lattice point into the interior. The adjoint argument then supplies the saturated rational-polyhedral Gorenstein semigroup. This uses the actual multiplier/vanishing operation, not just a lattice assertion.

The reducedness argument needs V>(N+1/2)^n. The resulting second associated graded ring is D[v], with Hilb_T(D)=(1-z)^(-N) and canonical bidegree (r,n). In the nonsmooth residual branch D has a stabilizer h>=2. The level-slice construction gives a normal Gorenstein singular n-fold Y with a mu_h action and a parameter lambda_Y of character -1. The proof that Y is klt needs only V>N^n: a non-klt test would force V<=N^n. Thus the stipulated all-dimension theorem is applicable to Y itself, with all its hypotheses present.

For the invariant normalized-volume minimizer u on Y put ell=u(lambda_Y)>0, A'=A_Y(u), sigma=vol(u). Restriction gives w on C and

    A_C(w)<=N ell+A',
    vol(w)<=min_(0<=x<=1) {ell^(-n)x^n+(sigma/h)(1-x)^n},
    d(C)<=p_n/2+d(Y)/h.

The character factor 1/h is essential and is supplied by the source's injective multiplication by lambda_Y between character quotients; using the full upstairs length would lose it. Since d(Y)<=p_n, h>=3 forces d(C)<=5p_n/6. Our regime consequently leaves h=2. No nonroutine new operation has occurred.

## Counting the whole killed triangular region

The source's adapted vector-space basis is {v^a e_i}, a>=0, with W(v^a e_i)=a+T_i and the number of e_i of T-degree T equal to binomial(T+N-1,N-1). Since W-domination gives w(e_i)>=ell T_i, if q=w(v) and c=q/ell>=1, then

    w(v^a e_i)>=ell(ca+T_i).

In the exact length split at p=floor(kx/ell), the first summand is S/(F^p+ a_k(w)). The adapted basis modulo F^p consists of a+T<p. All its distinct elements with ca+T>=k/ell lie in the kernel. Thus counting ALL of these, not just one translated block, is valid without any independence assumption about their images in the valuation quotient. The second summand keeps the source character-share estimate.

Scale a=k A/ell and T=k B/ell. For c>1, the leading volume of the killed region A+B<x, cA+B>=1 is zero if cx<=1. Otherwise its normalized coefficient is

    n!/(N-1)! int_0^((cx-1)/(c-1))
       [x-1/c-(1-1/c)B] B^(N-1) dB
       = (cx-1)^n / [c(c-1)^(n-1)].

Consequently the strengthened bound is

    vol(w)<=ell^(-n) min_(0<=x<=1)
      {x^n - L_n(c,x) + (sigma ell^n/h)(1-x)^n},
    L_n(c,x)=((cx-1)_+)^n/[c(c-1)^(n-1)]  (c>1),
    L_n(1,x)=0.

Floors and the finitely many endpoint degrees affect only lower-order terms; the polynomial Hilbert function gives the displayed leading coefficient. Continuity supplies x=0,1. As a check, x=1 gives vol(w)<=1/(q ell^(n-1)). At ell=1,c>2,x=1/2 the subtraction is strictly positive, recovering and sharpening the source's equality-count contradiction.

This elementary full-region integration is not a new primitive. The source already injects one v-power block into this same kernel. Xu–Zhuang's uniqueness proof and Li–Xu Proposition 2.7 use related positive-size shell multiplications to make differing valuations force a strict volume loss. The present formula is a useful paid strengthening of that operation, not a substantial nominee.

## What the stronger count still fails to control

In the h=2 branch set t=A'/(N ell) and kappa=d(Y)/p_n<=1. Then sigma ell^n=2 kappa/t^n and the full bound becomes

    d(C)/p_n <= (1+t)^n/2 * min_x
      {x^n-L_n(c,x)+kappa/t^n(1-x)^n}.

Dropping L and applying the source's Holder optimization bounds this by (1+kappa)/2. At equality one must have kappa=1,t=1. The full count then forces c<=2. The source's uniqueness identity w=(2N/n)wt_xi additionally gives

    w(v)=2Nm/r+o(1/r),

so c<=2 rounds to Nm-r<=o(1), hence to Nm<=r. This forces the small-stabilizer classification.

Below equality the displayed inequalities give scalar restrictions on t,kappa,c, but they do not identify w with the Reeb valuation. In particular, they do not compare w(v)/ell with 2Nm/r to the o(1/r) accuracy required for the integer Nm-r. A constant-size error in this comparison, even one tending to zero with the density defect, becomes r times that error after rounding. Primitive rational approximants may have unbounded r. Xu–Zhuang uniqueness proves equality rigidity by valuation-dependent witnesses and positive-tail estimates; its read proof does not provide the uniform quantitative comparison just described.

The strongest primary boundedness/discreteness result does already pay a qualitative second gap. Bounded families of cones with density bounded below, together with constructibility of local volume in Q-Gorenstein families, give only finitely many volume values above a fixed positive threshold; the primary explicitly states that zero is the only accumulation point. Combining that with the stipulated ODP equality characterization isolates the ODP value. This is not a new theorem here. The boundedness definition allows varying Reeb vectors and does not bound denominators of chosen approximating rational rays. Replacing the missing comparison by 'boundedness' is therefore not a completed effective argument.

No quantitative modulus, effective bounded-generation replacement, or alternative nonroutine closure has been proved. The old r25 screen-037 original is expressly excluded; this calculation neither determines its full scope nor renominates it. No exhaustion or priority claim follows.
