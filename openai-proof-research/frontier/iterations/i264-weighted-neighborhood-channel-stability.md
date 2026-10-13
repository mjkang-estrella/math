# I264: channel stability in a weighted neighborhood

Parent-authored candidate, 2026-10-12. **Unreviewed; no count increment.** This is a strengthening in the I250/I259/I262 chain, not a separate prospective finding. The exact I262 text currently under independent review is unchanged.

## Proposed theorem

Fix a>0 and 1/2<gamma<3/2. Write r=(gamma-1/2)^(-1)>1, p=gamma+1/2,

    w=w0 sech^2(ra x), w0=(r+1)a^2,
    phi=c sech^(1/r)(ra x), integral phi^2=1, rho=phi^2,
    Z=integral w rho.

For every finite m>=2 and every measurable real unit field v:R->S^(m-1), let

    P=v v^T, H=-d^2 I_m-wP,
    J=inf_(|e|=1) integral w rho [1-(v dot e)^2],
    D=C_gamma integral w^p-Tr(H)_-^gamma.

Here C_gamma is the stipulated sharp matrix Lieb--Thirring constant; the scalar soliton saturates it, so C_gamma integral w^p=a^(2gamma).

There are explicit tau,c_-,c_+>0 depending only on a,gamma such that

    J<=tau  implies  c_- J<=D<=c_+ J.                 (W)

There is **no pointwise closeness, support, derivative, variation or decay assumption** on v. Orientations can be orthogonal to the optimal constant channel on measurable exceptional sets, including sets arbitrarily far out in the soliton tails. The hypothesis is weighted average closeness alone. Scalar profile changes, complex channels, arbitrary-rank potentials, endpoint exponents and estimates when J>tau are not claimed.

## Constants

All integrals below are over the real line. Define

    C1=(integral w/rho)^(1/2), K=(r+2)/(2a),
    c_w=(r-1)/(2r(r+1)), B_w=1+2/c_w,
    theta=r/[4(r+1)],
    Ctheta=[integral (sqrt(w)/(w rho)^theta)^(1/(1-theta))]^(1-theta),
    N=(B_w/2)^(2gamma) (w0^(1/r)/c^2) Ctheta^(2gamma-1),
    m_gamma=gamma a^(2gamma-2) min{1,(7/8)^(gamma-1)},
    M_gamma=gamma a^(2gamma-2) max{1,(7/8)^(gamma-1)}.

The integrals defining C1 and Ctheta converge: w/rho decays as exp(-2a(r-1)|x|), and the numerator inside Ctheta has exponential decay because r-2theta(r+1)=r/2>0. In particular these are explicit constants, alternatively evaluable by the standard integral of powers of sech. Set

    tau=min{Z/4, a^2/[12(r+2)],
            [12(r+2) K C1]^(-2),
            [m_gamma/(4(r+2)N)]^(1/[theta(2gamma-1)])},
    c_-=m_gamma/[4(r+2)], c_+=M_gamma.

## 1. Principal channel and measurable gauge

The finite real covariance matrix Z^(-1) integral w rho P has a maximal unit eigenvector e. After one constant orthogonal conjugation, put e first. Replacing v pointwise by its negative when its first coordinate is negative does not change P or H. On the zero set choose either sign measurably. We can therefore write

    v=(alpha,f), alpha=sqrt(1-|f|^2)>=0, |f|<=1,
    integral w rho |f|^2=J,
    integral w rho alpha f=0.                          (1)

No essential-supremum estimate follows or is needed. Define g=alpha f. Then g has weighted mean zero and

    Tg=integral w rho |g|^2<=J.

If J=0, P is constant almost everywhere and (W) is the scalar equality. Henceforth 0<J<=tau.

Let H0=h direct-sum (-d^2 I_(m-1)), h=-d^2-w, psi=(phi,0), Q=I-|psi><psi|, and U=H-H0=w(e e^T-P). The exact pointwise operator norm is ||U(x)||=w(x)|f(x)|. Thus Cauchy--Schwarz gives

    L:=integral ||U||=integral w|f|<=C1 sqrt(J),
    L2:=integral w|f|^2<=L.                            (2)

This is the first replacement for the pointwise-small analytic perturbation in I262.

## 2. Scalar identities and the weighted quadratic form

For A=d/dx+a tanh(ra x),

    A*A=h+a^2, AA*=a^2+Lplus,
    Lplus=-d^2+[(r-1)/(r+1)]w.

The kernel of A is spanned by phi. Since AA*>=a^2, h is nonnegative on phi-perp. The same factorization gives, for u perpendicular to phi,

    q_h[u]>=c_w integral w|u|^2.                       (3)

For completeness set y=(AA*)^(-1)Au, so u=A*y. On a form core,

    q_h[u]=a^2<y,Lplus y>+||Lplus y||^2,
    integral w|u|^2<=2w0 integral |y'|^2+2a^2 integral w|y|^2
                  <=[2(r+1)+2(r+1)/(r-1)]q_h[u].

Closure proves (3). The factorization also yields the ground-state Poincare inequality

    integral rho |k-integral rho k|^2
                   <=a^(-2) integral rho |k'|^2.

For a bounded vector function g define

    Qform(g)=integral w rho |g|^2
              -<w g phi,(-d^2+a^2)^(-1) w g phi>.

Completion of the square after the ground-state transform proves

    Qform(g)=inf_k {integral rho |k'|^2+integral w rho |k-g|^2}.

Write V(g)=inf_b integral w rho |g-b|^2. By w<=w0, the Poincare inequality and the triangle inequality,

    sqrt(V(g))<=sqrt(r+1) sqrt(integral rho |k'|^2)
                         +sqrt(integral w rho |k-g|^2).

Taking the infimum gives Qform(g)>=V(g)/(r+2). By (1), V(g)=Tg. Consequently, with

    B2=<w g phi,(-d^2+a^2)^(-1)w g phi>,

we have

    J-B2=J-Tg+Qform(g)>=J/(r+2).                      (4)

Unlike a Taylor expansion in f, (4) retains the large-angle term J-Tg=integral w rho |f|^4 with its favorable sign.

## 3. A form estimate near the isolated eigenvalue

On Q define B0=Q(H0+a^2)Q. It is positive, B0>=a^2. For vector-valued u in its form domain,

    integral (|u'|^2+a^2|u|^2)<= (r+2)<u,B0u>.

The one-dimensional evaluation bound (componentwise, then summed) is

    sup_x |u(x)|^2<= (2a)^(-1) integral (|u'|^2+a^2|u|^2)
                  <=K<u,B0u>.

It follows from (2) that

    ||B0^(-1/2) Q U Q B0^(-1/2)||<=epsilon,
    epsilon=K C1 sqrt(J).                             (5)

Here the evaluation inequality can be obtained directly by the reproducing kernel of -d^2+a^2, whose diagonal is 1/(2a). It has no dimension factor.

As wP<=w I, H>=h I>=-a^2. Testing psi gives its lowest eigenvalue lambda1<=-a^2+J. Meanwhile QHQ>=-epsilon a^2. Our choice of tau makes epsilon<=1/[12(r+2)] and J/a^2<=1/[12(r+2)]. Thus lambda1 is a simple isolated eigenvalue below the spectrum of QHQ, and

    lambda1=-a^2+delta, 0<=delta<=J<a^2/8.

This also follows directly by the codimension-one min--max principle: QHQ has spectrum above -epsilon a^2, whereas the Rayleigh test is below that value. No analytic continuation or pointwise-small family is used.

Put t=epsilon+J/a^2<=1/[6(r+2)]<1/4. Then

    Q(H-lambda1)Q=B0+QUQ-delta Q,
    ||B0^(-1/2)(QUQ-delta Q)B0^(-1/2)||<=t.

Writing b=QU psi, the exact Feshbach equation is

    delta=J-<b,[Q(H-lambda1)Q]^(-1)b>.                 (6)

The two components of b are Q_scalar(w|f|^2 phi) and -w g phi. Hence

    B:=<b,B0^(-1)b>=B1+B2,
    B1=<Q_scalar(w|f|^2 phi),(h|_(phi-perp)+a^2)^(-1)
                                    Q_scalar(w|f|^2 phi)>.

The same evaluation bound gives the dual estimate

    B1<=K(integral w|f|^2 phi)^2<=K J L2<=epsilon J.  (7)

Indeed, testing against u perpendicular to phi removes the projection from the integrand; no L1-bound on the projected function is being silently assumed. The middle inequality is Cauchy--Schwarz on (sqrt(w)phi|f|) and (sqrt(w)|f|). Also B2<=Tg<=J. Form order therefore gives

    delta>=J-B/(1-t)
          >=J/(r+2)-epsilon J-[t/(1-t)](1+epsilon)J
          >=J/(r+2)-3tJ
          >=J/[2(r+2)].                               (8)

In the penultimate inequality epsilon<=t<1/4, so epsilon+t(1+epsilon)/(1-t)<=3t. This controls the first-channel quadratic term that would be lost by applying I262's small-angle expansion directly.

## 4. All other negative eigenvalues

For a first-channel u perpendicular to phi and a transverse vector z, (3) and Young's inequality give

    q_H[u,z]>= (1/2)q_h[u]+integral |z'|^2
                                     -B_w integral w|f^T z|^2.

This uses only alpha<=1 and |f|<=1. Compression interlacing and form order bound all eigenvalue moments after lambda1 by those of

    Kf=-d^2 I_(m-1)-B_w w f f^T.

The classical operator-valued endpoint theorem of Hundertmark--Laptev--Weidl, Theorem 3.1, gives

    sum_j sqrt(|lambda_j(Kf)|_-)<= (B_w/2) integral w|f|^2.

The matrix potential is nonnegative, bounded and trace-integrable. The theorem applies without compact support; its trace is exactly B_w w|f|^2. Consequently

    sum_(j>=2)|lambda_j(H)|_-^gamma
                            <=[(B_w/2) integral w|f|^2]^(2gamma).

Let Ahalf=integral sqrt(w)|f|^2. Critical Holder interpolation, using

    1=p/(2gamma)+(1/2)(1-1/(2gamma)),
    w rho=c^2 w0^(-1/r) w^p,

gives

    (integral w|f|^2)^(2gamma)
                <=(w0^(1/r)/c^2) J Ahalf^(2gamma-1).

A second weighted Holder inequality, now using |f|<=1 rather than a small supremum, gives

    Ahalf<= J^theta
       [integral (sqrt(w)/(w rho)^theta)^(1/(1-theta)) |f|^2]^(1-theta)
         <=Ctheta J^theta.

Thus

    sum_(j>=2)|lambda_j(H)|_-^gamma
                               <=N J^(1+theta(2gamma-1)).       (9)

The positive exponent theta(2gamma-1)=1/[2(r+1)] is essential. This pays for sparse, large-angle defects, including defects moving into the tails. All moment bounds include a possibly infinite sequence of eigenvalues by monotone convergence; channel dimension remains arbitrary finite.

## 5. Full deficit and scope

The scalar equality and the mean-value theorem give

    m_gamma delta<=a^(2gamma)-(a^2-delta)^gamma<=M_gamma delta.

Equations (8)--(9) and the last condition in tau imply

    D>= [m_gamma/(2(r+2))-N J^(theta(2gamma-1))]J
      >=m_gamma J/[4(r+2)].

Discarding the nonnegative moments after the first and using delta<=J gives D<=M_gamma J. This proves the proposed (W).

The proof's new burden relative to I262 is removal of pointwise smallness. Its replacements are the integrable weight ratio w/rho, dimension-free form estimates, the favorable large-angle term J-Tg, and the second weighted interpolation. The theorem is still local in J and keeps the scalar soliton fixed. It does not prove a global inequality for every matrix potential or a converse saying every small deficit has small J.

The stipulated matrix constant/scalar profile and external HLW theorem are credited as in I250/I259. The relevant primary-source read extents and identities are in those records; no new primary theorem is inferred from a search snippet. Whether this increment is substantial or already implied by broader matrix stability remains for independent contribution review. Whether every form and min--max argument is correct remains for independent proof review. The I260/I261 review targets are not changed by this draft.
