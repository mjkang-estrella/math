# I262: spatially global, dimension-uniform soliton-channel stability

2026-10-12. Parent-authored strengthened candidate. It supersedes the restricted I250 and fixed-support I259 proposals as **one** prospective finding. No independent review or acceptance is claimed.

## Exact proposed theorem

Fix a>0 and 1/2<gamma<3/2. Put r=(gamma-1/2)^(-1)>1,

    w(x)=w0 sech^2(ra x), w0=(r+1)a^2,
    phi(x)=c sech^(1/r)(ra x), integral phi^2=1,
    rho=phi^2, Z=integral w rho.

There are explicit positive eta,c_-,c_+, depending only on a,gamma, such that the following holds for **every** finite m>=2. Let v:R->S^(m-1) be measurable and suppose some fixed unit e0 satisfies

    ess sup_x |v(x)-e0| <= eta.

Define P(x)=v(x)v(x)^T, W(x)=w(x)P(x), and H=-d^2/dx^2 I_m-W. With the stipulated sharp constant C_gamma and p=gamma+1/2, put

    D(W)=C_gamma integral tr(W^p)-Tr(H)_-^gamma,
    J(P)=inf_{|e|=1} integral w rho [1-(v dot e)^2].

The proposed theorem is

    c_- J(P) <= D(W) <= c_+ J(P).                         (G)

Equivalently, 2J is the infimum of integral w rho ||P-ee^T||_HS^2. The distance is to constant rank-one channels with the **same fixed soliton profile**. This is a local theorem in the essential-supremum distance of orientations, but is spatially global: there is no support, derivative, variation, decay, or oscillation assumption on v. It allows any finite number of real channels, with the same constants.

No assertion is made for complex orientations, several initially occupied channels, changes of the scalar profile, arbitrary-amplitude rotations, or endpoint exponents. This is not a global theorem on the entire class of matrix potentials.

## Constants

Let

    c^2=ra Gamma(1/2+1/r)/(sqrt(pi) Gamma(1/r)),
    c_w=(r-1)/[2r(r+1)], B_w=1+2/c_w,
    rho0=1/[48(r+1)], B=80(r+1), A0=2B/rho0^2,
    I_w=integral sqrt(w)=pi sqrt(r+1)/r,
    N0=(B_w/2)^(2gamma) (w0^(1/r)/c^2) I_w^(2gamma-1),
    m_gamma=gamma a^(2gamma-2) min(1,(7/8)^(gamma-1)),
    M_gamma=gamma a^(2gamma-2) max(1,(7/8)^(gamma-1)).

Choose

    M_* = min{rho0/2, 1/2,
               [1/(8A0(r+2))]^(1/2),
               [m_gamma/(8N0(r+2))]^(1/(4gamma-2))},
    eta=min{1/8,M_*/4},
    c_-=m_gamma/[4(r+2)], c_+=M_gamma.

Every constant is finite and positive for the stated open exponent range. No constant depends on m or on v.

## 1. Choice of one global channel

Let T0=Z^(-1) integral w rho v v^T, a real positive semidefinite m by m matrix of trace one. Let e be a unit eigenvector of its largest eigenvalue lambda, with e dot e0>=0. Since v is eta-close to e0,

    lambda >= e0^T T0 e0 >=1-eta^2,
    lambda |proj_(e0-perp)e|
       =|proj_(e0-perp) T0 e| <=eta.

Thus |e-e0|<=sqrt(2)eta/(1-eta^2)<=3eta, and |v-e|<=4eta. In particular v dot e>0. After one constant orthogonal conjugation write

    v=(sqrt(1-|f|^2),f), f:R->R^(m-1), M=||f||_infinity<=4eta<=M_*.

Put T=integral w rho |f|^2. The choice of e gives

    T=J(P),
    integral w rho sqrt(1-|f|^2) f=0.                     (1)

If T=0, v is constant almost everywhere and (G) follows from the stipulated equality case. Assume T>0 below.

Let V(f)=inf_b integral w rho |f-b|^2. Equation (1) implies

    integral w rho f=integral w rho(1-sqrt(1-|f|^2))f.

Cauchy–Schwarz gives |integral w rho f|^2/Z<=M^4 T. Therefore

    V(f)>= (1-M^4)T >= T/2.                              (2)

This replaces I259's fixed-support tail-mass estimate. Choosing the principal channel is substantive: an arbitrary original chart would not make (1) true.

## 2. Global weighted coercivity off the scalar ground state

Set h=-d^2/dx^2-w and A=d/dx+a tanh(ra x). Then

    A*A=h+a^2,
    AA*=a^2+L_+,
    L_+=-d^2/dx^2+[(r-1)/(r+1)] w.

The normalized kernel of A is phi. On phi-perp h is nonnegative. For u in H^1 perpendicular to phi, set y=(AA*)^(-1)Au, so u=A*y. Smooth approximation and the form identities give

    q_h[u]=a^2 <y,L_+y>+||L_+y||^2,
    integral w |u|^2
       <=2w0 integral |y'|^2+2a^2 integral w |y|^2
       <=[2(r+1)+2(r+1)/(r-1)]q_h[u].

Hence

    q_h[u]>=c_w integral w |u|^2.                       (3)

This estimate is global and weighted. It does not assert a false positive unweighted spectral gap for h above its continuous threshold.

Define the quadratic form

    Q(f)=T-sum_j <w f_j phi,(-d^2/dx^2+a^2)^(-1) w f_j phi>.

Ground-state transformation of the scalar positive free resolvent gives

    Q(f)=min_g [integral rho |g'|^2+integral w rho |g-f|^2].

The gap a^2 for h+a^2 on phi-perp yields the weighted Poincare inequality with measure rho. The triangle inequality in L2(w rho), followed by Cauchy–Schwarz, gives

    V(f)/(r+2)<=Q(f)<=V(f).

Together with (2),

    Q(f)>=T/[2(r+2)].                                   (4)

All identities hold componentwise and sum in Euclidean norm without dimension factors. For bounded measurable f, the free resolvent is well-defined because w f phi is in L2. The ground-state transform follows by form closure; compact support of f is not needed.

## 3. Uniform isolated-eigenvalue remainder

Write f=M b with ||b||_infinity=1. For complex z with |z|<=rho0 consider

    v_z=(sqrt(1-z^2|b|^2),z b), W_z=w v_z v_z^T,
    H_z=H_0+U_z, H_0=h direct-sum (-d^2 I_(m-1)).

The transpose defines analytic continuation; for real z it agrees with the desired symmetric potential. The square-root branch is fixed by its value one at zero. Rank-two block norm estimates imply

    ||U_z||<=6w0|z|<=a^2/8,
    |<psi,U_z psi>|<=4|z|^2 T(b),
    ||U_z psi||, ||U_z^* psi||<=6sqrt(w0 T(b))|z|,
    psi=(phi,0,...,0).

The Riesz projection around the isolated simple eigenvalue -a^2 remains rank one. Its analytic eigenvalue lambda(z) is in the a^2/4 disk about -a^2. On psi-perp, the resolvent of the compressed H_z at lambda(z) has norm <=2/a^2. The scalar Feshbach identity therefore gives

    |lambda(z)+a^2|<=B |z|^2 T(b).

Conjugation by diag(1,-I) changes z to -z. Thus F(z)=(lambda(z)+a^2)/z^2 is even analytic and bounded by B T(b). The second-order eigenvalue equation gives F(0)=Q(b). Cauchy coefficient estimates and the even geometric series on |z|<=rho0/2 give

    |lambda(z)+a^2-z^2 Q(b)|<=A0 |z|^4 T(b).

At z=M this reads, with delta=lambda_1(H)+a^2,

    |delta-Q(f)|<=A0 M^2 T.                             (5)

For real f, W<=wI, while testing with psi gives

    0<=delta<=T, delta<=a^2/8.                           (6)

The spectral separation of the Riesz branch identifies it as the ground eigenvalue. The estimates involve no spatial regularity or support radius.

## 4. All additional eigenvalues: the critical interpolation

On the codimension-one subspace u perpendicular to phi in the first channel, the quadratic form, (3), and Young's inequality give

    q_H[u,v]>= (1/2)q_h[u]+||v'||^2
                            -B_w integral w |f^T v|^2.

Compare the negative eigenvalues after the first, by compression interlacing and form order, with those of

    K_f=-d^2 I_(m-1)-B_w w f f^T.

The external operator-valued endpoint theorem of Hundertmark–Laptev–Weidl, Theorem 3.1, gives

    sum_j sqrt(|lambda_j(K_f)|_-)
                       <=(B_w/2) integral w |f|^2.

Since 2gamma>1, summing powers after the square roots gives

    sum_{j>=2}|lambda_j(H)|_-^gamma
                  <=[(B_w/2) integral w |f|^2]^(2gamma).

The exact identity w rho=c^2 w0^(-1/r) w^p, with p=gamma+1/2, is decisive. Holder's inequality in the form

    (integral w |f|^2)^(2gamma)
       <=(integral w^p |f|^2)
                         (integral sqrt(w) |f|^2)^(2gamma-1)

uses the identity 1=p/(2gamma)+(1/2)(1-1/(2gamma)). As integral sqrt(w)|f|^2<=M^2 I_w, it follows that

    sum_{j>=2}|lambda_j(H)|_-^gamma
                         <=N0 M^(4gamma-2) T.            (7)

This removes both the support dependence and the factor counting additional channels. It allows infinitely many negative eigenvalues in intermediate estimates by monotone convergence; m itself remains arbitrary finite as stated.

## 5. Finish the full trace estimate

The pointwise eigenvalues of W are w,0,...,0. By the stipulated scalar soliton equality,

    C_gamma integral tr W^p=a^(2gamma).

The mean-value theorem and (6) bound a^(2gamma)-(a^2-delta)^gamma between m_gamma delta and M_gamma delta. Using (4), (5) and (7),

    D(W)>=[m_gamma/(2(r+2))
                 -m_gamma A0 M^2-N0 M^(4gamma-2)]T.

Each of the two subtracted terms is at most m_gamma/[8(r+2)] by the choice of M_*. This proves the lower bound c_-T. The upper bound follows by discarding the other nonnegative eigenvalue moments and using delta<=T. Finally T=J(P) by (1), proving (G).

## Sources, risks and intended review scope

The pinned family-262 scalar profile and sharp matrix constant are the same inputs as in I250/I259. The external endpoint theorem, including its full presented proof, was read on pages 3–6 of the author-hosted primary PDF; details and its hash are in I259's source record. Scalar Carlen–Frank–Lieb stability is existing prior art, not credited here.

The proposed new contribution is the spatially global and channel-uniform control of the full moment deficit. Its new steps relative to I259 are principal-channel centering, global weighted coercivity, and the critical weighted interpolation of the endpoint bound. A contribution reviewer must still determine whether existing matrix/vector stability already subsumes this argument or makes it only a technical corollary.

No independent proof or contribution verdict is claimed. The prepared I260/I261 briefs must be updated to this strengthened exact target before either is launched. The old proposals and this one are one research chain, not several accepted findings.
