# I259: dimension-uniform local stability for rotating soliton channels

2026-10-12. Parent-authored candidate replacing the restricted I250 direction. No independent gates have run and no acceptance is claimed.

## Proposed theorem

Fix a>0, 1/2<gamma<3/2, L>0, and r=(gamma-1/2)^(-1)>1. Set

    w(x)=(r+1)a^2 sech^2(ra x),
    phi(x)=c sech^(1/r)(ra x),  integral phi^2=1,
    rho=phi^2,  Z=integral w rho,
    tau=Z^(-1) integral_{|x|>L} w rho >0,
    k=min_{|x|<=L} w(x)rho(x)>0.

There are explicit eta,c_-,c_+>0 depending only on a,gamma,L such that the following holds **for every finite m>=2**. Let f:R -> R^(m-1) be bounded measurable, supported in [-L,L], with ||f||_infinity<=eta, and define

    v_f(x)=(sqrt(1-|f(x)|^2),f(x)) in R^m,
    W_f(x)=w(x) v_f(x)v_f(x)^T,
    H_f=-d^2/dx^2 I_m-W_f.

Let C_gamma be the stipulated sharp matrix Lieb–Thirring constant and p=gamma+1/2. Define

    D(f)=C_gamma integral tr(W_f^p)-Tr(H_f)_-^gamma,
    V(f)=inf_{b in R^(m-1)} integral w rho |f-b|^2.

Then the proposed uniform estimate is

    c_- V(f) <= D(f) <= c_+ V(f).                         (S)

There is no derivative, oscillation, number-of-components, or finite-dimensional coefficient bound on f beyond its stated L-infinity bound. All constants below are independent of m and f. The fixed support interval is essential to this proof; no support-uniform estimate is claimed. The real-valued chart restriction is explicit, and no complex-channel extension is claimed here.

This is a local estimate near a single occupied soliton channel, not a global stability theorem for every extremal multi-soliton potential. It controls the full negative-eigenvalue sum, including eigenvalues newly emerging at zero.

## Explicit constants

Write w_max=(r+1)a^2, v_L=(r-1)a^2 sech^2(ra L), and choose

    c_L=a^2/[2(1+a^2/v_L)],
    B0=w_max+2w_max^2/c_L,
    rho0=1/[48(r+1)], B=80(r+1), A0=2B/rho0^2,
    N0=[B0/(2k)]^(2 gamma) Z^(2 gamma-1),
    m_gamma=gamma a^(2 gamma-2) min(1,(7/8)^(gamma-1)),
    M_gamma=gamma a^(2 gamma-2) max(1,(7/8)^(gamma-1)).

One proposed choice is

    eta=min{rho0/2,
            sqrt[tau/(4 A0(r+2))],
            [tau m_gamma/(4 N0(r+2))]^(1/(4 gamma-2))},
    c_-=m_gamma/[2(r+2)], c_+=M_gamma/tau.

All quantities are positive. The normalization of phi is explicit:

    c^2=ra Gamma(1/2+1/r)/(sqrt(pi) Gamma(1/r)),
    Z=2(r+1)a^2/(r+2),
    k=(r+1)a^2 c^2 sech^(2+2/r)(ra L).

The integral defining tau is an ordinary positive incomplete beta integral; no optimization or implicit existence constant enters eta.

## Sources and their exact roles

The pinned family 262 equality theorem gives the sharp constant and the scalar extremizer w, with sole negative eigenvalue -a^2. The parent previously read its actual introduction and theorem, as recorded in I250. Its matrix companion and full equality argument still require an independent overlap check before accepting this candidate.

The external input is Hundertmark–Laptev–Weidl, *New bounds on the Lieb–Thirring constants*, Theorem 3.1: for a nonnegative finite-matrix potential U with integrable trace,

    Tr(-d^2/dx^2 I-U)_-^(1/2) <= (1/2) integral tr U.     (HLW)

The parent read primary PDF pages 3–6, including the theorem, operator-domain conventions, majorization lemma, Cauchy-kernel monotonicity and full proof. The primary PDF is https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf . Formulae were visually inspected because text extraction omitted mathematical glyphs. This endpoint theorem is a credited external input, not attributed to the pinned corpus and not new here.

## 1. Ground state, local coercivity, and vector quadratic form

Let h=-d^2/dx^2-w and A=d/dx+a tanh(ra x). Direct differentiation gives

    A*A=h+a^2,
    AA*=a^2+L_+,
    L_+=-d^2/dx^2+(r-1)a^2 sech^2(ra x)>=0.

The kernel of A is span(phi); the spectrum of h on phi-perp is nonnegative. For u perpendicular to phi, write u=A*y, y=(AA*)^(-1)Au. On smooth vectors and then by form closure,

    q_h[u]=a^2 <y,L_+ y>+||L_+ y||^2,
    ||u||_L2([-L,L])^2 <= (2/a^2+2/v_L)q_h[u].

Thus q_h[u]>=c_L ||u||_L2([-L,L])^2. This is a local form estimate, not a nonexistent positive gap above zero for h itself.

For a bounded measurable vector f supported in this interval, set

    T(f)=integral w rho |f|^2,
    Q(f)=T(f)-sum_j <w f_j phi,(-d^2/dx^2+a^2)^(-1) w f_j phi>.

The scalar completion of squares, summed over components, gives

    Q(f)=min_g [integral rho |g'|^2+integral w rho |g-f|^2],
    V(f)/(r+2)<=Q(f)<=V(f).                              (1)

Here the minimizer is obtained componentwise from the free resolvent by writing its output as phi g_j. For completeness, the weighted Poincare inequality

    integral rho |g-E_rho g|^2<=a^(-2) integral rho |g'|^2

is the ground-state transform of the gap above zero for h+a^2 on phi-perp. Taking b=E_rho g and applying the triangle inequality in L2(w rho), followed by Cauchy–Schwarz on the two summands, yields V(f)<=(1+w_max/a^2)Q(f)=(r+2)Q(f). Constant g gives the reverse upper bound. Each estimate sums Hilbert norms and is independent of the number of components.

Support gives an additional useful estimate:

    tau T(f)<=V(f)<=T(f).                                (2)

Indeed the weighted mean minimizes V, and Cauchy–Schwarz on [-L,L] yields |integral w rho f|^2 <=(1-tau) Z T(f). This step is why support control is retained explicitly.

## 2. Uniform analytic remainder for the ground eigenvalue

If M=||f||_infinity=0 the theorem is immediate. Otherwise let b=f/M, so ||b||_infinity=1, and consider the analytic family for complex z near zero:

    v_z=(sqrt(1-z^2 |b|^2),z b),
    W_z=w v_z v_z^T, H_z=H_0+V_z.

The square root is the analytic branch equal to one at zero. The transpose, not a complex adjoint, defines the analytic continuation; for real z it gives exactly the real symmetric potential. For |z|<=rho0, elementary rank-two block estimates give

    ||V_z||<=6w_max |z|<=a^2/8,
    |<psi,V_z psi>|<=4|z|^2 T(b),
    ||V_z psi||, ||V_z^* psi||<=6 sqrt(w_max T(b)) |z|,
    psi=(phi,0,...,0).

These use the Euclidean norm of b, not sums of absolute component magnitudes; there is no hidden m factor.

The spectrum of H_0 is the simple eigenvalue -a^2 and the nonnegative spectrum. A resolvent Neumann series gives one analytic eigenvalue lambda(z) in the disk about -a^2 of radius a^2/4. Let delta(z)=lambda(z)+a^2. Compress to psi-perp. Its resolvent at lambda(z), after adding V_z, has norm at most 2/a^2. The scalar Feshbach identity then gives

    |delta(z)|<=B |z|^2 T(b).

The symmetry diag(1,-I_(m-1)) conjugates H_z to H_-z, so delta is even. Solving the first two perturbation equations gives delta(z)=z^2 Q(b)+O(z^4). More quantitatively F(z)=delta(z)/z^2 extends as an even analytic function to |z|<=rho0, bounded by B T(b). Its Taylor coefficients and a geometric-series estimate for |z|<=rho0/2 imply

    |delta(z)-z^2 Q(b)|<=A0 |z|^4 T(b).

Consequently at real z=M,

    |delta(f)-Q(f)|<=A0 M^2 T(f).                       (3)

For real f, 0<=W_f<=wI implies lambda_1(H_f)>=-a^2. Testing with psi gives lambda_1(H_f)<=-a^2+T(f). The isolated branch is the ground eigenvalue by the spectral separation just established. Thus

    0<=delta(f)<=T(f),    delta(f)<=a^2/8.              (4)

The analytic argument does not require any spatial derivative of b or f.

## 3. All additional eigenvalues, uniformly in channel number

On the codimension-one subspace u perpendicular to phi in the first channel, write a vector as (u,v) with v taking values in R^(m-1), or its complexification. Expansion of the real potential gives

    q_f[u,v] >= q_h[u]+||v'||^2-integral w |f^T v|^2
                   -2 integral w |u| |f^T v|.

The omitted first diagonal perturbation is nonnegative. Since f is supported in [-L,L], the local coercivity and Young inequality give

    q_f[u,v] >= (1/2)q_h[u]+||v'||^2
                         -B0 integral |f^T v|^2.        (5)

Let K_f=-d^2/dx^2 I_(m-1)-B0 f f^T. This potential is bounded, compactly supported and positive semidefinite, with trace B0|f|^2. Compression interlacing and form comparison in (5) bound the negative eigenvalues of H_f after the first by those of K_f, including multiplicities. Apply (HLW), then the inequality sum t_j^(2 gamma)<=(sum t_j)^(2 gamma), valid for nonnegative t_j because 2 gamma>1. This gives

    sum_{j>=2} |lambda_j(H_f)|_-^gamma
       <= [(B0/2) integral |f|^2]^(2 gamma)
       <= N0 M^(4 gamma-2) T(f).                        (6)

In the second step integral |f|^2<=T(f)/k and T(f)<=Z M^2. The inequality also holds for an empty or infinite negative list by monotone limits. This pays the threshold contribution without bounding the number of eigenvalues by m.

## 4. Full trace deficit

Pointwise W_f has eigenvalues w,0,...,0, so the stipulated soliton equality gives

    C_gamma integral tr(W_f^p)=a^(2 gamma).

For 0<=delta<=a^2/8, the mean-value theorem bounds

    m_gamma delta <=a^(2 gamma)-(a^2-delta)^gamma
                         <=M_gamma delta.

Use (1)–(6) and T(f)<=V(f)/tau. The deficit is bounded below by

    [m_gamma/(r+2)
       -(m_gamma A0 M^2+N0 M^(4 gamma-2))/tau] V(f).

The displayed choice of eta bounds each of the two error terms by m_gamma/[4(r+2)], proving the lower half of (S). For the upper half, discard the nonnegative moments of all additional eigenvalues, use delta<=T(f), and then (2), to get D(f)<=M_gamma V(f)/tau.

This completes the proposed proof with the stated constants.

## 5. Matrix-potential distance interpretation

The same result is a quadratic stability estimate modulo constant channel orientation. For |b|<=eta put P_b=v_b v_b^T, v_b=(sqrt(1-|b|^2),b), and set

    dist(f)^2=inf_{|b|<=eta} integral (rho/w)
                              ||W_f-wP_b||_HS^2.

The weight rho/w is specified exactly, so this is not an unweighted L2 claim. Since eta<1/4, two chart vectors satisfy v_f dot v_b>=1-2eta^2>0, and the map f -> v_f has Lipschitz constant at most two and lower Lipschitz constant one. The exact identity

    ||v_f v_f^T-v_b v_b^T||_HS^2
       =(1+v_f dot v_b)||v_f-v_b||^2

therefore places the pointwise squared distance between |f-b|^2 and 8|f-b|^2. The minimizer of V(f) is the weighted mean of f and has norm at most eta. Consequently

    V(f)<=dist(f)^2<=8V(f),
    (c_-/8)dist(f)^2 <=D(f)<=c_+ dist(f)^2.

This is a reformulation of the same proposed finding, not another counted result. It compares with constant orientations having the fixed scalar profile w and lying in the stated chart.

## Checks and remaining gates

- f=0 gives D=V=0. The weighted variance accounts for constant channel changes, while support prevents a nonzero constant change on the whole line. No false spectral gap at zero is used.
- The endpoint gamma=1/2 is excluded because 4 gamma-2 vanishes. The endpoint gamma=3/2 is excluded to retain the stated scalar equality structure. No conclusion uniform in either endpoint is asserted.
- The estimate is genuinely independent of finite channel number and of the measurable profile's oscillation. Its radius and constants deteriorate with growing support L.
- Complex-valued channel maps, multiple initially occupied solitons and global arbitrary-amplitude perturbations remain outside the statement.
- This is a candidate deduction, not an acceptance. Independent proof and contribution reviews must check the Feshbach bounds, interlacing, exact external endpoint hypothesis, and overlap with established scalar/vector stability results. The earlier I250 fixed-profile Hessian is not a separate counted finding.
