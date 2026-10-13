# I250: transverse Hessian for the full matrix Lieb–Thirring deficit

2026-10-12. Parent-authored candidate; not independently reviewed or accepted.

## Exact statement proposed for review

Fix 1/2<gamma<3/2, r=(gamma-1/2)^(-1)>1, a>0, and a real theta in C_c^infinity(R). Let L>0 contain its support and set

    w(x)=(r+1)a^2 sech^2(ra x),
    phi(x)=c sech^(1/r)(ra x),       integral phi^2=1,
    v_e(x)=(cos(e theta(x)),sin(e theta(x)))^T,
    W_e(x)=w(x) v_e(x) v_e(x)^T,
    H_e=-d^2/dx^2 I_2-W_e.

Let C_gamma be the stipulated sharp one-bound-state constant, p=gamma+1/2, and define the **full** deficit

    D(e)=C_gamma integral tr(W_e^p)-Tr(H_e)_-^gamma.

The potential integral is independent of e and equals a^(2 gamma)/C_gamma. Define

    Q(theta)=integral w phi^2 theta^2
             - <w theta phi,(-d^2/dx^2+a^2)^(-1) w theta phi>,
    V(theta)=inf_{c in R} integral w phi^2 (theta-c)^2.

The proposed conclusion is

    D(e)=gamma a^(2 gamma-2) Q(theta) e^2
             +O(|e|^min(4,4 gamma))     as e -> 0,
    V(theta)/(r+2) <= Q(theta) <= V(theta).

Constants in the remainder may depend on a,r,L and theta. This is not uniform over varying theta or growing support, and it asserts no global stability theorem. For nonzero compactly supported theta, V(theta)>0, so the full spectral deficit has a strictly positive quadratic leading coefficient. Global constant rotations have zero coefficient, as they must.

The sought contribution is a quantitative local stability statement for spatially rotating internal channels in the **sum of all negative eigenvalue moments**. It is not the already established scalar lowest-eigenvalue stability or the source's auxiliary action defect. Whether this distinction is substantial enough to count is a separate review question.

## Stipulated source contract

Pinned revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The exact source is

[Equality cases in the sharp one-dimensional matrix Lieb–Thirring inequality](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026), build/sections/introduction.tex, Theorem thm:main. It gives the sharp full matrix moment inequality and its constant-unitary scalar-soliton equality classification. In particular w has exactly one negative eigenvalue -a^2 and saturates the scalar bound. These source assertions are assumed true, not audited.

The parent fully read introduction.tex and spectral-bound.tex, action.tex through line 95 (including act:quantitative-action), and rigidity.tex through line 115. Other retrieved portions were searched, not fully read or copied. The source already retains auxiliary first-order and commutator defects; simply displaying those is not new.

The matrix-inequality companion and the remaining equality proof must still be checked for overlap by the independent contribution reviewer. No claim of worldwide novelty is made.

## Complete proposed argument

### 1. Isolated ground-state branch

Put h=-d^2/dx^2-w. Direct differentiation gives h phi=-a^2 phi. Let

    A=d/dx+a tanh(ra x),
    A*= -d/dx+a tanh(ra x).

Then

    A*A=h+a^2,
    AA*=a^2+L_+,
    L_+=-d^2/dx^2+(r-1)a^2 sech^2(ra x)>=0.

Thus h restricted to phi-perp has nonnegative quadratic form. The kernel of A is spanned by phi; AA*>=a^2 excludes additional negative eigenvalues of h. This is also part of the stipulated source conclusion.

At e=0, H_0=h direct-sum (-d^2/dx^2), with a simple isolated eigenvalue -a^2. The bounded multiplication perturbation W_e is operator-norm analytic in e near zero, on a common H^2 domain. A resolvent Neumann series on a circle of radius less than a^2 about -a^2 gives an analytic rank-one Riesz projection. It gives a unique analytic eigenvalue lambda_1(e) near -a^2. Conjugation by diag(1,-1) maps H_e to H_-e, so this branch is even.

The expansion of H_e-H_0 has first coefficient

    V_1=[[0,-w theta],[-w theta,0]]

and second coefficient

    V_2=[[w theta^2,0],[0,-w theta^2]].

Solving the first-order eigenvector equation on the orthogonal complement of (phi,0), and projecting the second-order equation on (phi,0), gives

    lambda_1(e)=-a^2+e^2 Q(theta)+O(e^4).

Only the free second channel enters the reduced resolvent because V_1(phi,0)=(0,-w theta phi). Evenness removes the cubic term. This calculation concerns the isolated eigenvalue; possible new eigenvalues at zero are treated next, not ignored.

### 2. Explicit local coercivity off the ground state

For u in H^1 perpendicular to phi, represent u=A*y with y=(AA*)^(-1)Au. First use smooth vectors and then form density. Since AA*>=a^2, this representation holds on phi-perp. Its regularity gives y in H^2 and

    q_h[u]=a^2 <y,L_+ y>+||L_+ y||_2^2
             >=a^2 (||y'||_2^2+integral V_+ |y|^2),
    V_+=(r-1)a^2 sech^2(ra x).

On I=[-L,L], V_+>=v_L=(r-1)a^2 sech^2(ra L)>0. Also

    ||u||_L2(I)^2 <=2||y'||_2^2+2a^2||y||_L2(I)^2
                  <=(2/a^2+2/v_L) q_h[u].

Consequently

    q_h[u]>=c_L ||u||_L2(I)^2,
    c_L=a^2/[2(1+a^2/v_L)]>0.

This pays the local coercivity needed at the continuous-spectrum threshold; a mere positive spectral gap for h on phi-perp would be false.

### 3. Any second eigenvalue is of order e^4

Restrict the form of H_e to the codimension-one space u perpendicular to phi in the first channel. With M=||theta||_infinity and w_max=(r+1)a^2, the positive first diagonal perturbation may be discarded. Since theta is supported on I,

    q_e[u,v]>=q_h[u]+||v'||_2^2
                -e^2 w_max M^2 ||v||_L2(I)^2
                -2|e| w_max M ||u||_L2(I)||v||_L2(I).

Young's inequality and the preceding local coercivity give

    q_e[u,v]>= (1/2)q_h[u]+||v'||_2^2
                         -e^2 B ||v||_L2(I)^2,
    B=w_max M^2+2w_max^2 M^2/c_L.

For a scalar v in H^1(R), ||v||_infinity^2<=||v||_2||v'||_2. Completing a square therefore bounds the last two terms from below by

    -e^4 B^2 L^2 ||v||_2^2.

The codimension-one min-max principle implies lambda_2(H_e)>=-e^4 B^2 L^2 whenever a second negative eigenvalue exists. Moreover 0<=W_e<=w I_2, hence H_e>=h direct-sum h. The latter has exactly two negative eigenvalues, so H_e has at most two. Thus every negative eigenvalue besides the isolated branch contributes in total at most

    B^(2 gamma) L^(2 gamma) |e|^(4 gamma).

This also handles the case when the second eigenvalue does not exist, by assigning its negative moment zero.

The equality value C_gamma integral tr(W_e^p)=a^(2 gamma), the even ground-state expansion, and this threshold bound now give the displayed full-deficit expansion. Since min(4,4 gamma)>2, the error is o(e^2).

### 4. Variational formula and explicit variance bounds

The positive free resolvent gives the exact minimization identity

    Q(theta)=inf_{f in H^1(R)} integral
       [|f'|^2+a^2 |f|^2-2w theta phi f+w theta^2 phi^2].

The minimum is attained at f=(-d^2/dx^2+a^2)^(-1)(w theta phi); real data allow real f. Write f=phi g. Integration by parts, using phi''=(a^2-w)phi, yields

    Q(theta)=min_g [integral phi^2 |g'|^2
                        +integral w phi^2 |g-theta|^2].

The minimizer decays like phi outside I, so this integration and the weighted form limits are legitimate. Taking g constant proves Q<=V.

Normalize rho=phi^2 to mass one. The spectral gap of h+a^2 above its ground state is at least a^2, as shown by the factorization. Its ground-state transform gives

    integral rho |g-E_rho g|^2 <=a^(-2) integral rho |g'|^2.

Let c=E_rho g. By the triangle inequality in L2(w rho), w<=w_max, and the last display,

    V(theta) <= integral w rho |theta-c|^2
      <= [sqrt(integral w rho |theta-g|^2)
                 +sqrt((w_max/a^2) integral rho |g'|^2)]^2
      <= (1+w_max/a^2) Q(theta)=(r+2)Q(theta).

This proves the lower bound. The weight w rho is strictly positive everywhere; its weighted variance vanishes only for an almost-everywhere constant theta. A compactly supported nonzero theta is not such a constant.

## Counterexample pressure and limits

- Global constant rotations must give zero, and both Q and V vanish for them.
- A spectral gap at zero is not assumed; the explicit supersymmetric local estimate supplies the missing threshold control.
- The second negative eigenvalue cannot be discarded merely because H_0 has one. Its possible contribution is bounded by O(|e|^(4 gamma)), essential when gamma approaches 1/2.
- The strict endpoint restriction gamma>1/2 is used both in r>1 local coercivity and in 4 gamma>2. No endpoint conclusion is asserted.
- No uniform remainder over all angular profiles, multiple initially occupied channels, or growing matrix size is claimed.
- This does not yet imply a global distance-to-all-optimizers estimate. The result is a fixed-profile transverse second variation with explicit coercivity of its quadratic form.

## Primary prior-art screen

[Carlen–Frank–Lieb, arXiv:1301.5032v2](https://arxiv.org/html/1301.5032), Sections 1 and 2.1 (primary lines 35–100), already proves scalar lowest-eigenvalue stability. That known result must not be credited here. Its statement is about a scalar potential and its lowest eigenvalue, not rotating matrix channels or additional threshold eigenvalues.

[Leng, arXiv:2606.03749](https://arxiv.org/html/2606.03749) was located as a density-distance reformulation; only its abstract/metadata have been screened, not its proof. It is not a proof input. A final contribution gate must read the relevant primary statements before assessing overlap.

[MathDB Lieb–Thirring problem](https://mathdb.com/p/405329/lieb-thirring-conjecture) and [one-dimensional problem](https://mathdb.com/p/353885/one-dimensional-lieb-thirring-conjecture) were located in search results. No score or ranking is asserted, and their complete pages were not read.

No independent gate has yet passed. The accepted count remains ten of twenty.
