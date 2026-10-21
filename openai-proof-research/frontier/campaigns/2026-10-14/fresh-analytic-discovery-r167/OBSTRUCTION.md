# r167 — exact near-diagonal calculations, no nominee

The closed calculation in DERIVATION.md needs the square of the Green kernel. Higher Laguerre-renormalized occupation powers require higher even powers. This note computes the distinction instead of merely naming a hard conjecture. It does not assert that the FK ensemble has the bad configurations with a relevant probability, that all its operative probabilistic inputs hold in these examples, or that no new theorem is possible.

## 1. The continuum side already supplies all fixed kernel powers

The source's continuum proof gives, for the actual normalized sqrt(3) sphere, a random C and theta=1/56>0 with mu(B(x,r))<=C r^theta uniformly in x at small r. For any finite q>=1, dyadic annuli give

    sup_x integral_{rho(x,y)<delta} |log rho(x,y)|^q mu(dy)
       <= C_q delta^theta(1+|log delta|^q).            (1)

Indeed sum over radii 2^-j delta; the summand is bounded by C(2^-j delta)^theta (|log delta|+(j+1)log2)^q. The geometric series with polynomial weight converges. Centering G in both variables only adds bounded functions by the same estimate for q=1. Thus G_mu is in every finite Lq(mu x mu), with uniformly square-integrable rows.

For the killed Brownian covariance the exact identity is

    C_a = a^-1 Pi+2K-4a K(I+2aK)^-1K.                (2)

The last term has kernel bounded in absolute value by

    4a ||k(x,.)||_2 ||k(y,.)||_2,

because the intervening resolvent is a contraction. It is uniformly bounded. Consequently c_a(x,y)=2G_mu(x,y)+O_a(1), almost everywhere, with a random uniform bound. All its finite powers are integrable too. This also explains why continuum existence of higher Wick fields is not the missing discrete estimate.

This is the same dyadic operation actually read in Maillard–Rhodes–Vargas–Zeitouni, arXiv:1406.0491v4, Lemma3.1 and its proof. That paper's setting there is a log-correlated field on a torus, not the three-mark quantum sphere. The source supplies the sphere ball estimate; the displayed elementary summation transports the operation without importing an incorrect field law. Their Theorem3.3 further gives a continuum eigenvalue bound n^(1-delta) from diagonal heat-kernel control. A stronger continuum tail does not upgrade a uniform discrete tail near its diagonal.

For Gaussian spectral cutoffs, a local fourth Wick power has variance 4! integral f(x)f(y)c_a(x,y)^4 mu(dx)mu(dy). Le Jan's loop occupation polynomial of order2 has instead coefficient alpha(alpha+1)/2 multiplying c_a^4. The finite Laguerre identities eliminate all diagonal self-contractions, but they do not eliminate this cross-point fourth power. Section10 of the primary proof makes exactly this distinction: after algebraic cancellation it estimates collision integrals with the logarithmic kernel and circle-averaging bounds. Those bounds need a discrete counterpart for unsmoothed vertex fields.

## 2. A rank-one diagnostic, with every exponent explicit

Let A_epsilon subset[0,1] have Lebesgue mass epsilon and put phi=1_A-epsilon. For 0<r<1 let

    D_epsilon(t,u)=epsilon^-r phi(t)phi(u).

It is a positive, centered rank-one covariance. Its operator/HS norm is epsilon^(1-r)(1-epsilon), which tends to zero. But

    integral |D_epsilon|^q >= epsilon^(2-rq)(1-epsilon)^(2q).

For q>2, choose 2/q<r<1; the qth moment diverges. If A_epsilon shrinks toward one fixed location, double differences at four pairwise distinct limiting positions tend to zero: at most one of the four coordinates is in A eventually, and all entries involving a coordinate outside A are O(epsilon^(1-r)). Hence even that distinct-limit observation does not detect the concentrated power.

Similarly, epsilon=exp(-m) and coefficient m^2 give HS norm m^2 exp(-m)->0 but

    integral_{A x A} exp(beta^2 m^2 phi(t)phi(u))dtdu
        =exp(-2m+beta^2 m^2(1-exp(-m))^2)->infinity

for every fixed beta nonzero. This is only an operator diagnostic: arbitrary positive covariance perturbations need not be inverse Markov generators. The next calculation removes that particular objection.

## 3. A unit-conductance planar Markov example

Take a star with N leaves and attach to its center a simple path of L edges. All edges have conductance1; loops are unnecessary. Let n=N+L, mu(v)=deg(v)/(2n), A=n(I-P), B=2A. Choose

    L=floor(N^r),             1/3<r<1/2.             (3)

This is a connected planar multigraph within the deterministic network category, although it is not sampled from the FK law and its limiting geometry is not a quantum sphere. We prove three features: vanishing centered HS inverse, the same type of polynomial spectral/energy control, and a diverging fourth killed-kernel integral.

### 3.1 Exact centered Gaussian representation and HS bound

For any finite unit network, pin a Gaussian field to zero at the attachment vertex, give it covariance the inverse grounded graph Laplacian, then subtract its mu average. Its covariance kernel relative to mu is precisely B^dagger: its columns solve Q k(.,y)=delta_y-mu, and are mu-centered. Here Q is the unweighted graph Laplacian, B=M_mu^-1 Q. This identity fixes the normalization without appealing to asymptotic Gaussian physics.

For the base star, write X for its mu_0-centered field, mu_0=deg/(2N). Its centered raw inverse eigenvalues are 1/(2N) with multiplicity N-1 and 1/(4N) once. Hence

    ||K_0||_S2^2=(N-1)/(4N^2)+1/(16N^2)->0.

Its center variance is v=1/(4N): pinning the center makes the N leaf values independent N(0,1), and their mu_0 average is (1/(2N)) times their sum.

Independently take a unit-variance Gaussian random walk S_j on the added path, S_0=0. Extend X along the path by X_root. The full pinned-edge Gaussian field is the extended X plus S, with S zero on the base. Centering with respect to the new degree measure is the only remaining operation.

Put e=L/n and epsilon=(L-1/2)/n=mu(path vertices). The new mu-average of the extended X is exactly e X_root: the base measure is (N/n)mu_0+(1/(2n))delta_root. Thus the centered base part is Xtilde+X_root h, where Xtilde=X on the base, zero on the path, h=-e on the base and h=1-e on the path. In particular ||h||_L2(mu)^2<=2epsilon for large N. Let g be Cov(Xtilde,X_root). The covariance correction has the exact rank-two expression

    h tensor g + g tensor h + v h tensor h.         (4)

Cauchy–Schwarz bounds ||g||_2^2 by v E||Xtilde||_2^2=O(1/N); the latter expected norm is bounded for a star. Therefore (4) has HS norm O(sqrt(epsilon/N)+epsilon/N). The covariance of Xtilde itself has HS norm O(N^-1/2): changing the base measure multiplies its density by a factor bounded by2, and the path-zero extension contributes nothing.

For the independent path part, let W=integral S dmu. Its centered covariance is positive. Its trace is

    E ||S-W||_L2(mu)^2 <= E ||S||_L2(mu)^2
          =sum_{j=1}^L mu(j)j <= L^2/n.             (5)

A positive trace-class operator has HS norm at most its trace. Equations(3)–(5) prove

    ||K_n||_S2 <= O(N^-1/2)+O(sqrt(epsilon/N))+L^2/n ->0. (6)

For every fixed a>0, (1) of DERIVATION.md consequently gives

    ||C_{n,a}-a^-1 Pi||_S2 ->0.                      (7)

The limit is the killed resolvent of the one-point conservative Markov process. Thus this is a genuine sequence of Markov covariances, not just positive kernels.

### 3.2 Polynomial spectrum and all-level approximation do not fix it

For any u, subtracting u(root) gives

    Var_mu(u) <= integral |u-u(root)|^2 dmu
          <= C (L^2/n) sum_edges (du)^2.             (8)

The leaf terms cost at most E/(2n). On the path, |u(j)-u(0)|^2<=j E_path, which proves (8). The first positive raw eigenvalue is therefore at least c n/L^2 ->infinity.

Impose u(root)=0, a codimension-one constraint. The star-leaf restricted eigenvalues are 2n. The path Dirichlet-at-root/free-at-tip eigenvalues are bounded below by c n k^2/L^2, 1<=k<=L, from the elementary discrete sine basis (the tip mass differs from interior mass by a fixed factor only). Codimension-one min–max interlacing, with (8) for the first positive eigenvalue, yields a uniform lower bound

    nu_{n,i} >= c i^p,       p=7/10, i>=1,           (9)

with padding by infinity. To check the ranges explicitly: until the path modes reach order n, n(i-1)^2/L^2 dominates i^p since n/L^2>=1; subsequently the eigenvalues are at least c n and i<=n+1. The fixed first indices use (8).

There is also a direct analogue of the all-level energy approximation. For rank budget k<=n, use one constant value on all star vertices and divide the path into at most k consecutive blocks. The best L2 projection onto this subspace has error no larger than the test approximant using u(root) on the star and block averages on the path. Discrete one-dimensional Poincare gives

    ||u-Q_k u||_2^2 <= C [n^-1 + L^2/(n k^2)] E(u)
                    <= C' k^-p E(u),               (10)

when k<=L; for k>L use individual path vertices, leaving only the n^-1 term. When k exceeds the dimension take the identity. Rank is at most k+1. The ceiling in block lengths changes only C. Thus setting k=2^j gives the same form of all-level rank/error inequality as the source. No eigenvalue or rank-tail improvement alone is a local covariance-power bound.

### 3.3 The fourth kernel moment really diverges

Kill additionally at the root and restrict to the path. Killing paths earlier can only decrease the positive resolvent kernel, so the full c_{n,a} dominates this restricted kernel. Without rate-a killing, the Brownian-clock path Green kernel is exactly

    d_0(i,j)=2 min(i,j),   1<=i,j<=L.                (11)

Indeed the grounded raw Laplacian inverse is min(i,j), while A has half the raw energy. Adding killing gives the resolvent identity in the path degree measure

    d_a=d_0-a d_0 d_a,
    0<=d_a<=d_0.

Consequently, pointwise,

    0<=d_0(i,j)-d_a(i,j)
       <=a sum_k mu(k)d_0(i,k)d_0(k,j)
       <=4a L^3/n.                                 (12)

For i,j>=ceil(L/2), (11) is at least L. Since L^2/n->0, (12) is at most L/2 eventually. The upper half of the path has mu mass at least cL/n. Therefore for every q>0,

    integral c_{n,a}(x,y)^q mu(dx)mu(dy)
          >= c_q L^(q+2)/n^2.                       (13)

At q=4 this tends to infinity by r>1/3, whereas (6) holds by r<1/2. For example r=2/5 gives a fourth-moment lower bound of order N^(2/5), while the path's HS bound in (5) is N^(-1/5). No sign cancellation or diagonal value convention is involved: (13) uses two sets of vertices of positive mass and a positive killed kernel.

## 4. Relation to the actual source, and exact unpaid operation

This network example does not have the source's random surface law, local conditional laws, or nondegenerate sphere limit. It is not a refutation of any stipulated theorem. Its purpose is narrower and fully explicit: the HS convergence, polynomial eigenvalue control and all-level energy approximation used in the closed quadratic-field argument do not themselves imply fourth-kernel uniform integrability, even for planar unit-conductance networks with the exact degree measure and clock.

Appending a path to any base network also has an exact electrical observation useful for interpreting the source's four-point statement. Effective resistances between base vertices are unchanged; resistance from path vertex j to base vertex y is j+R_base(root,y). For a four-point voltage combination involving at most one added-path vertex, the extra j cancels. If an attached path is spatially collapsed to its root, four pairwise DISTINCT limiting positions can involve at most one point from it. Thus the distinct-limit voltage observation alone cannot see its long internal resistance. This is an exact cancellation, not a claim that all other source hypotheses survive an arbitrary graft.

The source's Section5 proves more than a spectral bound: it constructs common finite-rank approximations, boundary-only oscillation estimates and path support packings. In its quantitative step, pointwise boundary oscillation is allowed to grow like exp(N/10) sqrt(E), while the mass of an address block is on the scale exp(-N). Squaring first and averaging is precisely what permits the HS/energy compactness argument. It is not a logarithmic pointwise Green majorant, and its proof does not assert one. The strong local harmonic and voltage limits in Sections4,6,7 have fixed spatial buffers before the discrete threshold; they cannot be evaluated at a shrinking, map-dependent buffer by merely changing quantifiers.

A concrete sufficient bridge for order2 renormalized occupation powers would include convergence off the spatial diagonal of the relevant uncentered or correctly centered killed kernels, together with uniform integrability of |c_{n,a}|^4 under mu_n tensor mu_n (and mixed regularization kernels for a constructive coupling). Equivalent direct L2 Cauchy estimates for the Laguerre fields would also suffice. Higher fixed orders require their corresponding collision bounds. No such estimate is proved for FK–Ising here. The continuum logarithmic bound (1), the source's square-integrable inverse convergence, or an unspecified slowly varying smoothing scale cannot replace it.

This is not a new candidate statement or a narrowing of an old target. The entire developed work stays PREFREEZE. It retains the closed quadratic construction and a finite-network explanation of the next unpaid operation, without claiming an exhaustion of the family.
