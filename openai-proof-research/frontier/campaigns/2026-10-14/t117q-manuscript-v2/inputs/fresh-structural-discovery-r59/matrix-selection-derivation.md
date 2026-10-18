> Historical pre-freeze working note. Final status and complete proof are in checkpoint.md and candidate.md; the original exploration is retained below.

# Matrix chart-selection construction (pre-freeze derivation)

This records the concrete construction before a theorem scope is frozen. Full source parameter compatibility, strongest primary/history comparison and final proof remain to be completed.

## Operator Gaussian moment lemma

Let X_1,...,X_m be selfadjoint operators on a finite-dimensional complex Hilbert space H, with sum_j X_j^2 <= I. For independent standard real Gaussians g_j put G=sum_j g_j X_j. Then

    0 <= E G^(2q) <= (2q-1)!! I,    q>=1.

Here is a dimension-free proof distinct from invoking a trace Khintchine inequality. Expand by Wick's formula. Fix any pairing of the 2q positions. Scan its positions in reverse order, keeping one index register C^m for each currently open pair, and an H register. On opening a pair, apply the column contraction V:h -> sum_j e_j tensor X_j h to H and retain all existing registers. On closing a pair, move its register adjacent to H by a unitary permutation of tensor factors and apply V*:sum_j e_j tensor h_j -> sum_j X_j h_j; retain all other registers. V*V=sum_j X_j^2<=I. Each operation is contractive, and all registers have been removed at the end. Expanding its action shows that the resulting operator is exactly the sum of words indexed by this pairing. It has norm at most1. There are (2q-1)!! pairings. Since E G^(2q) is positive, its norm bound is the stated Loewner bound. The Wick identity itself is a standard Gaussian identity, not a new contribution.

## From moments to charts

Write Z_si=sum_j u_sij X_j. Suppose the directions satisfy, uniformly for every such tuple and every matrix dimension,

    (SN)^-1 sum_si Z_si^(2q) <= (Cq/m)^q I.

Set Q_s=(sum_i Z_si^(2q))^(1/q), a positive operator. Operator concavity of t^(1/q) implies

    S^-1 sum_s Q_s <= N^(1/q) Cq/m I.

For q>=log N, choose threshold h=2e Cq/m and let P_s be the spectral projection of Q_s on [0,h]. Then I-P_s<=Q_s/h, so sum_s P_s >= S I/2. Moreover Z_si^(2q)<=Q_s^q and operator monotonicity of t^(1/q) gives Z_si^2<=Q_s. Consequently ||Z_si P_s||<=sqrt(h).

## Positive Gaussian dual pairing

For selfadjoint A_j let A(g)=sum_j g_j A_j, U(g)=sign(A(g)), and X_j=E[g_j U(g)]. Bessel's inequality in L2(Gaussian;H), applied to U(g)v, gives sum_j ||X_j v||^2 <= E||U(g)v||^2 <=||v||^2. Thus X_j are selfadjoint and sum_j X_j^2<=I. Crucially,

    Y=sum_j A_j X_j=E[A(g) sign(A(g))]=E|A(g)| >=0,
    Tr Y=E||A(g)||_1.

Suppose every chart has A_s=sum_i u_si tensor b_si with ||b_si||_1<=t, and sum_j ||A_sj-A_j||_1<=e. Then

    (S/2) Tr Y <= sum_s Tr(Y P_s)
      = sum_si Tr(b_si Z_si P_s) + errors
      <= SNt sqrt(h) + S e,

because ||X_j P_s||<=1. Hence E||A(g)||_1 <=2Nt sqrt(h)+2e. This is the proposed new simultaneous-chart operation. General matrices can be replaced by their Hermitian block dilations, with the standard factor2 cancelled on both sides.

## Finite universal moment construction

Take N=m^6, q=ceil(log N), S=m^(10q). Independently sample all SN standard Gaussian vectors, with u=g/sqrt m. Match all ordered scalar monomials of degree2q to accuracy m^(-3q). After truncating at ||g||<=2sqrt m, each is bounded by (2sqrt m)^(2q). Hoeffding and union bound over m^(2q) words give the required matching with probability tending to1. The truncation bias is exponentially small in m, times m^O(q), so is below this tolerance for q=O(log m). Expanding the matrix polynomial introduces at most m^(2q) coefficient errors, and each ||X_j||<=1. After the m^(-q) normalization the total operator error is at most m^(-2q). The Gaussian lemma then implies the displayed uniform matrix moment bound with an absolute C. This is uniform in matrix dimension because the matching is at the scalar coefficient level.

All source per-chart Gaussian concentration events still hold: log S=O((log m)^2), whereas their failure estimates have exponents of order m or m^4. The scalar majority-good-chart event is also available if desired; the matrix proof does not use it.

## Parameter issue that must not be suppressed

Source kernel.tex has Fourier mass epsilon*S*N and preliminary extension amplitude epsilon^(-1/2). Thus enlarging S cannot retain epsilon=m^-200 and tau=m^-2000 unchanged. One can contemplate epsilon=m^-200/S and tau=m^-2000/S^C0 for fixed sufficiently large C0. Hilbert derivative bounds grow by a polynomial factor in S, so the smaller mesh is necessary. This changes log(1/tau) to O((log m)^2), log|V| to O(m(log m)^2), and the triangle-repair logarithm to O((log m)^2). The prospective contraction is C sqrt(m)(log m)^(7/2), yielding a near-square-root finite-size lower bound with (loglog n)^(9/2) loss. This compatibility still requires full written estimates; no theorem is asserted here.
