# Prefreeze derivation: full spectral density and multiscale matrix solitons

No theorem is frozen or nominated. The source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true. The calculations below investigate a full stability operation; they are not independent correctness/contribution grades or supporting replacement nominees.

## 1. The question, and the actual old work

For 1/2<gamma<3/2 write sigma=gamma-1/2, p=1+sigma, r=1/sigma, q=r+1. Source262 supplies

    S_gamma(W)=Tr(-d²/dx² I_m-W)_-^gamma
       <= C_gamma int tr W^p,
    C_gamma=((gamma-1/2)/(gamma+1/2))^(gamma-1/2)
             Gamma(gamma+1)/(sqrt(pi) Gamma(gamma+3/2)).

Its exact equality class consists of a constant unitary conjugate of scalar solitons

    w_(a,b)(x)=(r+1)a² sech²(ra(x-b)),

in mutually orthogonal channels, with independent positive scales and real centers. Zero channels are allowed. This is for arbitrary finite m and measurable Hermitian W>=0 with finite trace-power integral. The full negative spectrum, including multiplicities and possible accumulation at zero, is included.

The feasibility question is whether small normalized FULL deficit forces small Lp(Sp) distance from sums

    sum_(j=1)^J w_(a_j,b_j) P_j,                         (1)

where J is arbitrary finite with NO uniform budget and P_j are constant rank-one orthogonal projections individually, but need not be mutually orthogonal. This union includes separated bubbles occupying the same channel. One would seek a modulus depending only on gamma, uniformly over all finite m and all W with int tr W^p=1. This is a question under investigation, not a frozen statement, a literature-open designation or a result. No quantitative modulus has been established here.

Actual history prohibits several misleading replacements. I38 section1.2 proves that distance to the exact equality class does not vanish even for a scalar two-bump sequence. Arithmetic r30's finite-bubble-obstruction gives the full k-versus-K distance limit and excludes any finite-valued budget K(delta). I250/I259/I262/I264/I271 already develop transverse Hessians, local and global orientation stability for a fixed scalar profile; their strong Feshbach, threshold, weighted interpolation and exponent-comparison operations are credited. The frozen P3R statement concerns an exact three-well phase asymptotic and every R, and is untouched. None of those questions is reopened or narrowed here.

The late r118 HANDOFF navigation hit states that an exact infinite-channel equality extension was already reduced using operator-norm tails and Schatten duality. Its operative bodies are behind packet/work exclusions and were not read. That navigation is not a premise or an authenticated proof read. In particular this round does not assert a new exact infinite-dimensional equality theorem or clearance from that history.

## 2. Retain the strongest source action comparison

Put D_sigma=sigma^sigma/(1+sigma)^(1+sigma), b_sigma=int_(-1)^1(1-t²)^sigma dt, so C_gamma=D_sigma/b_sigma. For normalized W, list its binding parameters k_i decreasingly, with eigenvalues -k_i². Given a finite initial list, approximate its eigenfunctions by compactly supported orthonormal rows U with form matrix <=-K², where K uses a common arbitrarily small square-energy shift.

The equality manuscript's act:quantitative-action produces a lower triangular C and symmetric path B, with A=CU, |B|op<=kappa, and a first-order plus truncated algebraic defect. The triangular spectral inequality supplies the additional nonnegative term

    T=sum_(l<=i) |C_il|²(k_l²-k_i²).

Writing Z=A* A and

    Y(W,Z)=D_sigma tr W^p-tr(WZ)+tr Z^q,

the COMPLETE compatible comparison gives, with trial errors made arbitrarily small,

    T + int [Y(W,Z)+|A'-BA|_HS²+c_* Phi_K(A,B)]
       <= b_sigma(Delta_gamma(W)+sum_(i>N)k_i^(2gamma)) + o(1), (2)

where Delta_gamma=C_gamma-S_gamma and

    Phi_K=min{1, |[B,K²]|op²+|K²-B²-(AA*)^r|op²}.

For real potentials this is exactly the source's comp:triangular-gap/vanishing-errors argument, with a nonzero spectral deficit retained. Realification supplies the corresponding complex version with the usual factor two; no separate complex path theorem is assumed. Since k_1^(2gamma)<=C_gamma, kappa may be chosen depending only on gamma. Thus c_* is independent of m,N and the smallest retained energy. The field, parity continuation, penalty, full matrix trace remainder, and all spectral approximations are paid source operations, not proposed findings.

In exact equality the source controls omitted row Hilbert--Schmidt norm by m times an operator-norm tail. Its proof fixes W, its physical dimension and its eigenfunctions. This particular bound is not uniform in a sequence of arbitrary m. That observation alone is not an unpaid-operation certificate: the next two reductions bypass parts of it.

## 3. Matrix Young reconstruction is already paid

Carlen, arXiv:1605.04581v1, Theorem1.1 and its proof give, for positive normalized matrices X in Sp and Z in Sq,

    1-tr(XZ) >= (p-1)/4 |X-Z^(q-1)|p²,   1<p<=2.       (3)

For matrix-valued simple functions the SAME inequality follows by putting the matrices on weighted block diagonals, with factors mu_j^(1/p) and mu_j^(1/q). Approximation in Lp(Sp) and Lq(Sq) gives the integrated version. In passing from simple functions, one can first prove the midpoint uniform-convexity inequality on block diagonals and then repeat Carlen's duality argument in the Banach space; no unproved continuity estimate for a noncommutative power map is needed. The dual optimizer of positive Z is Z^(q-1)/||Z||q^(q-1), as follows directly from trace Holder. This is a classical extension, not a new theorem.

Suppose ||W||Lp(Sp)=1 and e=int Y(W,Z). Set s=||Z||Lq(Sq) and s0=q^(-1/(q-1)). Then

    e=[D_sigma-s+s^q] + [s-int tr WZ].                  (4)

Each bracket is nonnegative. The first function has its unique minimum zero at s0. If e is smaller than half the minimum of its values at s0/2 and 2s0, then s0/2<s<2s0. Its second derivative on that interval is at least

    M=q(q-1)(s0/2)^(q-2)>0,

so |s-s0|<=sqrt(2e/M). Applying (3) to W and Z/s gives

    ||W-(Z/s)^r||Lp(Sp) <= sqrt(4e/((p-1)s)).           (5)

Since ||(Z/s)^r||p=1 and q s0^r=1,

    ||W-qZ^r||Lp(Sp)
       <= sqrt(8e/((p-1)s0))
          +q r (2s0)^(r-1) sqrt(2e/M).                (6)

All constants are independent of matrix size and row count. Thus the Young defect in (2) really DOES control physical-potential distance to the reconstructed density power. It cannot honestly be described as only an auxiliary algebraic defect with no potential consequence. But (6) alone does not identify qZ^r as a sum of solitons.

For fixed N, the elementary bound (tr Z)^q<=N^(q-1)tr Z^q uses rank Z<=N. On a bounded interval this and A'=BA+error provide local H1 bounds for N Hilbert-valued rows. Piecewise averages approximate them uniformly in L2, with error bounded by the mesh size times their derivative norm. Finitely many averages have a bounded Gram matrix; after taking a subsequence, square roots of those finite Gram matrices give convergence modulo a constant isometry into a common Hilbert space. A diagonal mesh/interval construction gives local compactness modulo constant isometries for fixed N. This standard finite-sample argument pays physical-channel escape at fixed spectral rank. It does not give a bound independent of N, global tightness, or a full bubble theorem.

## 4. The stronger full-spectrum reduction at gamma=1

It would be premature to call the tail in (2) the final obstruction. Read--Schulz arXiv:2609.10478v2 gives a sharp kinetic inequality for orthonormal Hilbert-valued families, with

    K=pi²/4,
    sum_(j=1)^N int |psi_j'|² >= K int tr R_N³,
    R_N(x)=sum_(j=1)^N psi_j(x)psi_j(x)*.               (7)

Its actual vector proof, not just its title, was read: cumulative matrix mass, basis-independent differentiation, completion of squares, positive fourth-power representation, weighted kernel estimate, and alpha-up-to-pi limit. This supplies a stronger compatible route at gamma=1. That exponent is a diagnostic part of the same full family question, not a nominated restricted replacement.

Fix finite m and W>=0 with int tr W^(3/2)=1. Let psi_j be ALL negative eigenfunctions, orthonormal including multiplicity, and let

    S_N=sum_(j<=N)|lambda_j|,
    T_N=sum_(j<=N)int|psi_j'|²,
    s_N=(int tr R_N³)^(1/3).

The eigenfunction form equations and Holder give

    T_N+S_N=int tr WR_N<=s_N,
    T_N>=K s_N³.

Hence s_N<=K^(-1/2) and T_N<=K^(-1/2). The latter is a bound for the total derivative energy, not a bound on N or on total L2 particle number.

The positive matrices R_N increase. Monotone eigenvalue convergence and the L3 trace bound give a finite positive matrix limit R(x) almost everywhere, for fixed finite m. Moreover 0<=R-R_N<=R and eigenvalue monotonicity imply tr(R-R_N)³<=tr R³. Dominated convergence gives R_N->R in L3(S3). The nonnegative sums T_N converge to finite T, and S_N converge to S by the stipulated spectral bound (or the preceding bounds). Holder passes the potential pairing to the limit. Thus

    T+S=int tr WR,
    T>=K int tr R³.

With C=C_1=4/(3sqrt(3)pi) and Delta=C-S, the EXACT full identity is

    Delta = E_kin + E_Young,
    E_kin=T-K int tr R³ >=0,
    E_Young=C-int tr WR+K int tr R³ >=0.                (8)

No negative eigenvalue or emerging threshold state is omitted. Infinite negative lists are allowed. This is primary kinetic duality plus monotone convergence, not an additional substantial finding.

The integrated matrix Holder estimate makes (8) quantitative. Set s=||R||3 and s0=(3K)^(-1/2)=2/(sqrt(3)pi). Then

    E_Young=[C-s+Ks³]+[s-int tr WR].                    (9)

The first bracket has minimum zero at s0. Its value at s0/2 is 5s0/24 and at 2s0 is 4s0/3. If Delta<=5s0/48, then s0/2<s<2s0, and the second derivative is at least 3Ks0 there. Consequently

    |s-s0|<=sqrt(2Delta/(3Ks0)),
    ||W-(R/s)²||_(3/2)<=4 sqrt(Delta/s0).

Using 3Ks0²=1 and the derivative bound 6Ks<=12Ks0 on this interval gives the convenient explicit estimate

    ||W-3K R²||L^(3/2)(S_(3/2))
       <=4(1+sqrt(2)) sqrt(Delta/s0).                  (10)

This displays a fully paid reconstruction bound for the FULL occupied density. It is not a soliton-distance estimate, and is not offered as a substitute nominee.

## 5. Retain the actual primary kinetic remainders as well

For the first N eigenfunctions let U_N have those rows, Q_N=U_N U_N*, and M_N(x)=int_(-infinity)^x Q_N. Then 0<=M_N<=I_N. For 0<alpha<pi, write

    b_alpha(t)=-alpha tan(alpha(t-1/2)).

In an eigenbasis of M_N with eigenvalues mu_i, set

    (B_(alpha,N))_ij=b_alpha((mu_i+mu_j)/2)(Q_N)_ij.

Read--Schulz's vector-chain calculation and boundary limits give the EXACT identity

    T_N-alpha²/4 int tr R_N³
      =int |U_N'-B_(alpha,N)U_N/2|_HS²
         +(1/4)int G_(alpha,N).                       (11)

The actual proof makes G nonnegative by representing its scalar kernel as a positive sum of fourth powers of coordinate differences. For one such term, if C>=0 and K_ij=(sigma_i-sigma_j)² C_ij, its matrix sum is 2 tr(CK²)>=0. This is an exact noncommutative operation already paid by the primary proof; one must not replace it by a scalar pointwise sign argument for triple matrix entries.

As N exhausts the negative list, the left side of (11) tends to

    E_kin+(pi²-alpha²)/4 int tr R³.

The last integral is bounded independently of m and N. Thus near equality forces both primary remainders to be small in the successive N limit and alpha-to-pi limit. These are stronger data than bare nonnegativity of (7). An argument which discards them and merely declares stability unpaid would under-credit the available composition.

What they do not yet provide here is uniform physical reconstruction into (1). The bounded b_alpha blows up as alpha approaches pi near cumulative eigenvalues 0 and 1. A naive unweighted Gronwall estimate for the first-order square therefore has deteriorating constants. Exact solitons balance this singularity with a vanishing density, so blowup of the naive estimate is not an impossibility proof. A weighted conversion retaining that balance, including coalescing energies and variable multiplicities, has not been obtained.

## 6. Pay the ordinary spatial and internal localization calculations

FGL2109.05984v2 Theorem1 has a COMPLETE fixed-N bubble proof: IMS decouples spectra across low-mass annuli; localization of eigenfunctions away from threshold gives tightness; weak convergence plus equality of norms gives strong Lp convergence; a strictly decreasing integer spectral rank terminates extraction. These operations are credited at their actual strength. The proof has no gamma>3/2 restriction for its bubble theorem; that restriction belongs to its later strict-binding/compactness theorem. Under the stipulated sharp scalar constant and equality classification, applying FGL at fixed N is a compatible source/classical composition. It is not a new substantial result.

For scalar smooth cutoffs with sum chi_j²=1, summing the exact IMS identity over occupied states gives the error

    int (sum_j|chi_j'|²) tr R.                         (12)

For fixed N this is bounded by N times the squared gradient bound. The full-density estimates give int tr R³, not int tr R; the latter is the number of occupied states and may be infinite.

An exact optimizer shows why fixed physical scales cannot silently fix this. At gamma=1 take

    W_m(x)=3a² sech²(2ax) I_m,
    a=(C/m)^(1/2),
    R_m(x)=(2a/pi)sech(2ax) I_m.                      (13)

Then int tr W_m^(3/2)=1, Delta=0, int tr R_m=m, and W_m=3K R_m². For any nonconstant compactly supported smooth cutoff chi, (12) equals

    (2ma/pi) int |chi'|² sech(2ax),

which grows as a positive constant times sqrt(m). A length L=R/a, followed by R->infinity, does control this particular example; it is already a sum of m exact solitons. Thus (13) refutes an unweighted fixed-scale localization estimate, NOT the unrestricted approximation question. A successful method must adapt to binding scale and multiplicity.

Nor can internal spectral localization be treated as cost-free scalar IMS. Let V(x)u=(chi_j(x)u)_j be a differentiable isometry, so sum chi_j*chi_j=I. Put A=V*V'; differentiating V*V=I gives A*=-A. Direct expansion gives

    sum_j |(chi_j u)'|²
      =|u'+A u|²+<u,V'^*(I-VV*)V' u>.                 (14)

The second term is nonnegative, and the connection A need not vanish. Also sum chi_j*Wchi_j equals W only with an additional compatibility condition, for example a complete spectral-projector partition commuting with W. A local unitary gauge can remove A on the line but rotates the potential; it does not produce fixed physical soliton channels for free. Coalescing spectral clusters also prevent uniform estimates based on an assumed inverse gap. Formula (14) is ordinary product and Gram algebra. It is not another rotating-channel theorem or a retry of I250--I271.

## 7. Precise remaining operation and outcome

The strongest integrated reductions pay source action/trace/current coefficient selection, dimension-independent matrix Young reconstruction, fixed-N compactness modulo constant channel isometries, actual primary fixed-N bubble extraction, and at gamma1 the full occupied-density identity with all kinetic remainders retained. No completed nonroutine operation beyond those compositions was found.

To answer the full feasibility question affirmatively one still needs a construction or estimate converting these full-deficit data into an unrestricted finite soliton sum with vanishing Lp(Sp) error, uniformly in physical dimension, spectral multiplicity, arbitrary centers, and arbitrary positive scales. This requires error accounting across space, energy scale and internal subspace that retains all spectral mass, controls (12)/(14), and handles the endpoint balance in (11). It cannot be replaced by a finite budget, a fixed spectral cutoff, a variable-profile assumption, or the existing fixed-profile orientation theorem. No such conversion is proved here. Conversely, none of the diagnostic failures refutes that conversion.

PREFREEZE / NO NOMINEE. These are durable mathematical reductions with explicit limits, not a claimed new theorem, exhaustive obstruction, literature-priority claim, contribution verdict or acceptance. All protected old scopes and dispositions remain unchanged.
