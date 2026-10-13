# I266 contribution analysis of the authenticated I264

Verdict: **TECHNICAL**. This is a contribution assessment, not a PASS for I264's displayed proof or radius. All pinned OpenAI results are stipulated true. I265 was not read. I250/I259/I262/I264 remain one chain and one prospective finding.

## The earlier objection fails at its original exponent

I261's decisive objection must be retained in full. For the compressed potential

    U_f=B_w w ff^T,  p=gamma+1/2,  M=||f||_infinity,

the SAME-EXPONENT stipulated matrix LT theorem gives

    S_gamma <= C_gamma B_w^p integral w^p |f|^(2p)
            <= N_LT M^(2gamma-1) J,
    N_LT=C_gamma B_w^p kappa,  kappa=w0^(1/r)/c^2.

For I262, M tends to zero, so this already closes comparability at a changed radius; HLW improves a rate but is not indispensable. Covariance centering, factorization and local perturbation were judged a useful technical synthesis, without a published duplicate or proof defect being identified.

For I264, M can be one at every positive J. If |f|^2 is an indicator, integral w^p |f|^(2p)=kappa J exactly. Thus this estimate is only O(J), and its coefficient cannot be absorbed by decreasing J. Repeating I261's same-exponent argument as though it still supplied o(J) would be incorrect. I264's core and tail examples genuinely expose that failure.

Two different direct comparisons nevertheless close the new scope. The first also removes the need for the proposed nonlinear perturbation machinery.

## An exact ground-energy comparison with no smallness hypothesis

Let h=-d^2-w. The stipulated equality companion, rigidity section, gives a normalized ground state phi at -a^2 and no other negative spectrum. Hence h+a^2 is nonnegative, with kernel span{phi}, and on phi-perp it is at least a^2. The matrix spectral companion justifies the form realizations and discreteness below zero for the bounded measurable potentials considered here.

For any real normalized u in H^1(R;R^m), decompose componentwise

    u=phi b+xi,  b=integral phi u in R^m,
    integral phi xi=0,  |b|^2+||xi||_2^2=1.

Define the two nonnegative quantities

    E=sum_i q_(h+a^2)[u_i]=sum_i q_(h+a^2)[xi_i],
    F=integral w |(I-P)u|^2.

Exactly, not to second order,

    R:=q_(H+a^2)[u]=E+F,   E>=a^2||xi||_2^2.

The definition of J implies for every constant b

    J |b|^2 <= integral w rho |(I-P)b|^2.

Minkowski in L2(w dx), ||I-P||<=1, and w<=w0=(r+1)a^2 give

    sqrt(J)|b|
      <= ||sqrt(w)(I-P)(phi b)||_2
      <= sqrt(F)+sqrt(w0)||xi||_2
      <= sqrt(F)+sqrt(r+1)sqrt(E).

Cauchy--Schwarz in R^2 therefore gives

    J |b|^2 <= (r+2)(E+F)=(r+2)R.

Since |b|^2>=1-R/a^2,

    J(1-R/a^2)<=(r+2)R,
    R >= J/(r+2+J/a^2).                              (A)

This rearrangement is valid even when 1-R/a^2 is negative. Taking the infimum over normalized real u is sufficient because H has real coefficients; equivalently the argument applies separately to the real and imaginary parts. Testing phi e, with e minimizing J (the finite covariance maximizer), gives the converse variational bound. Consequently

    J/(r+2+J/a^2) <= inf spec(H)+a^2 <= J.            (B)

For J<a^2 the test is negative, so inf spec(H)=lambda_1 is an actual negative eigenvalue. For J<=a^2, (B) gives delta=lambda_1+a^2>=J/(r+3). No simplicity, analytic continuation, pointwise chart, exact centering of g, relative-form expansion, integrability of w/rho, or estimate of Q(w|f|^2 phi) is needed to obtain this lower bound. All those couplings are included in the exact nonnegative identity R=E+F. (A)--(B) are a comparison used in this review, not a second spectral nomination.

This is an abstract bounded-profile observation: replace a^2 by a scalar ground-to-complement gap G and w0/a^2 by w0/G in the proof. The mechanism is a Hilbert-space projection and triangle inequality, not a claim that an unread published matrix-stability theorem already exists. Here the requisite gap is supplied explicitly by the stipulated soliton result.

## Compression still needs a threshold-weight estimate

The gap above is for h+a^2, not a positive unweighted gap for h on phi-perp. To compare extra eigenvalues, retain the elementary factorization estimate

    q_h[t]>=c_w integral w|t|^2,  t perpendicular to phi,
    c_w=(r-1)/(2r(r+1)).

Its independent derivation from the read source factorization is as follows. Set A=d/dx+a tanh(ra x), Lplus=-d^2+[(r-1)/(r+1)]w, so A*A=h+a^2 and AA*=a^2+Lplus. For t perpendicular to phi put y=(AA*)^(-1)At; then t=A*y. Bounded coefficients and the elliptic inverse justify these identities first on the form domain; alternatively use a core and closure. Directly,

    q_h[t]=a^2<y,Lplus y>+||Lplus y||_2^2,
    integral w|A*y|^2<=2w0||y'||_2^2+2a^2 integral w|y|^2
      <=[2(r+1)+2(r+1)/(r-1)]q_h[t].

The reciprocal coefficient is c_w. This is the same elementary consequence of the existing explicit partner factorization used in I264.

Choose a constant optimal channel e and write v=(alpha,f) after a measurable sign choice, with alpha>=0, |f|<=1. Only integral w rho|f|^2=J is used below; no mean-zero condition is needed. Compress H to (phi e)-perp. A vector in this space has first component t perpendicular to phi and transverse component z. Expanding the exact quadratic form and using alpha<=1 and Young's inequality,

    2|t||f^T z| <= (c_w/2)|t|^2+(2/c_w)|f^T z|^2,

gives

    q_H[t,z] >= (1/2)q_h[t]+integral |z'|^2
                    -B_w integral w|f^T z|^2,
    B_w=1+2/c_w.

The first block is nonnegative. Codimension-one min--max interlacing and form order compare lambda_(j+1)(H) with lambda_j(K_f), K_f=-d^2 I_(m-1)-B_w w ff^T. Apply the comparison to finite negative lists and then exhaust them. Neither simplicity of lambda_1 nor a finite eigenvalue count is needed.

## The stipulated theorem at a lower exponent gives o(J)

Fix the target gamma and define

    p=gamma+1/2, beta=(gamma-1/2)/(2p)=1/[2(r+1)],
    s=(1/2+gamma/p)/2,
    p_s=s+1/2,
    alpha=s(1+beta)/gamma,
    d=(p_s-alpha p)/(1-alpha).

All are explicit. Since gamma>1/2 and p>1,

    1/2<s<gamma/p<gamma<3/2.

Furthermore alpha<p_s/p<1: indeed alpha<p_s/p is equivalent to sp<gamma for this beta. Thus d>0. Let

    I_d=integral w^d
       =w0^d sqrt(pi) Gamma(d)/[ra Gamma(d+1/2)]<infinity.

For y=|f|^2 in [0,1], use p_s>1 and weighted Holder on y dx:

    integral w^(p_s)y^(p_s)
      <= integral w^(p_s)y
      = integral (w^p y)^alpha (w^d y)^(1-alpha)
      <= (integral w^p y)^alpha (integral w^d y)^(1-alpha)
      <= (kappa J)^alpha I_d^(1-alpha).              (C)

The exact weight identity integral w^p y=kappa J follows from rho=c^2(w/w0)^(1/r) and p=1+1/r. The profile remains the TARGET-gamma soliton. It need not be a soliton or optimizer at s: the stipulated matrix theorem at s applies to every admissible positive matrix potential.

U_f=B_w w ff^T is bounded, measurable, positive, rank at most one, with integrable p_s-th trace power. The fully read matrix main theorem, at s rather than gamma, therefore gives

    Tr(K_f)_-^s <= C_s B_w^(p_s) kappa^alpha I_d^(1-alpha) J^alpha.

For nonnegative eigenvalue magnitudes E_j and q=gamma/s>1,

    sum_j E_j^gamma <= (sum_j E_j^s)^(gamma/s).

This follows first for finite lists from sum x_j^q<=(sum x_j)^q and then by exhaustion. Combining with compression yields

    S_gamma:=sum_(j>=2)|lambda_j(H)|_-^gamma
      <= A_tail J^(1+beta),                         (D)
    A_tail=[C_s B_w^(p_s) kappa^alpha I_d^(1-alpha)]^(gamma/s).

There is no supremum-small factor, support radius, derivative hypothesis or m factor. This matches I264's positive J exponent exactly, without invoking HLW. It is a different argument from I261's failed same-exponent estimate.

More generally the same elementary comparison works for every fixed 0<beta'<(gamma-1/2)/p: choose 1/2<s<gamma/(1+2p beta') and alpha=s(1+beta')/gamma. This interval is nonempty precisely under the displayed bound on beta'. Thus simply promoting I264's intermediate exponent to the contribution would not distinguish it from the already available exponent family. No endpoint or optimal-rate claim is made here.

## Explicit alternate closure of the actual weak-neighborhood theorem

Let m_gamma,M_gamma be exactly the positive mean-value constants defined in I264. Set

    tau_alt=min{Z/4,a^2/8,
                [m_gamma/(2(r+3)A_tail)]^(1/beta)}.

For 0<J<=tau_alt, (B) gives 0<=delta<=J<=a^2/8 and delta>=J/(r+3). Scalar saturation at the target gamma and the mean-value theorem give

    D=a^(2gamma)-(a^2-delta)^gamma-S_gamma,
    D>=m_gamma delta-S_gamma
      >=[m_gamma/(r+3)-A_tail J^beta]J
      >=m_gamma J/[2(r+3)]
      >=m_gamma J/[4(r+2)],
    D<=M_gamma delta<=M_gamma J.

For J=0, P is constant almost everywhere since w rho>0, and scalar equality gives D=0. Thus the same stated c_-,c_+ and an explicit possibly different radius work under weighted smallness alone. This alternate derivation does NOT certify I264's particular displayed tau, Feshbach details or HLW implementation. Those remain the independent I265 gate. It validates a concrete comparison for the contribution judgment.

## Large-angle examples and scope

For v=e2 on A and e1 outside A with integral_A w rho<Z/2, J=integral_A w rho and |f|=1_A. For A=[0,ell], ell decreasing to zero, J and integral_A w are both comparable to ell. For A=[L,L+1], L increasing to infinity, their scales are exp(-2a(r+1)L) and exp(-2raL). In both cases (integral_A w)^(2gamma)=o(J); for the tail case the ratio has order exp(-2aL). These analytic checks from I264 were fully read; they require no numerical experiment. They rule out replacing the hypothesis by essential-supremum smallness and show why the SAME-exponent bound cannot be absorbed. Both (B) and (D) hold uniformly for these examples and for arbitrary mixtures, arbitrary measurable oscillations, and every finite channel dimension. The comparison is therefore against the actual nonlinear weak-neighborhood theorem.

The geometric estimate alone gives no sharp limiting D/J for these defects. I264's asymptotic example calculation supplies additional explanatory detail, not a theorem target or an independent finding. The useful point of the comparison is that even the whole rough-orientation comparability statement has a short route from the stipulated gap, partner factorization and exponent family.

## Contribution judgment

The wider hypothesis is real. Small-angle Hessian arguments cannot simply be reused with a weighted norm, and I264 correctly tries to retain large-angle terms and the first-channel coupling. Its proposed proof solves that technical issue by an exact gauge and relative-form estimates. Nevertheless the direct identity R=E+F, with a projection onto phi in EVERY channel, avoids that issue entirely. Coupled with (C)--(D), the whole conclusion follows from basic Hilbert-space geometry, one elementary factorization comparison and two standard moment/Holder inequalities. This is stronger evidence for TECHNICAL than describing individual ingredients as classical.

No directly applicable published matrix stability theorem was authenticated, so KNOWN is not warranted. No essential contribution uncertainty remains that would force UNRESOLVED: the positive alternate derivation supplies the comparison. The proposed statement is a useful new-to-project weighted-neighborhood corollary, but does not demonstrate a substantial advance beyond the stipulated family under this task's gate.

The unaddressed substantial stability barrier is the passage from a small full spectral deficit to closeness to the full matrix optimizer manifold, with profile/scale/center variations and potentially several occupied channels. I264 assumes the transverse distance is small and fixes the scalar profile; those hard issues are outside its claim. They are not additional obligations smuggled into a proof review. They explain what the current short corollary does not contribute once its chosen scope is paid by the direct comparison above. Future broader work is not requested, and no second finding is nominated.
