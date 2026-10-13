# I265 independent correctness review of I264

**Verdict: PASS. No required mathematical repairs.** This is a new correctness review of the weighted-neighborhood theorem, including its stated constants and full negative-moment deficit. It is not a replay of I260's small-amplitude review. No contribution, priority, acceptance, or finding-count verdict is assigned. No author response, rejection, or existing I264 gate was assumed.

The completely read target is `frontier/iterations/i264-weighted-neighborhood-channel-stability.md`, 223 lines, 10,230 bytes, SHA256 `a0080234eacf4d410917e426222e3e89b24f9eba968cc815c4b46c5b59957395`. It matches the assigned identity. Its analysis, reading record, authentication JSON, and literature record were completely read. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true; this review checks the new deductions, not upstream truth. Final provenance rechecks are recorded in the authentication manifest.

## Exact statement validated

Fix a>0 and 1/2<gamma<3/2. Set r=(gamma-1/2)^(-1)>1, p=gamma+1/2=1+1/r, w=(r+1)a² sech²(ra x), and phi=c sech^(1/r)(ra x), with c>0 and integral phi²=1. Put rho=phi². For every finite m>=2 and every measurable real unit field v, form the self-adjoint operator H=-d² I_m-w vv^T, the weighted projective defect

    J=inf_(real |e|=1) integral w rho [1-(v.e)²],

and the full moment deficit D=C_gamma integral w^p-Tr(H)_-^gamma. The explicit positive tau,c_-,c_+ in I264 satisfy

    J<=tau  =>  c_- J<=D<=c_+ J.

The constants depend only on a,gamma and work simultaneously in every finite m. There is no pointwise orientation, support, continuity, derivative, variation, or decay hypothesis on v. In particular the statement permits orthogonal orientation defects on small weighted sets. Its conclusion remains local in J and fixes the scalar profile. It makes no assertion that small D forces small J.

## Primary contracts and operator setting

The pinned equality manuscript's complete introduction, Theorem `thm:main`, gives the exact measurable positive semidefinite finite-matrix class, ordinary unnormalized trace, sharp full negative-moment constant, and scalar soliton equality with sole negative eigenvalue -a². The complete matrix companion introduction, also Theorem `thm:main`, confirms the same full-moment constant and conventions. Both primary section identities were independently checked against fresh pinned HTTPS bytes and match I260's retained excerpts. Only these sections were read; upstream proofs were not audited.

The external theorem is Hundertmark–Laptev–Weidl, *New bounds on the Lieb–Thirring constants*, Theorem 3.1, in the [author-hosted primary PDF](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf). I independently read all rendered pages 3–6, including form conventions, the exact theorem, supporting majorization/monotonicity statements, and the complete presented proof. Fresh full-PDF bytes have SHA256 `1e8aac1f8d388ae8e53dfeffd04736a0e00da6b26db6b618023a25d1ffb7f2c1`, matching the prior source identity. Its contract is a nonpositive trace-class operator-valued V almost everywhere with integrable tr V_-; the square-root negative moment is at most one half that trace integral. The sign and factor are essential. No compact-support hypothesis appears.

Here all physical potentials are bounded measurable multipliers, with operator norm dominated by a fixed multiple of w. Their operators have domain H² and forms on H¹. Their essential spectrum is [0,infinity); negative eigenvalues are discrete. The forms compressed to psi-perp have domain H¹ intersect psi-perp. The projection preserves H¹ and H² since phi is smooth with the requisite square-integrable derivatives. Real potentials may be treated on complex vector-valued Hilbert space; every estimate below remains valid for complex test vectors by absolute values. This does not extend the theorem to complex orientation fields.

## Principal covariance and measurable gauge

Write dmu=w rho dx and Z=mu(R)>0. S=Z^-1 integral vv^T dmu is a real positive semidefinite finite matrix of trace one. Compactness of the unit sphere, or its spectral decomposition, gives a maximal real unit eigenvector e and

    J=Z(1-lambda_max(S)).

Since J<=Z/4, lambda_max>=3/4 and the sum of the remaining eigenvalues is <=1/4, so the top eigenspace is in fact one-dimensional. Its uniqueness is not necessary for the centering identities. A single constant orthogonal conjugation takes e to the first coordinate. The measurable sign change v->-v on {v_1<0}, with sign +1 on {v_1=0}, leaves P and H unchanged and yields

    v=(alpha,f), alpha=sqrt(1-|f|²)>=0, |f|<=1,
    integral |f|² dmu=J, integral alpha f dmu=0.

The latter identity is precisely the off-diagonal covariance eigenvector equation, not a small-angle approximation. With g=alpha f, Tg=integral |g|² dmu<=J, and

    J-Tg=integral |f|^4 dmu>=0.

If J=0, positivity of mu's density implies P=ee^T almost everywhere, even if the original v changes sign arbitrarily. The scalar equality then gives D=0. For J>0, no bound smaller than one for ess sup |f| is used.

On the two-dimensional span of e and f, ee^T-P has eigenvalues +/-|f|; it vanishes on the remaining transverse directions. Thus ||U(x)||=w|f| exactly for U=H-H0. Cauchy–Schwarz with factors sqrt(w rho)|f| and sqrt(w/rho) gives

    L=integral w|f|<=C1 sqrt(J), L2=integral w|f|²<=L.

The ratio w/rho is integrable because its sech exponent is 2-2/r>0. This is the specific place where weighted closeness produces a small unweighted L¹ perturbation. No derivative of the gauge or f is taken.

## Independent scalar and quadratic-form check

For A=d/dx+a tanh(ra x), direct differentiation gives

    A*A=h+a², AA*=a²+Lplus,
    Lplus=-d²+(r-1)a² sech²(ra x)>=0.

The kernel of A is span(phi), and AA*>=a². The positive spectra of A*A and AA* agree by polar decomposition, so h>=0 on phi-perp. For u in H¹ intersect phi-perp, y=(AA*)^-1 Au is in H² and A*y=u. At the form level,

    q_h[u]=||(a²+Lplus)y||²-a²<y,(a²+Lplus)y>
          =a²<y,Lplus y>+||Lplus y||².

Using u=-y'+a tanh(ra x)y, w<=w0, and the derivative and potential terms in Lplus separately gives

    integral w|u|²
       <=2w0||y'||²+2a² integral w|y|²
       <=[2(r+1)+2(r+1)/(r-1)]q_h[u].

The reciprocal coefficient is exactly c_w=(r-1)/[2r(r+1)]. Smooth approximation and closed forms justify the identities on the full stated domain. There is no claim of a positive unweighted gap for h on phi-perp; the gap a² belongs to h+a² there.

Specify the transformed domain in the quadratic minimization as k with phi k in H¹, equivalently k and k' square-integrable against rho. For F=phi k the ground-state transform is

    ||F'||²+a²||F||²=integral rho|k'|²+integral w rho|k|².

Completion of squares against the positive free operator T=-d²+a² therefore gives exactly

    Qform(g)=Tg-<w g phi,T^-1 w g phi>
            =min_k {integral rho|k'|²+integral w rho|k-g|²}.

The minimizer is F=T^-1(w g phi), which exists because g is bounded measurable and w g phi is in L². No derivative of g is required. The scalar spectral gap yields Var_rho(k)<=a^-2 integral rho|k'|². Taking b=integral rho k in the definition of V(g), and using the triangle inequality in L²(mu), gives for every admissible k

    sqrt(V(g))<=sqrt(r+1)sqrt(integral rho|k'|²)
                 +sqrt(integral w rho|k-g|²).

Two-term Cauchy–Schwarz yields V(g)<=(r+2)Qform(g). Exact centering gives V(g)=Tg. Hence B2=<w g phi,T^-1 w g phi> obeys

    0<=B2<=Tg, J-B2=J-Tg+Qform(g)>=J/(r+2).

The large-angle contribution J-Tg has the favorable sign and is retained. Applying the I262 Taylor coefficient directly to f would not justify this step.

## Isolation and exact Feshbach equation

Let psi=(phi,0), Q=I-|psi><psi|, and B0=Q(H0+a²)Q on Q's Hilbert space. We have B0>=a². For u in its form domain,

    E_a[u]:=integral (|u'|²+a²|u|²)
            =<u,B0u>+integral w|u_1|²
            <=(r+2)<u,B0u>.

Here integral w|u_1|²<=w0||u||²<=(r+1)<u,B0u>. The free inverse kernel is exp(-a|x-y|)/(2a). Its diagonal evaluation inequality, summed over components, is |u(x)|²<=E_a[u]/(2a), with no factor m. Consequently sup |u|²<=K<u,B0u> and

    |<u,Uu>|<=L sup|u|²<=epsilon<u,B0u>,
    epsilon=K C1 sqrt(J).

This is a bounded relative form perturbation. It implies QHQ>= (1-epsilon)B0-a² Q>=-epsilon a² Q, since epsilon<1. The order H>=h I_m>=-a² and the normalized psi test give inf sigma(H) in [-a²,-a²+J]. The choice of tau ensures epsilon<=1/[12(r+2)] and J/a²<=1/[12(r+2)]. Thus -a²+J<-epsilon a²<0. Discreteness and codimension-one min–max now imply exactly one eigenvalue, of multiplicity one, below the compressed spectrum. Denote it lambda1=-a²+delta, where 0<=delta<=J<a²/8.

For t=epsilon+J/a²<=1/[6(r+2)]<1/4,

    R:=Q(H-lambda1)Q=B0+QUQ-delta Q,
    (1-t)B0<=R<=(1+t)B0.

These are forms on the same dense domain. R has a bounded positive inverse; the normalized conjugation by B0^-1/2 also justifies inverse order. An eigenvector for lambda1 must have a nonzero psi component, since otherwise it lies in the compressed spectral subspace below its lower bound. Eliminating its Q component gives the exact identity

    delta=J-<b,R^-1 b>, b=QU psi.

This requires no analytic family or continuation. The coupling has the two actual components

    b=(Q_scalar(w|f|² phi), -w g phi).

Accordingly <b,B0^-1 b>=B1+B2, with B1 exactly as defined in I264. For a scalar test u perpendicular to phi, the projection drops out of <Q_scalar(w|f|² phi),u>. The dual evaluation bound gives

    B1<=K(integral w|f|² phi)²
       <=K (integral w rho|f|²)(integral w|f|²)
       =K J L2<=epsilon J.

This is the needed o(J) control, including when |f|=1 on exceptional sets. It uses the unprojected source in the dual pairing; it does not presume that the projected function has the same L¹ norm.

Inverse order gives <b,R^-1 b><=(B1+B2)/(1-t). Combining this with the previous coercivity,

    delta>=J/(r+2)-epsilon J-t(1+epsilon)J/(1-t)
          >=J/(r+2)-3tJ>=J/[2(r+2)].

The arithmetic is valid since epsilon<=t<1/4 implies epsilon+t(1+epsilon)/(1-t)<=2t/(1-t)<3t. The final step uses t<=1/[6(r+2)]. Thus both isolation and the claimed lower bound on the ground-eigenvalue displacement hold with the stated constants.

## Independent full-tail moment proof

For u perpendicular to phi and transverse vector z, the compressed form equals q_h[u]+||z'||² plus the positive first-channel term integral w|f|²|u|², the mixed term -2 Re integral w alpha conjugate(u) f^T z, and -integral w|f^T z|². Discarding the positive term, set X²=integral w|u|² and Y²=integral w|f^T z|². Since alpha<=1,

    2XY<=(c_w/2)X²+(2/c_w)Y²

and c_w X²<=q_h[u] give the proposed lower comparison

    q_H[u,z]>=(1/2)q_h[u]+||z'||²-B_w integral w|f^T z|².

If mu_j are the negative variational levels of QHQ, codimension-one interlacing gives lambda_(j+1)(H)>=mu_j. Form order gives mu_j>=lambda_j(S), where S=(h/2 on phi-perp) direct-sum Kf and Kf=-d² I_(m-1)-B_w w ff^T. The first summand is nonnegative, so the negative levels of S are precisely those of Kf. With zeros supplied when a list ends, these directions imply that the negative moments of H after lambda1 are at most all the negative moments of Kf.

Apply HLW with V=-B_w w ff^T on G=C^(m-1). It is measurable, nonpositive, bounded, trace class pointwise, and integral tr V_-=B_w L2<infinity. Hence

    sum sqrt(E_j(Kf))<=(B_w/2)L2.

For q=2gamma>1, sum t_j^q<=(sum t_j)^q for nonnegative t_j. Thus the tail is <=(B_w/2)^(2gamma)L2^(2gamma). No channel count or eigenvalue count enters. Finite partial sums and monotone limits also justify the formula if an infinite list is allowed. In this particular fixed finite m setting, H>=h I_m additionally limits its negative count by m, but that observation is not needed and supplies no factor m in the estimate.

The first Holder step is exact because

    p/(2gamma)+(1/2)(1-1/(2gamma))=1,
    w rho=c² w0^(-1/r) w^p.

Factoring w|f|² as (w^p|f|²)^(1/(2gamma))(sqrt(w)|f|²)^(1-1/(2gamma)) gives

    L2^(2gamma)<=(w0^(1/r)/c²)J Ahalf^(2gamma-1).

For theta=r/[4(r+1)] in (0,1), the second factorization is

    sqrt(w)|f|²=(w rho|f|²)^theta
        [ (sqrt(w)/(w rho)^theta)^(1/(1-theta)) |f|² ]^(1-theta).

Holder and |f|²<=1 yield Ahalf<=Ctheta J^theta. The sech exponent of sqrt(w)/(w rho)^theta is 1-2theta(1+1/r)=1/2>0, so the integral defining Ctheta is finite. Consequently the entire tail is bounded by

    N J^(1+beta), beta=theta(2gamma-1)=1/[2(r+1)]>0.

Both Holder steps keep the same factor |f|² inside their integrals. Neither replaces the tail weight by a compact lower bound for rho. Every factor in N is correct. This proves independent full-moment control for the stronger weighted hypothesis, rather than using its experiment file as evidence.

## Constants and final deficit

All threshold terms are finite and positive for fixed a>0, r>1. The first three conditions in tau establish the covariance choice, spectral isolation, inverse order, and delta<=a²/8. The last condition gives N J^beta<=m_gamma/[4(r+2)]. On [7a²/8,a²], the minimum and maximum of gamma s^(gamma-1) are exactly the proposed m_gamma and M_gamma, including gamma<1 and gamma=1. Since the cost is a^(2gamma),

    D=a^(2gamma)-(a²-delta)^gamma-tail,
    D>=m_gamma J/[2(r+2)]-N J^(1+beta)
      >=m_gamma J/[4(r+2)],
    D<=M_gamma delta<=M_gamma J.

This proves the proposed coefficients without changing tau. Optional closed beta-integral expressions and dimensional checks appear in the analysis artifact. No hidden m dependence appears in any constant.

## Adversarial cases and limitations

For v=e2 on a measurable A and e1 elsewhere, if J_A=integral_A w rho<Z/2, the principal channel is e1, J=J_A, f=1_A e2, and g=0. H splits as (h+w1_A) direct-sum (-d²-w1_A), with additional free channels. Here the essential supremum of |f| is one. Exact Feshbach and the dual estimate give 0<=J-delta<=K J L_A/(1-t), L_A=integral_A w. For A=[0,ell], J is asymptotic to w(0)rho(0)ell and L_A to w(0)ell. Thus L_A->0 and L_A^(2gamma)/J->0 because 2gamma>1. For A=[R,R+1], R->infinity, J is asymptotic to a positive multiple of exp(-2a(r+1)R), while L_A is asymptotic to a positive multiple of exp(-2raR). Since 4r gamma=2r+4, L_A^(2gamma)/J=O(exp(-2aR))->0. Both cases give D/J->gamma a^(2gamma-2), independently confirming the claimed linear scale in genuinely large-angle regimes.

For arbitrarily many disjoint exceptional sets assigned different transverse channels, total J controls the same Euclidean quantities and total trace integral. For arbitrarily rapid or infinite measurable oscillation, all identities and forms still require only the measurable multiplier; no derivative or frequency bound is invoked. As m grows through arbitrary finite values, the covariance, evaluation inequality, inverse form estimate, cross-term bound, and HLW endpoint retain exactly their constants. These checks expose no shrinking-set, tail-translation, oscillation, or channel-dimension counterexample. They do not assert an infinite-dimensional orientation theorem.

No conclusion is made for endpoints, constants uniform as gamma approaches endpoints, complex orientation fields, variable scalar profiles, arbitrary rank, multiple initially occupied solitons, J>tau, or a converse from small D. C1 loses integrability at r=1, c_w degenerates there, and beta tends to zero as gamma decreases to 1/2. No novelty assessment, acceptance decision, or count decision follows from this PASS.

## Repairs, artifacts, and read boundaries

**Required repairs: none.** Specifying the transformed minimization domain, compressed operators as forms, and explicit interlacing directions would improve exposition; the details above justify the existing statement and constants without a theorem repair.

The independent derivation is in `frontier/experiments/i265_weighted_neighborhood_channel_proof/analysis.md`. Complete read extents and tool failures are in `reading-and-failures.md`; primary URLs and retained source identities are in `frontier/sources/i265_weighted_neighborhood_channel_proof/literature.md`; exact input and output hashes are in `input-authentication.json`. Its own hash is detached in the handoff, avoiding self-reference.

The finalized I260 review, analysis, reading record, authentication and literature record were completely read as permitted background, and its fully read primary excerpts were re-read and authenticated here. I260's correctness verdict does not supply this theorem's new estimates. I261 and every other live sibling or review output were excluded. No subagent, shared edit, staging, commit, publishing, research code, test, numerical scan, snapshot, or giant history replay was used. All retained primary files are fully read section or page excerpts, not copied unread source trees. All writes are within the assigned I265 paths.
