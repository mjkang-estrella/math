# I281 — adversarial analytic record for uniform GAD stability

**No counterexample to U is obtained. General U remains unresolved.** This record proves dimension-independent obstructions to several proposed attacks, including a uniform theorem for a restricted pure-input class. These are author deductions, not an independent acceptance or substantiality verdict. The target remains twenty substantial findings with eleven accepted; no count changes.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Fix 0<gamma,nu<1, t=1-gamma, h=nu(1-nu), b=gamma(1-nu), c=gamma nu. A is the source GAD channel, s0=g(gamma h), and

    phi_theta=sqrt(1-nu)|0>+e^(i theta)sqrt(nu)|1>,
    M_n={P_(tensor_j phi_theta_j)},
    D_n(psi)=S(A^tensor n(P_psi))-n s0,
    d_n(psi)=min_(P in M_n)||P_psi-P||_1.

Entropy is in nats, trace norm unhalved. U asks for one finite K(gamma,nu), for every n and every pure input, with d_n^2<=K D_n. It has no dimension cap or division by n. Nothing below proves U for arbitrary phases or for mixed inputs.

## 1. Actual dependencies and independent I279 check

Read the completed I273 report, its entire 248-line analysis, entire reading log and authentication JSON, and literature note. Actual needed retained family-276 files were read completely: `build/paper.tex`, `sections/output.tex`, `sections/thermal.tex`, and `sections/partners.tex`. Fresh pinned raw retrievals match their retained bytes and pinned-tree Git blobs. Relevant contracts are `eq:channel`, `eq:v-main`, `lem:partner-branch`, `eq:recursion`, `thm:thermal`, `eq:thermal-table`, `eq:minimum-output-value`, and `cor:partner-additivity`. The zero-block theorem and scalar convexity are stipulated dependencies, not audited.

For a=phi_0, bvec=phi_pi, z=<a,bvec>=1-2nu, independently expand

    psi_n=(a^tensor n+bvec^tensor n)/sqrt(2(1+z^n)).

Its norm is one since the two cross inner products are z^n; |z|<1 ensures a positive denominator. Its marginal is diagonal with entries

    (1-nu)(1+z^(n-1))/(1+z^n),
    nu(1-z^(n-1))/(1+z^n).

The determinant is h(1-z^(2n-2))/(1+z^n)^2, tending to h. Applying the channel's linear population transition to |a><bvec| gives

    X=[[ (1-nu)(1-2gamma nu), -sqrt(t h)],
       [ sqrt(t h), nu(2gamma(1-nu)-1) ]].

Direct two-by-two algebra gives det X=gamma h(1-4gamma h)>0 and Tr(X*X)=1-6gamma h+8gamma^2 h^2. Thus

    ||X||_1^2=Tr(X*X)+2|det X|=1-4gamma h,
    kappa=sqrt(1-4gamma h)<1,  kappa^2-z^2=4t h>0.

With sigma_a=A(P_a), sigma_b=A(P_bvec), and tau=(sigma_a^tensor n+sigma_b^tensor n)/2, tensor trace-norm multiplicativity yields

    ||A^tensor n(P_psi)-tau||_1
        <= (|z|^n+kappa^n)/(1-|z|^n).

For trace-distance parameter delta=||rho-tau||_1/2 in dimension d, the elementary positive/negative-part mixture proof gives

    |S(rho)-S(tau)|
      <= delta log d+(1+delta)h2(delta/(1+delta)).          (C0)

Indeed rho-tau=delta(R-S), and (rho+delta S)/(1+delta)=(tau+delta R)/(1+delta). Apply entropy concavity and the mixture upper bound to both representations, and use |S(R)-S(S)|<=log d. Here d=2^n, so the error tends to zero. Measuring Pauli X on the products distinguishes the equally weighted labels: conditional outcome means are +/-m, m=2sqrt(t h)>0, and the sign test has error <=1/(n m^2). The binary conditional-entropy bound and the actual primary Holevo contract give chi(tau)->log 2. The mixture upper bound is chi(tau)<=log 2. Therefore D_n(psi_n)->log 2.

This independently confirms I279. Summed marginal determinants grow as nh while D_n stays bounded, refuting LP. It does not refute U. The marginal trace-distance lower bound is asymptotically 2sqrt(h), whereas d_n^2<=4 and the excess does not vanish. Generic inverse-channel exponential cost remains genuine; no inverse shortcut is used here.

## 2. A dimension-independent conditional-amplitude lower bound

Let Q_n(x)=nu^|x|(1-nu)^(n-|x|) on {0,1}^n, and let P(x)=|<x|psi>|^2. Write K_cl(P||Q_n) for classical relative entropy. Set

    lambda=2gamma t h>0.

**Theorem A.** For every n and every pure psi,

    D_n(psi)>=lambda K_cl(P||Q_n).                       (A1)

This bound survives cats. It does not control phase-only errors.

**Proof.** Fix any order of sites. At prefix u, let w_u=P(X_<j=u) and p_u=P(X_j=1|X_<j=u). Conditional vectors on the remaining sites are normalized by sqrt(w_u); zero-weight prefixes are omitted. Iterate the actual pure branch recursion *without* replacing conditional populations by unconditional ones. Each leaf is a scalar state of entropy zero, so

    D_n(psi)>=sum_(j,u) w_u [e(p_u)-s0].                (A2)

For g(v)=h2((1+sqrt(1-4v))/2), direct differentiation gives g'(v)=2 atanh(sqrt(1-4v))/sqrt(1-4v)>=2, continuously at v=1/4. Hence e(p)-s0>=2gamma t(p-nu)^2. Also log r<=r-1 gives, including p=0,1 by continuity,

    k_cl(p||nu)
      =p log(p/nu)+(1-p)log((1-p)/(1-nu))
      <=(p-nu)^2/h.

The probability chain rule, obtained by multiplying the conditional probabilities and taking logarithms, is

    K_cl(P||Q_n)=sum_(j,u)w_u k_cl(p_u||nu).

Combining these proves (A1). No channel inversion, ambient dimension or n-dependent constant enters. The proof uses conditional, rather than marginal, populations; it does not reinstate LP.

**Corollary A.** Suppose there are local phases theta_j and one global phase eta such that

    <x|psi>=e^(i eta+i sum_j theta_j x_j)sqrt(P(x))

for every x. Thus the amplitudes become nonnegative after a local diagonal unitary. Then, for every n,

    d_n(psi)^2<= [2/(gamma t h)] D_n(psi).               (A3)

To prove it, use the latitude product with those same phases. Its overlap is F_amp=sum_x sqrt(P(x)Q_n(x)). Jensen applied to log gives K_cl(P||Q_n)>=-2log F_amp. The squared unhalved pure-state distance is 4(1-F_amp^2)<=4(1-e^(-K_cl))<=4K_cl. Apply (A1).

This is a restricted pure-input stability theorem, not the requested arbitrary-input theorem. Nonnegative amplitudes still permit strong correlations and entanglement. Arbitrary nonlocal computational-basis phases do not meet its hypothesis.

### 2.1 Exact effect on positive cats and rare correlated amplitude errors

For I279's positive cat, P=Q_n conditioned on even parity, so

    K_cl(P||Q_n)=log[2/(1+z^n)] -> log 2.

Equation (A1) supplies a positive dimension-independent lower bound, while (A3) controls its actual global distance. Neither sums marginal determinants.

More generally take alpha=sqrt(1-epsilon), beta=sqrt(epsilon), 0<=epsilon<=1/2, and

    psi=(alpha a^tensor n+beta bvec^tensor n)/sqrt(Z),
    Z=1+2alpha beta z^n>0.

Its computational amplitudes are sqrt(Q_n(x))(alpha+beta(-1)^|x|)/sqrt(Z), all nonnegative. It therefore satisfies (A3) for *every* epsilon, even weights far below any entropy-continuity error. In particular an exponentially or superexponentially rare positive cat cannot give an unbounded distance/excess ratio. Positivity and normalization are exact, not inferred from a limiting mixture.

For an explicit scalar formula put q_+=(1+z^n)/2, q_-=(1-z^n)/2 and P_+/-=q_+/- (alpha+/-beta)^2/Z. Then

    K_cl(P||Q_n)=sum_(sign)P_sign log[(alpha+sign beta)^2/Z],
    ||P_psi-P_(a^tensor n)||_1^2
       =4epsilon(1-z^(2n))/Z.

Zero probability terms use 0 log 0=0. The scalar relative entropy compares the parity distributions exactly. No entropy equality with an incoherent binary mixture is asserted for rare weights.

## 3. A trace-norm branch remainder, without inversion

Quantum Pinsker in the fully read primary Carlen excerpt (Corollary 3.3) gives the standard entropy-concavity remainder

    S(wT1+(1-w)T2)-wS(T1)-(1-w)S(T2)
       >=(1/2)w(1-w)||T1-T2||_1^2.                     (B0)

It follows by writing the gap as w D(T1||T)+(1-w)D(T2||T); the two differences from T are (1-w)(T1-T2) and -w(T1-T2). Singular states follow by regularization.

In the actual thermal mixture for a pure split psi=sqrt(x)|0>psi0+sqrt(y)|1>psi1, x=1-p,y=p, put R_i=A^tensor(n-1)(P_psi_i), q=c+t p, U0=1-q,U1=q. I273's endpoint subtraction is

    T1-T2=diag((u/U1)(R1-R0),-(u/U0)(R1-R0)),
    w1 w2=bcxy U0U1/u^2.

The trace norm of the block difference is u||R1-R0||_1/(U0U1). Thus the strengthened recursion is

    D_n(psi)>=e(p)-s0+xD_(n-1)(psi0)+yD_(n-1)(psi1)
              +[bc p(1-p)/(2q(1-q))]||R1-R0||_1^2.     (B1)

Interior parameters ensure q in (0,1) and u>0. At p=0,1 the last term is zero and the unused branch is arbitrary. Applying (B1) recursively gives a sum over prefixes, with weights w_u, of its nonnegative scalar and trace terms. All coefficients are independent of remaining block dimension. Since q(1-q)<=1/4, the trace term is at least 2bc p(1-p)||R1-R0||_1^2.

This is useful output distinguishability coercivity that avoids the Hilbert–Schmidt dilution of I273. It does **not** uniformly control input branch distance: a hidden-coherence branch pair can have very close outputs. It is a standard Pinsker upgrade, not a general stability solution or substantial nomination. Cats are consistent with it and with (A1); no claim that the root trace term alone detects every cat is made.

## 4. Rare arbitrary-phase parity cats: a uniform obstruction in the unital slice

The preceding amplitude theorem misses e^(i theta (-1)^|x|) phase errors, whose diagonal distribution can remain exactly Q_n. The following separate calculation treats all weights and relative phases for nu=1/2. It does not extend by notation to nu!=1/2.

Let a=|+X>, bvec=|-X>, alpha=sqrt(1-epsilon), beta=e^(i theta)sqrt(epsilon), 0<=epsilon<=1/2, and

    psi=alpha a^tensor n+beta bvec^tensor n.

These vectors are orthogonal, so normalization is exactly one. Put k=sqrt(t), r=k^n, and lambda_+=(1+k)/2, lambda_-=(1-k)/2. Let D_axis(k)(rho)=((1+k)/2)rho+((1-k)/2)axis rho axis. Pauli multipliers show exactly

    A_(gamma,1/2)=D_X(k) composed with D_Y(k).

Set rho_pre=D_Y(k)^tensor n(P_psi), tau=(1-epsilon)sigma_a^tensor n+epsilon sigma_b^tensor n. In the X basis rho_pre has only diagonal entries and off-diagonal entries linking strings v with their complements. D_X(k)^tensor n multiplies every such off-diagonal entry by r and fixes every diagonal entry. Consequently

    omega=A^tensor n(P_psi)=(1-r)tau+r rho_pre.          (C1)

**A uniform entropy estimate on rho_pre.** The D_Y errors are Y^v with probabilities p_v=lambda_+^(n-|v|)lambda_-^|v|. Their vectors Y^v psi overlap only when the error strings agree or are complements. Complementary overlap has a common modulus |zeta|=|<psi|Y^tensor n|psi>|<=2sqrt(epsilon(1-epsilon)). The Gram state G of this error ensemble has diagonal p_v, complement off-diagonal entries sqrt(p_v p_complement) times a phase of modulus |zeta|, and the same nonzero spectrum as rho_pre.

For any state G and positive diagonal state Pdiag, independently diagonalizing both and applying scalar log Jensen proves

    D(G||Pdiag)<=log Tr(G^2 Pdiag^-1)
               <=Tr(G^2 Pdiag^-1)-1.                  (C2)

Indeed the Jensen weights are g_i |<i|j>|^2 and the positive arguments are g_i/p_j; zero g_i terms vanish. Here

    Tr(G^2 Pdiag^-1)=1+|zeta|^2,
    D(G||Pdiag)=H(p)-S(G)=n s0-S(rho_pre).

Therefore S(rho_pre)>=n s0-4epsilon(1-epsilon), with no dependence on log(1/epsilon) or on n. This protects even superexponentially small weights; dimension-dependent entropy continuity is not being used.

For tau, (B0) and partial-trace contraction imply

    S(tau)-n s0
      >=(1/2)epsilon(1-epsilon)||sigma_a^tensor n-sigma_b^tensor n||_1^2
      >=2t epsilon(1-epsilon).

Entropy concavity in (C1) now gives the exact lower estimate

    D_n(psi)>=epsilon(1-epsilon)[2t(1-r)-4r].           (C3)

Choose any integer N(gamma) for which t^(N/2)<=t/[2(t+2)]. For all n>=N, (C3) implies

    D_n(psi)>=t epsilon(1-epsilon),
    d_n(psi)^2<=4epsilon<= (8/t)D_n(psi).               (C4)

Thus this arbitrary-relative-phase, rare, high-weight parity attack cannot refute U along n tending to infinity. The finitely many omitted lengths are not being assigned a constant by compactness; (C4) suffices for the proposed asymptotic attack. No conclusion for general unital inputs follows.

**Exact entropy spectrum, if an entropy scale is needed.** For one representative v from each complement pair, put

    q_v=(1-epsilon)p_v+epsilon p_complement,
    C_v=(-1)^|v|[alpha conjugate(beta)p_v
                        +(-1)^n beta conjugate(alpha)p_complement].

The two eigenvalues of the corresponding output block are

    L_(v,+/-)=(q_v+q_complement
       +/-sqrt((q_v-q_complement)^2+4r^2|C_v|^2))/2.

Then S(omega)=-sum_(pairs,sign)L log L exactly. The blocks are positive by (C1), and their traces sum to one. For epsilon=0 the formula gives n s0. For fixed 0<epsilon<=1/2 and theta, cross suppression and binary product distinguishability give D_n->h2(epsilon). For varying rare weights, (C3)-(C4), rather than an unjustified fixed-weight limit, are the uniform obstruction.

In particular e^(i eta Z^tensor n)a^tensor n is this family with alpha=cos eta, beta=i sin eta (after selecting the dominant branch if necessary). The high-weight coherence decays but does not make its distance/excess ratio diverge.

## 5. Coherent separated latitude codewords: explicit entropy budget

This addresses many codewords for arbitrary fixed interior parameters. Choose M>=2 distinct sign strings x_i in {0,1}^n with minimum Hamming distance d, and Phi_i=tensor_j phi_(pi x_ij). Let c_i=sqrt(p_i)e^(i theta_i), sum p_i=1, V=sum c_i Phi_i, Z=||V||^2, psi=V/sqrt(Z). Define

    B_z=(M-1)|z|^d, B_k=(M-1)kappa^d,
    eta=|z|^d, m=2sqrt(t h).

Assume B_z<1. Since <Phi_i,Phi_j>=z^(distance), |Z-1|<=B_z by sum_(i!=j)|c_i c_j|<=M-1. This verifies the normalization. Cross output norms are exactly kappa^(distance): equal factors give a state of trace norm one, unequal factors give X or X*, and tensor norms multiply. With tau=sum p_i A^tensor n(P_Phi_i),

    ||A^tensor n(P_psi)-tau||_1<=(B_z+B_k)/(1-B_z).      (D1)

Let delta be half the right side, assumed <=1, and let C_ent=delta n log 2+(1+delta)h2(delta/(1+delta)). Equation (C0) bounds the entropy error by C_ent.

Measure X independently. Under codeword i the outcome means are m(-1)^x_ij. Decode by maximum correlation score. For a competing word at distance d_ij, the score comparison uses d_ij independent +/-1 variables of mean m. Their log moment-generating function at -s is at most -ms+s^2/2: its second derivative is a variance at most one and its derivative at zero is -m. Taking s=m gives error <=exp(-m^2 d_ij/2). A union bound gives average decoding error <=E=(M-1)exp(-m^2 d/2).

When E<=1/2, the elementary error-indicator conditional-entropy bound is H(label|decoded)<=h2(E)+E log(M-1). The read primary Holevo theorem and the mixture upper bound imply, writing F_err=h2(E)+E log(M-1),

    H(p)-F_err-C_ent <= D_n(psi) <= H(p)+C_ent.         (D2)

For global distance take an index with p_max=1-epsilon. Its overlap with V differs from c_max by at most eta sqrt((M-1)epsilon). Since Z<=1+B_z,

    d_n(psi)^2<=4[epsilon+B_z
                 +2eta sqrt((M-1)epsilon)]/(1+B_z).    (D3)

The lower bound on overlap used here may be negative after squaring expansion; the displayed distance upper bound still follows from |c_max+error|^2>=p_max-2sqrt(p_max)|error|. Shannon entropy satisfies H(p)>=-log p_max>=epsilon.

Equations (D1)-(D3) are quantitative, with all normalization and dimension errors explicit. For example, polynomial M and d>=delta0 n give exponentially small errors and D_n=H(p)+o(1). Fixed nontrivial codeword weights retain a positive entropy excess; an output-indistinguishability assertion alone cannot refute U. If the additive errors and eta sqrt((M-1)epsilon) are o(H(p)), these equations also bound the distance/excess ratio by 4+o(1).

**Boundary:** if H(p) is below those error scales, (D2) cannot determine a relative entropy scale. This regime is not declared closed for arbitrary complex coefficients. Positive binary coefficients are closed by (A3); arbitrary binary phases at nu=1/2 are closed by (C4). Dense nearly overlapping codebooks fall outside the separation/error hypothesis. No capacity theorem or code-decoding success is being equated with minimum-output stability.

## 6. Nearly overlapping collective phases: the small even-cat regime

For nu=1/2 let a_+/-=phi_(+/-delta/2), choosing harmless global phases so that

    a_+/-=cos(delta/4)|+X> -/+ i sin(delta/4)|-X>,
    <a_+,a_->=cos(delta/2).

The normalized even superposition has base-product fidelity

    F_n=2cos(delta/4)^(2n)/(1+cos(delta/2)^n).            (E1)

Under Q_n, let T=|X|-n/2 and u=delta T/2. Its computational probabilities have density

    R=cos^2(u)/Z0,  Z0=E_Q cos^2(u)=(1+cos(delta/2)^n)/2

relative to Q_n. This is nonnegative and normalized even though the *amplitudes* can have signs in rare tails. For n>=2 and n delta^2->0, independent Taylor/moment expansion gives

    K_cl(P||Q_n)=n(n-1)delta^4/256+O((n delta^2)^3),
    1-F_n=n(n-1)delta^4/512+O((n delta^2)^3).            (E2)

Details: E T^2=n/4, E T^4=(3n^2-2n)/16, so Var(T^2)=n(n-1)/8. From cos^2 u=1-u^2+O(u^4), R-1=-(delta^2/4)(T^2-n/4)+an L^2 remainder O(delta^4 n^2). Its L^3 norm is O(n delta^2); the needed even moments follow by expanding sums of independent centered +/-1/2 variables. On 0<=R<=2, the remainder in R log R=(R-1)+(R-1)^2/2+O(|R-1|^3) has an absolute uniform constant, including R=0 by continuity. This proves the first expansion. Similarly expand cos u, divide by Z0, and use Var(T^2) for the second. The implicit constants are independent of n and delta in a sufficiently small n delta^2 neighborhood.

Applying (A1) and using d_n^2<=4(1-F_n) gives

    limsup d_n^2/D_n <= 2/lambda

along every nonzero such small-phase sequence (zero delta gives a minimizer). Thus cancellation of the linear phase tangent does not supply a counterexample in this regime: both the explicit global-distance upper bound and the diagonal-entropy lower bound have the quartic n^2 delta^4 scale. This is a lower bound on output entropy, not a claim of an exact output-entropy asymptotic.

No result here controls all many-product collective fluctuations at n delta^2 of order one, arbitrary destructive coefficient choices, or high-dimensional phase manifolds. A bosonic fluctuation analogy is not used as a proof.

## 7. Unresolved adversarial scope and novelty limits

The general surviving attacks have nonlocal phase structure with diagonal probabilities close to Q_n, or codeword weight/coherence scales below the separated-code continuity resolution. Pure phase-only states sqrt(Q_n(x))e^(i f_n(x)) have K_cl=0 for every f_n, so (A1) explicitly says nothing about their entropy excess. The one parity-phase family is handled only at nu=1/2. An arbitrary code's hidden coherence cannot be controlled by the inverse channel with a uniform constant. Fixed-n rigidity and compactness do not provide a uniform nonlinear radius or settle these regimes.

No actual pure sequence with D_n->0 and d_n^2/D_n->infinity is established. Failure of the investigated attacks is not evidence sufficient to infer U. The completed fallback is the conditional-amplitude lower bound (A1), restricted stability (A3), and the rare-unital-cat obstruction (C4), with the explicit codebook and overlapping-cat bounds above. They use standard recursion, classical chain rules, Pinsker, Gram spectra and elementary concentration; no new-to-literature claim or substantial nomination is made. A separate proof/contribution gate would be necessary before acceptance, and none was requested or launched.

No live I277/I278/I280 outputs, subagents, shared edits, staging, commits, publication, numerical scans, or giant history replay were used.

## 8. Parent-supplied depolarizing stability lead: actual quantifiers and unpaid transfer

Fully read limited primary excerpts from Bae–Gour–Lee–Park–Sanders, arXiv:1510.07815v1: §II and all of §III.1–III.2. The parent supplied this literature lead, not a sibling result. The channel is the isotropic depolarizing channel D_lambda, whose product minimizers include every local pure state. It is not interior GAD, including at nu=1/2 where GAD's Pauli multipliers are sqrt(t),sqrt(t),t rather than three equal multipliers.

The exact read scope is important:

- §II Definitions 1–2 describe entropy excess and squared trace distance using O(epsilon), for a given channel. They do not explicitly quantify one big-O constant across all tensor lengths. The definitions range over states; the actual Lemma 5 and Theorem 6 proof use pure inputs. No mixed-input extension is imported from their theorem wording.
- Lemma 5 is stated for p>=2, epsilon>0 and an n-qudit pure state. Its threshold is a channel/dimension/order-dependent linear coefficient times epsilon plus O(epsilon^(3/2)); the displayed linear coefficient does not contain n. The proof defines epsilon0=1-max_product |overlap|^2, chooses a closest product as |0^n>, and expands with t=sqrt(epsilon0).
- Closest-product stationarity eliminates *all complex weight-one coefficients*, because local depolarizing covariance permits arbitrary local pure directions. Equation (41) gives epsilon0 sum |alpha_x|^2 f_p(|x|)+O(epsilon0^(3/2)); monotonicity makes f_p(2) the normal quadratic coefficient.
- The p=1 remark, Eqs. (44)–(45), gives f(k)=k(a-b)log(a/b)-(a-b)^(2k)[log(a^k)-log(b^k)]/(a^k-b^k), with a=(1+(d-1)lambda)/d and b=(1-lambda)/d. For 0<lambda<1, a-b=lambda and f(1)=0. Direct substitution gives f(2)=2lambda log(a/b)[1-lambda^2/(a+b)]>0, independent of n. This is a useful model-specific normal-Hessian comparator.
- Theorem 6 asserts stability for p>=2 or p=1 and invokes Lemma 5. Its proof does not add an explicit estimate of the O(epsilon0^(3/2)) constant or a block-length-uniform Taylor radius. The preceding Theorem 2 assumes a nonsingular output and justifies a Taylor series for small t; it does not state bounds uniform over its matrix dimension or least eigenvalue. For the product reference here the least eigenvalue is b^n, as its actual Eq. (36) shows.

Accordingly, this branch does not extract an n-independent remainder constant or a global near-minimizer-entry statement from the displayed proof. Writing the coefficient f(2) independently of n is insufficient: an estimate D>=c epsilon0-C_n epsilon0^(3/2) only yields a neighborhood of radius depending on C_n. Applying a local expansion in a contrapositive also does not, by itself, justify inputs with epsilon0 bounded away from zero. This is a limitation of the deduction available from the inspected passages, not a claim that the depolarizing theorem is false or that no other proof establishes its strongest reading. Its Eq. (47)'s literal trace-distance coefficient also needs convention/epsilon rescaling: unhalved pure trace distance squared is 4 times infidelity, while Lemma 5's overlap conclusion is 1-epsilon.

There are further unpaid GAD steps before even reaching these remainder issues. GAD lacks arbitrary local-unitary covariance. A closest point in M_n only permits the one real local phase tangent; a one-site population variation is normal and cannot be discarded as a weight-one tangent. A closest product outside the latitude manifold is not a minimizing GAD input. Thus the paper's rotation to |0^n>, weight-one elimination and coefficients cannot simply be reused for GAD. No constructive proof of U, uniform nonlinear radius, or global entry argument results from this lead. The rare-cat and amplitude results above do not depend on it.
