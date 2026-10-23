# Relative construction: durable prefreeze calculations

These calculations follow the complete canonical proof readings and the operative primary readings recorded in Note 01. There is no frozen theorem and no author-proof nominee. The tested extension is ordinary relative descendant Virasoro for every smooth pair (X,D) with X and D satisfying the source's full ordinary constraints. A construction would have to specify modes on the full super contact space, be independent of cap choices, retain every genus and actual integral curve class, and intertwine ordinary relative gluing. No positivity of N=N_{D/X}, no splitting assumption on bundles used to construct X or D, and no restriction to ambient/even insertions is allowed. This target is not claimed proved.

## 1. The state space and the available cap inverse

Write n=dim_C X and H_D=H^*(D,C). For total contact a put

    F_a(D) = direct-sum_{sum e m_e=a} tensor_e Sym_super^{m_e} H_D,
    F_{<=H} = direct-sum_{a=0}^H F_a.

Disconnected D carries its component labels. The empty profile is F_0=C. Use the source's ordered-root convention for the categorical pairing G_hbar: on roots e_1,...,e_l the gluing factor is (product e_j) hbar^l, followed by exactly the graded symmetrization and permutation quotients in degeneration. It is incorrect to replace this by a guessed unnormalized monomial pairing. Work over C((hbar)) coefficientwise, with Novikov coefficients retaining integral classes.

For C=P_D(O direct-sum N) (lines), the sections D_l=P(N), D_r=P(O) have normals N^{-1},N, and for alpha=pi_*beta,

    D_r.beta - D_l.beta = integral_alpha c1(N).

This flux condition is enforced before coefficients are combined. The source's P=(C,D_r) and Q=(C,D_l) are ordinary relative theories. In its exceptional configuration Q is instead the specified higher-rank cap. Nothing below replaces them by absolute or rubber invariants.

At any finite counting/contact budget, let J map a contact state to its array of pairings against all admissible ordinary cap coefficient rows. Dividing the closed factor is part of J's definition. The source constructs a finite row selector E for which A=EJ is invertible on the bounded input states. The single-root leading blocks are triangular, with nonzero scalar

    c_{e,b}=e^{-(b+1)} ((e-1)!)^{-r}.

The HLR jet construction explains both the factorial and the root-gerbe factor; it is not a numerical coincidence. Super symmetric products of single-root series supply arbitrary profiles, including odd labels; finite coefficient extraction suffices at fixed H. Thus

    P=A^{-1}E,             PJ=1.

With positive counting degree, write A=A_0(1+T), where T raises that degree. Modulo degree >d, A^{-1}=(sum_{j=0}^d (-T)^j)A_0^{-1}. The exceptional zero-degree lowering terms must first be inverted by their contact-nilpotent geometric series. This ordering is necessary; ordinary positive-degree inversion alone does not remove them.

The source provides the bound H+C_0 d on outgoing contact for the relevant cap preparation, including after changing or removing auxiliary labels. Any row calculation involving a mode must first enlarge the auxiliary descendant and contact budgets sufficiently for that mode. A matrix identity on a displayed truncation does not imply a compatible inverse-limit identity. Nor does a counting-degree calculation identify individual integral classes: those labels must be kept throughout the pushforward/splitting maps. The fixed smooth pair and its normal cone have actual class maps to X; the general source sewing lemma's numerical formulation cannot simply be relabeled as an integral-class statement.

## 2. A forced stable-coefficient boundary grading

Take a connected relative invariant with genus g, integral class beta, m interior insertions tau_{a_i}(gamma_i), and l roots (e_j,delta_j), where gamma_i has first Hodge index p_i and delta_j has first Hodge index q_j. Assume the insertion is homogeneous and potentially nonzero. Ordinary (unreduced) relative virtual dimension and the Hodge type of the virtual class give

    sum_i(a_i+p_i)+sum_j q_j
       = (1-g)(n-3) + integral_beta(c1(TX)-[D]) + m + l.       (2.1)

The contact orders have already entered through sum e_j=beta.D. Set R_log=c1(TX)-[D] and b=(3-n)/2. Here R_log is only the ordinary relative dimension class; no identification with a logarithmic Gromov–Witten theory is made. The weighted interior Euler term is

    S = sum_i(a_i+p_i-(n-1)/2).

The relative dilaton factor for an extra ordinary tau_1(1), in the stable forgetful range, is 2g-2+m+l. The divisor equation for R_log contributes integral_beta R_log after its usual descendant correction terms have been canceled. Subtracting these two contributions from S gives, directly from (2.1),

    S - b(2g-2+m+l) - integral_beta R_log
        = (n-1)l/2 - sum_j q_j
        = -sum_j mu_D(delta_j),                              (2.2)

where mu_D(delta)=q-(n-1)/2. Every genus term and every interior marking term cancels explicitly. This fixes the sign: a generating series whose variables label the INPUT root insertions needs the contact Euler correction

    B_0 = sum_{e>=1,alpha} mu_D(delta_alpha)
                         p_{e,alpha} partial_{p_{e,alpha}}.  (2.3)

If the relative tensor is instead raised to a state by G_hbar, the action is the corresponding dual action; equation (2.2) is the unambiguous convention. Odd variables use left super derivatives. B_0 is even. Neither an extra parity involution nor a factor e is justified by this calculation.

Equation (2.2) is an exact stable-coefficient calculation, NOT a complete L_0 identity for the disconnected potential. The degree-zero unstable conventions, genus-one scalar and quadratic terms have not been identified with those of a full relative representation. In particular the absolute scalar chi(X)/16-str(mu_X^2)/4 cannot silently be reused.

For gluing, dual classes on D have first indices q and n-1-q. Their mu_D eigenvalues sum to zero. Hence B_0 is skew for G_hbar; the contact factors and super permutation signs do not change that identity. The forced correction is compatible with seam contraction, including odd states and the empty profile. When D has dimension zero, B_0=0. This is consistent with the target-curve operator statements, but is not a proof of their higher modes.

### Two concrete grading calculations

For (X,D)=(P^2,a line), take g=0, beta a line, one ordinary point insertion and one simple root carrying the point class of D. The invariant is 1: the generic interior point and boundary point determine a unique line, meeting D transversely. There is no nontrivial expanded-target contribution with these generic incidences and degree one; a vertical trivial cylinder without another marking is unstable. Here S=3/2, b=1/2, the dilaton factor is zero, and R_log.beta=2. The residual is -1/2, exactly minus mu_D(point). Thus the contact correction is visible in a nonzero invariant, not just a formal dimension count. This example only checks the stable grading equation.

There is also an all-contact-order leading cap calculation. On the normal P^1-bundle cap, the rank-one fiber row with root order e and insertion tau_{e-1}(i_*gamma) pairs with a root delta by

    J_e(gamma,delta) = hbar^{-1}/e! * integral_D gamma cup delta + O(hbar^0).

This is the r=1, b=0 HLR/source row, since e^{-1}((e-1)!)^{-1}=1/e!. Its relative log first Chern degree is e, its dilaton factor is zero, and its interior weighted degree is e+mu_D(gamma). The row's stable grading residual is therefore mu_D(gamma)J_e=-mu_D(delta)J_e. This verifies the opposite cap/input actions at the entire leading one-root block, with no extra contact-order factor and with the usual categorical odd pairing. Multiplying the genus-zero one-root blocks gives the corresponding lowest-hbar multi-root statement. Positive-base, higher-genus and higher-mode corrections are not removed by this leading calculation.

## 3. Adjunction closes the elementary Chern and Hodge interfaces

Let i:D->X. Adjunction gives

    i^* R_log = c1(TD).

If delta has type (p,q) on D, i_*delta has type (p+1,q+1) on X. Thus on homogeneous classes

    i^* mu_X = (mu_D-1/2)i^*,
    mu_X i_* = i_*(mu_D+1/2),
    i^*(R_log cup gamma) = c1(TD) cup i^*gamma,
    R_log cup i_*delta = i_*(c1(TD) cup delta).              (3.1)

These are actual closed compatibilities, including primitive and odd classes. The half shifts are essential. They show why substituting log c1 while keeping the dimension-n grading and simply omitting the boundary states is not compatible with adjunction. They also explain why the source's Tate-shifted weight complex cannot be replaced by its vertex summands. These elementary interfaces are already classical/source-paid; they are not a nominee.

## 4. A contact-only correction cannot solve the representation problem

There is a useful algebraic obstruction to the simplest ansatz, not to existence of a relative theory. Suppose one tries

    L_k^rel = L_k^bulk + B_k,

where every B_k acts only on contact variables, every B_k therefore commutes with every bulk mode, and the string mode is unchanged (B_{-1}=0). The source normalization has [L_{-1},L_1]=-2L_0. Consequently the (-1,1) commutator of this ansatz is -2 L_0^bulk, whereas the required right side is -2(L_0^bulk+B_0). Therefore B_0 must vanish. The forced correction (2.3) is generally nonzero: already H^*(P^1) has mu eigenvalues -1/2 and +1/2.

Thus an extension with the standard unchanged string mode cannot consist of adding contact-only operators to a bulk Virasoro representation. It needs mixed interior/contact terms (or an independently justified change of the string action). This conclusion is algebraic and does not assume an unproved relative Virasoro identity. It does not rule out the desired operation. At a small-phase slice one can cancel the displayed commutator using a term proportional to t_0(1)B_0; on the full descendant space the string vector field also moves higher times, so this observation is not a full construction.

## 5. The cap-image obstruction and its exact algebra

The source's inverse rows solve recovery of contact states. They do not automatically transport a differential operation on cap labels. For a specified candidate row operation W_k, define

    T_k=P W_k J,
    O_k=(1-JP) W_k J.                                     (5.1)

The symbols T_k denote descended row actions, not the signed adjoint correction B_k in a relative Ward equation. All maps in this paragraph are honest linear operators on the underlying coefficient spaces; if they differentiate auxiliary variables, composition includes that differentiation. The identities are not based on commuting a derivative through a variable-dependent inverse. At each coefficient budget the necessary larger domains are understood, and no limit compatibility is assumed.

Since PJ=1, one has

    W_k J = J T_k + O_k,             P O_k=0.              (5.2)

An operation on ALL rows descends to the contact image exactly when O_k=0. If P' is another left inverse, the two candidate operations satisfy

    P'W_kJ-PW_kJ = (P'-P) O_k.                            (5.3)

This follows by substituting (5.2) and using (P'-P)J=0. Thus proving row-choice independence requires control of the residual; selecting one invertible square minor is insufficient.

If, additionally, the row operations have already been shown to obey

    [W_k,W_l]=(k-l)W_{k+l},

then expanding W_lJ=JT_l+O_l yields the exact defect formula

    [T_k,T_l]-(k-l)T_{k+l}
        = -P W_k O_l + P W_l O_k.                         (5.4)

This is not a claim that the geometric W_k needed here already form such a representation. Their construction, including mixed terms and rubber corrections, is one of the obligations. Formula (5.4) states exactly what the image residual would do even after that construction.

A two-row algebraic control shows why cap spanning alone is inadequate. Over C[t], take J=(1,t)^T, P=(1,0), and W=[[0,1],[0,0]]. Then PJ=1, T=t and O=(0,-t^2)^T. The equally valid left inverse P'=(1-at,a) produces T'=t-at^2. All inverses exist and recovery of states is exact; the row action still does not descend. This is a control for an invalid inference, not a Gromov–Witten counterexample and not a finding.

## 6. The missing quadratic piece is an explicit rubber correspondence

The strongest nodal reconstruction improves the reduction substantially. For an edge e={h,h'} of an (X,D)-valued graph, let M_{Gamma\e} be the cut relative moduli space. Its two recorded evaluations land in

    (X,D)^2 = Bl_{D x D}(X x X).

The nodal gluing uses the strict diagonal Delta_rel. With R the excess locus of two points in the same normal-bundle fiber on an expansion,

    Delta_rel^! = Delta_X^! - Delta_R^!.                   (6.1)

ABPZ's published Theorems 3.9–3.10 construct the second term, rather than leave it as a name. On the virtual class it is

    sum_{sigma=(gamma_1,gamma_2)} (product contact orders)/|Aut sigma|
       Psi_{sigma,*} Delta_sigma^!(
          [P_{gamma_1}(X,D)]^vir
          x Delta_D^![R_{gamma_2}(D,N)]^vir).             (6.2)

Here h,h' lie on the rubber graph gamma_2, gamma_1 carries the remaining relative part, and the graph contraction includes the actual map H_2(D,Z)->H_2(X,Z). The two external relative profiles of the rubber graph need not agree: their difference obeys the normal-bundle flux formula in Section 1. The global scaling on a disconnected rubber target must be kept. Formula (6.2) is not the product of unrelated rubber theories of its connected components.

For a proposed mode's contraction kernel, decorate the two distinguished legs in (6.2) by the same descendant and cohomology operators as in that kernel, use categorical Delta_D, and sum with its coefficient. This gives a concrete candidate rubber counterterm for that quadratic part. The interior legs h,h' allow rigidification by ev_h^*[D_0] (or D_infinity); ABPZ Lemma 3.13 proves compatibility with marked-node normal bundles and ordinary psi lines. The resulting two-relative invariants of P_D(N direct-sum O) are reconstructed by Maulik–Pandharipande. Source065 pays the full ordinary Virasoro constraints on this projective bundle, even when N has arbitrary degree. Thus the numerical inputs of (6.2) are available without a positivity assumption, without deleting primitive/odd states, and without a new reconstruction theorem.

This closes the issue of identifying the excess correspondence and its computability. It does NOT identify its sum, together with all linear, mixed, translation and scalar terms, with a row operation satisfying W_kJ=JB_k. An ordinary absolute constraint on the compact projective bundle is a contracted statement; uncontracting it by a cap inverse runs into (5.1)–(5.3). ABPZ's induction lowers the NUMBER OF NODES of a specified invariant. It does not on its own show stability of the cap image under the entire mode family, or a common recursion compatible with its commutators.

The simplest nonzero geometric warning is ABPZ Example 3.11: X=P^1, D={0}, two degree-one components joined at a node. The cut configuration is Bl_{(0,0)}(P^1 x P^1); the strict diagonal differs from the total transform by its exceptional P^1. The correction is present even though the final relative curve Virasoro theorem is true. Therefore a nonzero isolated correction is neither a disproof of relative Virasoro nor permission to discard it. The complete sum must be constructed.

## 7. Strongest integrated reduction reached

The following operations have actually been assembled in this analysis: full source constraints on X,D and the normal projective bundle; the complete ordinary relative cap inverse including empty/odd states and its cutoff control; stable grading (2.2) and adjunction (3.1); and the explicit strict-diagonal rubber correction (6.2), reducible to the available relative theories by rigidification. They eliminate positivity, split-normal, ambient-only, and mere numerical-reconstruction obstacles to this route.

What has not closed is a compatible family of mixed row operators incorporating all these terms, with image residual O_k identically zero for every k>=-1 and compatible enlarged budgets. In particular I have no proof of the all-mode cancellation of the residual rubber and cap-marking terms, no complete unstable/scalar normalization, and no derived gluing-compatible action on each integral curve coefficient. Formula (5.4) precisely exposes the further commutator obligation. These are failures of this construction to close, not impossibility results.

It would be misleading to freeze a theorem asserting that family, to promote the stable grading identity to a full relative theorem, or to nominate the cap inverse, nodal reconstruction, ordinary projective-bundle iteration, or standard relative curve case. The outcome remains PREFREEZE/no nominee. The durable reduction is stronger than the initial named question because the first correction, half shifts, image residual, row-choice defect, commutator defect and actual rubber correspondence have all been specified and derived.
