# R162W independent adversarial full correctness review, round 1

PRIVATE / LOCAL. This review contains protected source-bearing discussion and named source, primary, and original-history metadata. Original rights are retained; no distribution is authorized.

**Verdict: PASS for the entire unchanged frozen statement and author proof, relative to the stipulated upstream truth. No required author repairs and no essential remaining mathematical obligations were found.** This is solely the assigned independent correctness verdict. It makes no contribution, priority, acceptance, or campaign-count decision. Earlier scopes and dispositions remain unchanged.

Execution provenance: Codex / GPT-6 Astra / reasoning effort high. Service tier default was requested; the tier was not independently measured. Campaign 19/20, latest R041 are supplied context only. The user expressly authorized this review verdict and superseded the older discovery-only/no-self-gate wording. No delegation was used.

## 1. Exact object reviewed and dependency boundary

The frozen statement has SHA256 `fb4e7ccbddfb38a0908622f3c166cce9327d1b91cea0df335ec80b332a4f8bff`. The unchanged author proof is 23,212 bytes, SHA256 `54095012312b54b7c3ddeb33ab75ab66cdec950557ef63d3bd9fd39be32957c3`. All author line references below are to the 265-line file retained at `admitted/packet/private/author-proof.md`, relative to this private directory.

For every integer n >= 2 and every compact convex K in R^n with nonempty interior and K = -K, the claim is the existence of ONE C-infinity symplectic embedding

    {z in C^n : pi |z|^2 < 4} -> int K x int K°,
    K° = {p : p.q <= 1 for every q in K}.

The source form is sum du_i wedge dv_i and the target form sum dq_i wedge dp_i. The whole open capacity-4 ball is the source. A different embedding for each c < 4 does not establish this statement. No boundary extension, closed-ball neighborhood, surjectivity, prescribed prefix, continuous choice in K, quantitative regularity, favorable-body restriction, or dimensional upper bound has been substituted.

The immutable pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and its operative source results are stipulated true. I checked applicability and reconstructed all new steps, without auditing upstream truth. All four essential symplectic source proof chains were read completely: planar 1–362; holomorphic ball 1–274; realization 1–192; polar approximation/consequences 1–249. The actual wrapper, introduction, nested history and lens figure include were read, and the lens figure was inspected. The complete primary gluing section of Pelayo–Vu Ngoc 1210.1537v2, lines 549–778 including the next section heading, was read independently. The wider companion/primary/history readings and their limits are separately recorded; an author's reading assertion is never credited as my reading.

The proof has this dependency structure: a finite-row potential and its SAME momentum map; a smooth schedule of rows and adjacent integer powers with joint compact sublevels; a directly proved parametric radial/Moser construction; a conformally compensated family into the SAME target; and exact Hamiltonian stabilization. Each arrow is checked below. Width as a supremum is not used as a replacement for any arrow.

## 2. Source normalizations and precise paid interfaces

The source `ball.tex` uses d^c H(X) = -(1/4)dH(iX), so

    d^c |z|^2 = (1/2) sum(u_i dv_i - v_i du_i),
    dd^c |z|^2 = sum du_i wedge dv_i.

For a scalar holomorphic h, dd^c |h(a+ib)|^2 = |h'|^2 da wedge db. Consequently the source coefficient k^2 |g|^(2k-2)|g'|^2 is exactly the derivative of J_k required by the author. There is no missing factor 2, pi, or sign.

The actual planar construction has F(w) = (8/pi^2) sum_{j>=0} (-1)^j w^(2j+1)/(2j+1)^2, with no scaling, and g = F^-1. Its image D is bounded, has imaginary coordinates (-1,1), and its horizontal sections are centered intervals. F maps every strictly smaller closed disk compactly into D, g has its only zero at zero, and

    partial_a J_k(a,b) = k^2 |g(a+ib)|^(2k-2)|g'(a+ib)|^2 >= 0,
    |J_k(a,b)| <= k[(pi/4)|g(a+ib)|^(2k) + epsilon_k].

The epsilon_k are nonnegative, finite, and tend to zero uniformly over the entire lens, including moving heights and endpoints near either tip. The uniformity needed in the new schedule is actually present: source planar lines 293–361 bound the moving-endpoint integral and then choose one tail N valid at every point of D. No monotonicity of epsilon_k is promised or needed.

The source finite polar approximation chooses rows IN K°, not just arbitrary strip vectors, and supplies a spanning finite list with K subset K' subset lambda K for every lambda > 1. Full dimensionality and symmetry imply 0 is interior to K and K°, so it applies to every K in the frozen statement, including nonsmooth bodies. Taking successive unions preserves these properties. The source holomorphic-ball proof exposes the explicit logarithmic cutoff, regularized maximum, radial map and Moser sign used below; its mere pointwise existence theorem would not suffice for a parameterized family.

All three Source087 companion interfaces have been checked at their actual statements. Symmetric geometric volume product is at least 4^n/n!, with equality exactly for linear Hanner bodies. General geometric product at the Santaló center is at least (n+1)^(n+1)/(n!)^2, with equality exactly for simplices, and the bound also controls other interior centers. For proper lower-semicontinuous convex extended-valued phi with 0 < integral exp(-phi) < infinity, the general functional lower bound is e^n; with evenness it is 4^n. The conjugate integral may be infinite. The actual functional proof implications use all-dimensional auxiliary bodies. Neither transfers geometric equality classification to functional equality. No functional equality class, quantitative stability assertion, or new geometric bound is used here. The geometric companions' internal proof machinery is uninvoked, and the scope of my companion reading is explicit in LIMITS.md.

## 3. Independent check of the finite-row mixed-power model (author 104–142)

Fix a finite spanning list b_i in K°. Repetitions and zero extra rows do not change the following argument. For ell_i(z) = b_i.z and Omega = {ell_i(z) in D for every i}, define for l >= 2 and 0 <= theta <= 1

    tau = sum_i [(1-theta)|g(ell_i)|^(2l) + theta|g(ell_i)|^(2l+2)].

Writing theta = sin^2 alpha makes this the squared norm of the holomorphic tuple with components cos(alpha)g(ell_i)^l and sin(alpha)g(ell_i)^(l+1). At both endpoints zero components may be retained. Each row has total coefficient ONE. At least one power of each nonzero row is present, so tau = 0 forces every ell_i = 0; spanning then gives z = 0. Holomorphicity at zero gives order at least l.

For 0 <= r < 1,

    r^(2l+2) <= (1-theta)r^(2l) + theta r^(2l+2).

Thus tau <= s < 1 forces each |g(ell_i)| <= s^(1/(2l+2)), including theta = 0 and theta = 1. This is the key lower bound. It would be lost if one faded the weight of a fixed boundary constraint to zero. The author does not make that replacement. Every row image lies in a fixed compact inverse-lens image; a spanning sublist bounds z. Closedness follows inside Omega, not just in its ambient closure.

The matching primitive is J = (1-theta)J_l + theta J_(l+1), using precisely the SAME theta and the SAME row. At fixed parameter, set a_i = b_i.u and v_i = b_i.v. For Phi(u+iv) = (v, -u - sum_i J(a_i,v_i)b_i),

    Phi^*omega_0 = sum du_i wedge dv_i
                   - sum_i dv_i wedge dJ(a_i,v_i)
                 = omega_0 + sum_i (partial_a J) da_i wedge dv_i
                 = dd^c(|z|^2 + tau).

Here repeated i in the first term denotes ambient coordinates; the later sum denotes rows. Derivatives of J in its second argument wedge to zero. Since the parameter is fixed in this spatial pullback, no parameter-derivative terms arise.

For equal position v, subtracting two momenta and pairing with Delta u gives

    Delta p . Delta u = -|Delta u|^2
      - sum_i [J(b_i.u_2,b_i.v)-J(b_i.u_1,b_i.v)](b_i.Delta u)
      <= -|Delta u|^2.

Both row arguments lie in the same horizontal interval of D, where J is nondecreasing. The line segment need not stay in {tau < 1}; monotonicity on D is sufficient. This proves global injectivity even for disconnected fibers of V. Nondegeneracy of the pulled-back form makes Phi a local diffeomorphism. Injectivity plus openness gives a smooth inverse onto its image.

Retain one fixed spanning base list forever. The original base-lens domain bounds all later domains. Since h_K is continuous, there is one finite C > 0 with h_K(-u) <= C on all of them. Symmetry and b_i in K° give h_K(±b_i) <= 1. Therefore

    h_K(p) <= C + (pi/4) sum_i[(1-theta)l r_i^(2l)
                                          + theta(l+1)r_i^(2l+2)]
                  + m[(1-theta)l epsilon_l + theta(l+1)epsilon_(l+1)]
           <= C + (pi/4)(l+1)tau
                  + m(l+1)max(epsilon_l,epsilon_(l+1)).

This controls the very map whose pullback was computed. It does not combine a potential estimate for one witness with a momentum estimate for another. The bound also holds at pure-power endpoints; using a slightly wasteful l+1 coefficient causes no loss of the limiting capacity.

## 4. The infinite schedule has no finite-time defects (author 146–192)

Choose all nested finite approximation lists B_j first, with K subset K_j subset lambda_j K, lambda_j = 1 + 2^-j. Let m_j be their finite lengths and eta_j = 2^-j. For each fixed j,

    C/(l+1) + m_(j+1) max(epsilon_l,epsilon_(l+1)) -> 0.

Hence, after knowing m_(j+1), one can choose k_j so that the strict bound (4.1) holds for EVERY integer l >= k_j. Increasing k_j to exceed k_(j-1) preserves this tail property. The later k_(j+1) is chosen using m_(j+2); there is no circular dependence since all B_j were already chosen. A subsequence-only smallness claim would not suffice; the actual tail bound does.

In part A, a newborn row is r(t)b with r starting at zero. It stays in K° by convexity and 0 in K°. At r = 0, g(ell) and J_l(0,0)b vanish, and the constraint is 0 in D, hence vacuous. The initial base never moves. Old rows retain K_t subset K_j, while the possibly much larger row count is already paid by m_(j+1). In part B all new rows have arrived, so K_t = K_(j+1) and lambda may decrease safely. In C the count is fixed while l moves from k_j to k_(j+1) through finitely many adjacent-power mixtures. The tail estimate covers every one. In D the j+1 tail bound, with count allowance m_(j+2), controls the smaller actual count m_(j+1) while eta decreases to eta_(j+1).

Every ramp can be constant on endpoint neighborhoods, as the author explicitly allows. At the end of an l-to-l+1 interpolation, tau and J are exactly their pure l+1 values. They therefore agree with the next stage on a neighborhood, including all mixed spatial/parameter derivatives. Moving rows extend by zero before birth with the same property. The number of rows and substeps on each bounded time interval is finite, regardless of how rapidly k_j or m_j grow. Stages have length one, so there is no accumulation at finite time. Smoothness on the parameter ray and local extension through t = 0 follow.

The auxiliary h equals l+1+theta on a mixed interval and k+1 on a pure interval. Its values agree at both ends: l+1 at theta=0 and l+2 at theta=1. Flatness gives matching derivatives. Thus h is smooth, nondecreasing, and unbounded; lambda and eta are smooth and nonincreasing with limits 1 and 0.

The smooth lower order kappa = h-3 is positive because k_1 >= 4. On a mixed l-to-l+1 step it is l-2+theta <= l-1, while the lowest possible holomorphic order is l. On a pure k part it is k-2. At a shared junction one can take a sufficiently small neighborhood with kappa below the smallest exponent occurring anywhere in that neighborhood. The spare order makes this possible even when the lower-power coefficient vanishes at the junction. With finitely many locally bounded rows and holomorphic coefficients, a fixed neighborhood of zero and a common constant then give tau(t,z) <= C_I |z|^(2kappa(t)) locally in t. One first bounds by a fixed integer exponent and uses |z| <= 1; no differentiation of a noninteger holomorphic power is attempted. This verifies the exact hypothesis used in section 2.

For joint compactness, take compact I and 0 < s < 1. Extend every row meeting I by zero before its birth, and choose L bounding all occurring powers. Unit total coefficients imply each row lies in

    F({|w| <= s^(1/(2L+2))}),

a compact subset of D. The fixed base bounds z uniformly. For a convergent sequence (t_a,z_a), continuity of each of the finitely many rows puts every limiting row coordinate in that same compact subset of D. The limit is therefore in the total open domain O and satisfies tau <= s. This proves compactness in O. For s=0 the sublevel is the compact zero section over I; for s<0 it is empty. Local finiteness of constraints proves openness of O. Zero newborn rows and moving boundaries cause neither a missing constraint nor escape through a lens tip.

Finally, every v in V_t satisfies |b_i(t).v| < 1 for all finitely many rows. The strip body is full dimensional, so these inequalities give v in int K_t. Combining the mixed bound with the appropriate stage's strict tail budget gives h_K(p) < S(t), where S = (pi/4)(1+eta)h. During C, h >= l+1; during D the next-stage budget applies. This checks all pure, mixed, and row-birth endpoints, not just stage interiors.

## 5. Parametric holomorphic-zero construction (author 32–100)

This is an essential new interface. It is not justified merely by citing a parameterized Moser theorem. The author's proof gives the needed construction, and its choices and flow argument check as follows.

For smooth 0 < a < kappa, set b = (1+a/kappa)/2 and mu = (a+b kappa)/2. Then a < mu < b kappa and 0 < b < 1. The cutoff transition is between t_- = (2/3)log b and t_+ = (1/3)log b, so log b < t_- < t_+ < 0. Writing beta for the rescaled nondecreasing cutoff,

    chi' = b + beta(e^x-b),
    chi'' = beta'(e^x-b) + beta e^x >= 0.

On the transition e^x > b, and outside it the second derivative is either 0 or e^x. All coefficients depend smoothly on the parameter. The additive constant fixing chi=e^x above t_+ is also smooth, for example by integrating chi'-e^x from t_+.

A squared holomorphic norm has plurisubharmonic tau and log tau away from its unique zero; the latter follows from the Cauchy–Schwarz numerator in source ball equation (ball-log-levi). Composition with convex nondecreasing chi is plurisubharmonic. On a parameter neighborhood, tau tends to zero uniformly near z=0, so the affine part of chi applies and

    H_t <= b(t)kappa(t) log|z|^2 + C_1

with a locally uniform C_1. The inequality direction is correct for the domination argument.

The global scalar selections at author line 61 are valid. For a downward-closed scalar condition, pick positive constants valid throughout members of a locally finite open cover; at a given t, every active constant is valid there. A finite weighted average is no greater than the largest active valid constant and hence remains valid. An upward-closed condition is handled with the least active valid constant. Strict local bounds and supports subordinate to the cover preserve strictness. These selections occur SUCCESSIVELY, after earlier choices are fixed, so no moving-bound coupling is ignored. Smooth maxima themselves are not assumed. For an interval-valued choice such as sigma, choose a positive minorant of the remaining distance to 1 and set sigma=1 minus that minorant.

Choose smooth r_2 > 0 with its closed ball contained in V_t. Existence is local from the interior zero section and continuity, and compact spheres give locally persistent strict inclusion. The sphere minimum of H_t is finite because tau has no zero there, and continuous because it is the minimum of a jointly continuous function on a parametrized compact sphere. Choose the smooth majorant M satisfying author line 65. Then, for EVERY delta in (0,1],

    P_(t,delta) = mu log(|z|^2+delta)-M < H_t-2 on |z|=r_2.

The potential P is plurisubharmonic, since log(delta+sum|z_i|^2) is the logarithm of a nowhere-zero holomorphic squared norm. Conversely,

    P-H_t >= (mu-b kappa)log|z|^2 - M-C_1.

Because mu-b kappa < 0, this tends to +infinity as z tends to zero, locally uniformly in t and uniformly for all delta in (0,1]. Thus r_1 can be chosen smoothly and positively, less than r_2, BEFORE choosing delta, so P > H+2 on 0<|z|<=r_1. This ordering is indispensable and is present. Next choose smooth 0<delta<min(1,r_1^2(mu/a-1)). The upper bound is strictly positive.

For the fixed regularized absolute value rho, convexity and |rho'|<=1 make

    rmax(H,P) = (H+P+rho(H-P))/2

convex and nondecreasing in both arguments. Therefore it preserves plurisubharmonicity. When |H-P|>=1 it is the ordinary maximum. The strict comparisons by 2 yield equality with H near the outer moving sphere and with P on the inner ball. Compactness of each sphere and locally strict comparisons give parameter neighborhoods of these seams. At zero the formula is exactly the smooth P on a neighborhood of the total zero section. Consequently Htilde is jointly smooth, including the moving interfaces.

Let sigma(t) lie strictly between max(s_0(t),max_{closed B_(r_2)}tau_t) and 1. The second maximum is continuous. The difference Htilde-tau is supported in {tau<=sigma(t)}. On any compact I, max_I sigma <1; the joint compact-sublevel property places the entire time-support in a compact subset of the total V-domain. This is stronger than a list of separately compact fiber supports.

For Moser time s, every omega_(t,s) is a positive (1,1)-form bounded below on (X,iX) by |X|^2. Thus it is symplectic. Set

    i_Y omega_(t,s) = -d^c(Htilde_t-tau_t).

The right side and Y vanish outside the compact support just identified. Inverting the smooth nondegenerate form is smooth; on compact parameter intervals these fields extend by zero across the moving boundary to a jointly smooth ambient field with common bounded support and bounded derivatives. The support lies a positive distance from the total-domain complement locally, so extension is not an assertion of boundary regularity for V_t. Smooth ODE existence and uniqueness yield finite-time flows and smooth parameter dependence. The ambient flow fixes the complement of V_t and maps V_t to itself; the inverse flow has the same property. Cartan's formula gives

    d/ds phi_(t,s)^*omega_(t,s)
      = phi_(t,s)^*[dd^c(Htilde-tau)+d i_Y omega_(t,s)] = 0.

Hence phi_(t,1)^*omega_new = omega_old. The inverse phi_(t,1)^-1 is therefore the correct direction in E_t.

On the inner ball, the radial map R_t(z)=sqrt(1+mu/(|z|^2+delta))z satisfies R_t^*lambda_0=d^c(|z|^2+P), since the terms differentiating the radial scale cancel in lambda_0. Its squared radius x+mu x/(x+delta) has derivative 1+mu delta/(x+delta)^2 >0. At zero the derivative of the full map is sqrt(1+mu/delta) times identity, so the parameterized inverse function theorem gives joint smoothness of its inverse there; radial monotonicity gives global injectivity on the selected ball. The delta inequality gives mu r_1^2/(r_1^2+delta)>a, and hence its image contains B(pi a) strictly. Composing R_t^-1, inclusion, and phi_(t,1)^-1 gives E_t on the entire indicated open ball and with the required pullback. No hidden parametric theorem or loss at the origin remains.

## 6. Same target, exact scaling, and compact traces (author 196–234)

Set

    d = pi kappa/(lambda S) = 4(1-3/h)/(lambda(1+eta)).

Since h>3 increases to infinity and lambda,1+eta decrease to 1, d is positive, smooth, nondecreasing, strictly less than 4, and tends to 4. The functions

    c = d(1-1/(t+2)),       c_plus = d(1-1/(2(t+2)))

satisfy 0<c<c_plus<d. Moreover c' = d'(1-1/(t+2))+d/(t+2)^2>0, even on flat scheduling intervals. Both tend to 4. With a=lambda S c_plus/pi, one has a<kappa. The section-5 construction therefore provides E_t on B(lambda S c_plus).

The map f_t = T_t Phi_t E_t D_t, with D_t(z)=sqrt(lambda S)z and T_t(q,p)=(q/lambda,p/S), is defined on B(c_plus). Inclusion K_t subset lambda K implies int K_t subset int(lambda K): an interior Euclidean ball in K_t lies in lambda K even if boundaries touch. Division by lambda thus puts q in int K. The strict inequality h_K(p)<S puts p/S in int K°. This uses only convexity, compactness, symmetry and full dimensionality; no boundary smoothness or strict convexity of K enters.

The pullbacks satisfy T_t^*omega_0=(lambda S)^-1 omega_0, Phi_t^*omega_0=omega_t, E_t^*omega_t=omega_0, and D_t^*omega_0=lambda S omega_0. Their product is exactly one. Each constituent is injective and jointly smooth on its actual domain, so f_t is a smooth symplectic family into the SAME U_K.

For compact I, Q_I={(t,z):t in I, pi|z|^2<=c(t)} is compact and lies inside the total c_plus-domain. The positive gap has positive minimum on I. The continuous map (t,z)->f_t(z) sends Q_I to a compact subset of U_K. Therefore the trace of the smaller moving balls is relatively compact INSIDE U_K. In particular, the support needed for any fixed compact time interval has positive distance from the complement of U_K. The argument does not infer this from ambient boundedness or the mere boundedness of K.

## 7. Hamiltonian stabilization and the single global map (author 238–257)

Take V_j=B(c(j)) and e_j=f_j|V_j. The V_j exhaust B(4), with closure V_j contained in V_(j+1). For j>=2 choose capacities c(j-1)<r<r'<c(j). The path f_t for j<=t<=j+1 is defined on a neighborhood of closed B(r') because c is increasing and c_plus>c.

On f_t(B(r')), define X_t(f_t(z))=partial_t f_t(z). Differentiating the spatial symplectic identity gives closed alpha_t=f_t^*(i_X omega_0). Its radial primitive

    A_t(z)=integral_0^1 alpha_t(sz)[z] ds

satisfies d_z A_t=alpha_t by the homotopy formula on a star-shaped ball, including at zero. The integrand is jointly smooth on compact s intervals, so A is smooth in (t,z). No exactness assumption about the target or its complement is needed.

The map (t,z)->(t,f_t(z)) is an injective local diffeomorphism onto its open image: its differential is block triangular with invertible spatial block. Hence its inverse is smooth jointly in t. Choose a fixed smooth source cutoff chi equal to 1 on B(r), supported compactly in B(r'). On this open image set

    G_t(f_t(z)) = -chi(z) A_t(z),

and extend by zero. This is the transported cutoff construction, not a fixed target cutoff. Its total support is compact inside the image of [j,j+1] x B(r'), so extension across that moving image boundary is jointly smooth. The compact-trace result places the support compactly inside U_K. Endpoint smoothness is supplied by a slightly extended time interval, permitted by the strict margins and the global family.

Under the convention i_(X_G)omega_0=-dG, where chi=1 we have -dG=d(A_t o f_t^-1)=i_X omega_0. Thus X_G=X there. The positive-time Hamiltonian flow carries f_j(z) along f_t(z) for every z in V_(j-1), by uniqueness. A common compact support in U_K on this finite interval makes the flow complete for that interval; extending the field by zero outside U_K also proves preservation of U_K without any boundary regularity assumption. Let its time-one map be h_j, and set psi_j=h_j^-1. Then

    psi_j o e_(j+1) = e_j on V_(j-1).

The inverse is essential: using the forward map in this identity would give the wrong direction.

For N>=3 define F_N=psi_2 o ... o psi_(N-1) o e_N on V_(N-1), with the rightmost map acting first. On V_(N-1),

    F_(N+1) = psi_2 ... psi_(N-1) (psi_N e_(N+1))
            = psi_2 ... psi_(N-1) e_N = F_N.

This checks the precise stabilization domain and order. Consequently the common F is defined on union V_(N-1)=B(4). Every point has an open neighborhood on which F equals a finite smooth symplectic composition. Any two points lie in one common V_(N-1), where that composition is injective. Therefore F is globally injective and symplectic. Its derivative is invertible, hence it is open and is a smooth embedding into U_K.

There is no convergence assertion about the unrelated f_t, no demand for one compact support controlling all j, and no regularity claim at capacity 4's boundary. Exact eventual agreement on each smaller open ball supplies the global map. The construction works for every finite n>=2 and every K in the frozen hypotheses. No uniform estimates as n or K vary are required.

## 8. Primary and original-history applicability; adverse alternatives

The full actual gluing proof in Pelayo–Vu Ngoc has the same simply connected source, compact trace in the target, cutoff transport, finite-time flow, and correction composition used here. Its nearby remark about ambient ball bounds is not used for U_K; that would not establish relative compactness in an open target. Section 6 of the author proof separately verifies the specialization, so no broad theorem with unchecked hypotheses replaces the calculations.

Ramos–Sepe 1710.01753v1 was read at its balanced-region interfaces and complete operative section. It constructs separated one-dimensional Hamiltonians H_epsilon=(y^2+epsilon/(1-x^2))/2, action functions tending to 4sqrt(2c), and a nested exhaustion glued by isotopy extension. It gives the stronger global symplectomorphism for a cube factor. The new proof does not assume that arbitrary K admits those separated coordinates or import its parametric toric-classification assertions. Karasev's complete relevant section concerns lp-polar products with 1<p<infinity and strictly convex images of concentric subballs; its ambient Alexander deformation does not guarantee a path in an arbitrary target. Vicente's actual construction uses Young-function rectangular controls and epsilon-enlarged targets, and distinguishes functional duality from polarity. AAKO's capacity-4 statement and supporting-pair cylinder provide an upper bound, not attainment of the lower Gromov supremum. None of these is substituted for the new same-target family. No contribution verdict is inferred from these comparisons.

The exact original-history excerpts retain older scopes. I38 concerns a geometric stability reduction and explicitly separates functional equality. I70 supplies a target-contained isotopy-to-Hamiltonian argument but does not supply arbitrary fixed-capacity paths, and its shear example only refutes a particular Alexander path. I74 supplies explicit shear and derivative-bounded repairs within older restricted relative-packing scopes. The present theorem neither solves arbitrary-prefix packing nor asks to preserve an arbitrary prescribed embedding. No linked history bodies or metadata were followed. Those older conclusions remain unchanged.

The main adversarial failure modes have therefore been resolved within the unchanged author proof: vanishing fixed-row weights; incompatible tau/J witnesses; count growth after an exponent choice; unsmoothed integer order; failure of joint compactness at a moving constraint; wrong cutoff curvature or Moser sign; radial nonsmoothness at zero; escaping time-dependent support; failure of strict target inclusion for touching nonsmooth bodies; uncancelled conformal factors; ambient-only trace bounds; wrong Hamiltonian direction; wrong stabilization domains; and lack of global injectivity. Each has an explicit argument above. These are general arguments, not numerical or finite-body checks.

## 9. Disposition and limits

PASS is for the unchanged proof at its full frozen scope, relative to the stipulated upstream results. The expansions above explain why the existing arguments work; they are not replacements for a defective proof and impose no added hypotheses. **Required author repairs: none. Essential remaining mathematical obligations: none identified.**

This is not a claim that all transitive literature has been read, that the project history was exhaustively cleared, or that every upstream source was independently proved. The detailed actual extents, unavailable/unread ancestors, wrapper navigation, author-reported freeze chronology, display recovery, and isolation limits are in LIMITS.md and the independent read records. Those limitations concern uninvoked or stipulated ancestors, not a missing essential new step in the reviewed proof.

All 127 admitted author files were snapshotted and checked by bytes, SHA256 and full mode before semantic reading; the final post-review record checks the same selection again. The three narrow original-history extents were authenticated and read without extending their scope. All 55 canonical blobs independently matched the complete 13,223-entry tree by byte size, Git blob hash and SHA256. These authentication facts bind the reviewed text; they are not reasons for the mathematical verdict. The parent alone decides whether to integrate or adopt this correctness gate and controls all other gates and counts.
