# I288 independent contribution review of I285

2026-10-13. **Contribution verdict: TECHNICAL**, for the fixed-parity-rank theorem at the authenticated target below. **Proof assessment: no flaw found in the complete proof. Priority: UNRESOLVED.** These are separate judgments. No acceptance or finding-count change is claimed; twelve of the requested twenty findings remain accepted according to the assignment.

## Authenticated scope

The reviewed file is `frontier/experiments/i285_gad_phase_coercivity/analysis.md`, all 212 lines, SHA256 `c332f633df20a80ba96f449153cb115f366e5421cdd659a5b6aeefeb163b24fc`. Its theorem fixes interior gamma, nu and an integer k; quantifies over every n, probability law q (including zeros and correlations), and arbitrary phase function F on a binary syndrome image of rank at most k; and allows an additional arbitrary additive local phase. It asserts

    G_q(f) <= C_k [c_A KL(q || r_n) + max_pi Q_pi(psi)]
           <= C_k D_n(psi),
    d_n(psi)^2 <= (8 C_k + 8/c_A) D_n(psi).

Here r_n is Bernoulli(nu) product measure, Q is precisely I280's noisy conditional trace tree, entropy is in nats, and trace norm is unhalved. There is no small-defect assumption. Uniformity in k, unrestricted GAD stability, and new physics are outside the assertion. All OpenAI theorems at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

For the explicit comparison constants below, keep I285's definitions:

    t=1-gamma, h=nu(1-nu), b=gamma(1-nu), c=gamma nu,
    c_A=2 gamma t h, delta=min(nu,1-nu), s=gamma(1-2nu),
    L=[1+(1+s^2)/t^2]^(1/2), beta=4/h+2,
    A_m=2(1+2/h)L^(2(m-1))/(bc).

The complete I280 proof and parent disposition, I285 report/disposition/log/literature/authentication, I273 analysis and disposition, I279 obstruction, and I284 transfer exclusion were read. The actual pinned family-276 wrapper through line 275 and complete output, thermal, partners and special sections were read. Fresh immutable bytes and exact-path Git blobs agree with the retained sources. The manifest distinguishes these reads from complete-file hashing.

## Independent validity check

I checked the logical dependencies, rather than treating the parent's check as an independent gate.

1. The definition of Q agrees with I280, including zero branch weights. The root bound is `4bc L^(-2(m-1)) det rho_j`: the factor two in the pure-projector Hilbert–Schmidt square and the lower bound on eta are both present. Channel inversion is only on the m-site core.
2. The commuting projector bound gives product infidelity at most sum z_j, with z_j <= 2 det rho_j. Population adjustment to the latitude costs `(u_j-nu)^2/h`. The squared trace-distance triangle inequalities give I285 (8) and (11) with their stated factors. The classical KL decomposition, Bernoulli curvature lower bound, and affinity/Jensen calculation yield exactly A_m and beta in (4). A phase assigned at an a-zero string causes no problem for (10).
3. The syndrome basis includes every image coordinate. A non-reused coordinate belongs to exactly one original site; every other column has support only on reused coordinates. Equal-syndrome strings in the core give the two relations in (15). For a unit-modulus u, the nearer sign is at distance at most |u^2-1|, so the sign rounding used there is valid globally. Equation (17) follows because reused factors are signs, and non-reused integer exponents are actual single bits. No independent-amplitude hypothesis occurs in this lift.
4. Core orderings are fixed for all prefixes. Their conditional, q-weighted Q contributions are literal suffixes of the corresponding full trees, so summing m orderings costs m Q*, not an adaptive maximum. Conditional KL is charged by the classical chain rule once.
5. For 0 <= a <= 1, the square-root comparison proves `E_r a <= 2 E_q a + 2 KL(q||r)`. This includes q-zero points. It is substantially stronger for this purpose than a total-variation transport with a square-root KL error, but follows immediately from the paid affinity operation and a squared triangle inequality.
6. Conditioning on independent syndrome columns proves `Pr_r[B_R X_R=0] >= delta^(rank B_R)`, including empty R. On that event the bounded test equals the chosen zero-syndrome core defect. The final C_k in (3) absorbs both coefficients in (23); monotonicity of L and delta justifies the replacements m <= 2k and rank B_R <= k.

Rank zero, one-site cores, deterministic conditional bits, arbitrary large errors and empty removed sets are handled as stated. Local diagonal phase covariance follows directly from the pinned channel formula. I found no missing premise or invalid inequality in this target. This contribution review supplies an independent analytic check, but does not represent a separate formal proof-gate acceptance.

## What is new relative to the spent project inputs?

I280 already supplies amplitude control, the trace-norm tree remainder, site-separating phases, the distance conversion, and flat-amplitude single-parity stability. I273 already supplies finite-size inverse estimates and the product-projector/latitude calculation. I285's finite-core estimate is a recombination of those operations in Q notation, with a sharper root coefficient from I280. It is not a new all-n inverse.

The exact additional step is I285 (12)–(17): choose a parity basis plus reuse witnesses; use equal-syndrome comparisons to force the reused basis factors close to signs; lift one finite-core product phase pointwise. Equations (19)–(22) then pay this finite test through fixed suffix trees, square-root transport, and a positive product-measure syndrome probability. This is a real deduction beyond the literal statement of I280. The adverse question is whether the deduction requires a nonroutine new mechanism when all complexity-dependent losses are allowed.

## Constructive adverse reduction: finite column types suffice

The following proves the same qualitative theorem with worse constants, without the basis/reuse-witness construction. It is an explicit reduction, not an assertion that an external tester automatically controls GAD entropy.

Remove the additive phase and let B have image rank r <= k. There are at most `d = 2^r - 1` distinct nonzero column types. Zero columns do not affect the structured phase. For each type a, retain its unique site if its multiplicity is one, and otherwise retain any two sites of that type. Let C be their union, R its complement, and m = |C|. Then

    m <= M_k := 2(2^k - 1),   rank B_C = r.

Every singleton type is wholly retained. Every site outside C belongs to a repeated type or is a zero column. Denote by g the zero-syndrome core phase defect under r_m. A maximizing core product phase `w(x_C)=lambda product u_j^(x_j)` has

    |z(B_C x_C)-w(x_C)| <= epsilon,
    epsilon^2 = 2g delta^(-m),   z(y)=exp(iF(y)),

on every core string, by the same elementary minimum-atom argument as I285 (14).

For a repeated type a, call its retained sites c_a,d_a. The strings e_c and e_d have the same syndrome; the strings 0 and e_c+e_d have the same syndrome. Therefore

    |u_c-u_d| <= 2 epsilon,
    |u_c u_d-1| <= 2 epsilon,
    |u_c^2-1| <= 4 epsilon.

Choose a sign beta_a nearest to u_c, so `|u_c-beta_a| <= 4 epsilon`. For a singleton type use its unrounded u_j. For an arbitrary original string x construct a canonical core string T(x): retain every singleton bit; at c_a place the parity of all original bits of repeated type a; set d_a to zero; discard zero-column bits. Then `B_C T(x)=Bx`. Rounding w on this canonical string changes at most d factors. Consequently

    |z(Bx)-lambda product_j v_j^(x_j)|
        <= (1+4d) epsilon

for every x. Set v_j=beta_a at every site of repeated type a, v_j=u_j at each singleton site, and v_j=1 at zero columns. The signs permit parity exponents to be replaced by integer exponents. Singleton sites already have literal single-bit exponents. This proves the asserted single global product phase, even for arbitrary nonlinear relations among column types. In particular,

    G_q(F o B) <= 2(1+4d)^2 delta^(-m) g

for every law q, with no closeness or positivity assumption on q.

Now apply the paid finite-size operations on each conditional C-state. They give precisely I285 (4), with the actual m, by the root inverse, projector union bound, latitude adjustment and affinity calculation verified above. Put R first and use m fixed core orderings. Their suffix payment and the KL chain rule give

    E_(q_R) a <= A_m m Q* + beta KL(q||r_n),
    a(v)=G_(r_m)(F(B_R v+B_C x_C)),   0<=a<=1.

The elementary square-root transport gives

    E_(r_R) a <= 2 A_m m Q* + (2 beta+2) KL(q||r_n).

Since rank B_R <= k, its zero-syndrome product probability is at least delta^k, and hence `g <= delta^(-k) E_(r_R) a`. Define

    H'_k = 2[1+4(2^k-1)]^2 delta^(-(M_k+k)),
    C'_k = max{2 H'_k A_(M_k) M_k,
                H'_k (2 beta+2)/c_A}.

For k >= 1, all these constants are finite. The preceding inequalities prove

    G_q(f) <= C'_k [c_A KL(q||r_n) + Q*] <= C'_k D_n(psi).

The spent distance conversion completes exactly the same qualitative fixed-k stability assertion. Rank zero is immediate. The constant may be extremely bad in k; the assignment's theorem permits this. No numerical experiment, compactness argument, entropy continuity transport or depolarizing reduction is involved.

This alternative is a finite-generator, order-two consistency calculation combined with already paid operations. It makes the adverse classification constructive. I285 replaces a core of size O(2^k) by O(k), improving this route's losses from roughly exponential in 2^k to exponential in k (at fixed interior parameters, with polynomial factors). That improvement is useful. It is not needed for the qualitative fixed-k, all-n theorem, and I285 supplies neither optimal k-dependence nor a rank-uniform estimate.

## Older primary comparators and exact non-transfer boundaries

The closest older structural statement inspected is Gopalan–O'Donnell–Servedio–Shpilka–Wimmer, Definition 1.1 and Fact 5.2: low Fourier dimension is dependence on a small parity quotient, equivalently translation invariance of small codimension. Their Theorem 5.3 has a complete testing proof in Section 5. This identifies the older finite-complexity framework; it does not prove the displayed GAD inequality. Our finite column-type reduction is a reviewer derivation, not attributed to that paper.

The closest product-phase testing theorem inspected is Harrow–Montanaro Theorem 19 (proof in Appendix F), alongside Theorem 1 and its Appendices A–B proof. For a diagonal qubit unitary U_z, each local unitary's diagonal entries have a common modulus <=1. Thus maximizing its product-unitary overlap is attained by diagonal factors and equals `max_theta |E_uniform z(x) exp(-i theta.x)|`. Their theorem therefore already tests the uniform product-phase defect. This reduction is an inference. It neither covers biased/correlated weights directly nor pays the test with Q*.

Atici–Servedio Theorem III.3 and its full proof test dependence on individual variables via Fourier sampling. That is a weaker structural comparator than parity quotients, and not a GAD premise. Oono–Yoshida Theorem 4.1, with Section 4's proof, provides a complex-valued finite-group homomorphism-testing comparator for sign/character consistency. None asserts I285's particular coordinate core or noisy tree payment.

Bae et al., Lemma 5, its proof, the von Neumann remark and Theorem 6 concern depolarizing output entropy stability. Khatri–Sharma–Wilde's inspected Section VI passages concern GAD capacity and unital minimum-output relations. These establish relevant older directions, not a GAD stability transfer. I284's non-CP post-map exclusion remains operative. I279's summed-original-marginal bridge remains false; only bounded-core inverse operations were used here.

## Contribution and priority disposition

**TECHNICAL** is my contribution judgment for the whole bounded-parity-rank package. It is stronger than I280's flat-amplitude one-parity statement, and valid author-level progress, but its qualitative all-n scope follows from elementary finite-type consistency plus the paid finite-dimensional and tree operations. The 2k witness core is an economical refinement of that reduction. Increasing the permitted number of interacting parities and adding arbitrary q should not be counted automatically as two independent findings: both are consequences of the same pointwise finite-core lift and bounded-test payment. At k=1 the alternative core has at most two sites already; the correlated-amplitude extension uses the same transport mechanism.

This verdict does not assert that I285 was copied, previously published, or literally contained in an older theorem. **Priority remains unresolved**: the primary screen is bounded, no exact external duplicate was established, and search absence is not evidence of novelty. An independently established sharp or qualitatively new complexity dependence, a new test-to-tree comparison avoiding finite-atom losses, or rank-uniform control would require a different contribution assessment. None is proved in this target. This review nominates no acceptance and changes no ledger.
