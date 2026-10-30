# Independent manuscript verification, round 1

Review date: 2026-10-14 local / 2026-10-15 UTC. Reviewer: Codex, fresh
manuscript review agent. No child agents, git operations, shared edits,
submission, publication, acceptance or count decision were made. Writes are
confined to this review directory. The prior proof and contribution verdicts
are evidence about their own scopes, not the reason for this verdict.

## Verdict and exact scope

**PASS for the frozen consolidated manuscript's proof and mathematical
presentation, relative to the stipulated pinned OpenAI results and the named
classical analytic inputs.** I found no omitted paid operation, changed
hypothesis, bad constant, unsupported new deduction, or mathematical loss in
the inspected rendered passages. P1 and P3–P8 are resolved in the actual
compiled text. P2 is parent-owned archival bookkeeping; the parent reports
it complete at 4f302a5a. I made no git operation to independently certify
that archival assertion. All four reviewed proof inputs still match their
prescribed hashes.

The verdict covers the full claim: for each integer n >= 2, one
alpha_n in (0,1/3] and C_n work for **every finite p >= 3** and **every
bounded weak p-harmonic solution on B_1**, with gradient norm plus
alpha_n seminorm on B_(1/2) bounded by C_n osc_(B_1) u. There is no sign,
noncriticality, level-set or boundary assumption. No claim for 2 < p < 3
is supplied. The large-p inhomogeneous consequence is a corollary using
a cited transfer theorem, not a solution of full MathDB 405360 and not
another nominated result. This review makes no novelty, priority,
substantiality, acceptance or counting decision.

The binding validation file is
`p-gradient-manuscript/validation.json`, SHA-256
`d689320069f165faeb21cb2f8be63cbf5a70f269b6bf328963dea47b103649a6`.
Its PDF has 21 pages and SHA-256
`bc66e9d14e6d83e8e0a9c579e4856c0a302958af952a1506a5849f5b46875155`.
All manuscript source, PDF and log hashes in that receipt, all output
hashes in `p-gradient-manuscript-consolidation/outputs.json`, and all
formal-source hashes in `formal/validation.json` were checked against
actual bytes and match. Full per-file byte counts and hashes are in
[input-hashes.json](input-hashes.json). This verdict does not silently
cover later source or PDF changes.

## All-paid-operations map

I read the complete two proof reviews and their source maps, all four
reviewed mathematical inputs, the consolidation report and claim map,
the exact appendix delta and manifests, all active manuscript TeX, and
the scalar/vector Lean sources. The following checks concern the
manuscript itself, not just the implementer's comparison.

| Actual manuscript passage | Reviewed union / input | Independent verification and disposition |
|---|---|---|
| Section 1, Theorem 1.1 and scope | I345 §1; addendum R3/R6/R7 | All quantifiers, p range, oscillation normalization and exclusions retained. Classical inputs are credited; pinned truth is explicitly conditional at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. **PASS.** |
| Section 2, logarithmic bound | I345 §2.1 | The displayed c, b and C have the same coefficients. With p >= 3, dividing the bound for -(p-1) log v by (p-1)^2 is uniform; M <= v <= 2M removes a sign condition. Classical C1 regularity is used before extending the noncritical estimate across the zero-gradient set. **PASS.** |
| Lemma 2.1, structural and preliminary estimates | compact-p lemma §§1–2 | s=(p-2)/2, C=0, common a,K*, H_s and its [2/3,1] prefactor match. Fixed Sobolev/Moser exponents and the derivative bound for sqrt(H_s) give a common local supremum estimate. The scalar potential is u, avoiding a varying-exponent Hodge estimate. **PASS.** |
| Lemma 2.1, nonlinear comparison | compact-p lemma §3 | DA_s is uniformly Lipschitz for 2s >= 1; the lower reference radius gives rho >= 4^(-S). The quarter-segment monotonicity estimate and Cauchy–Schwarz give the printed inverse-power bound. Weighted Caccioppoli, the fixed Sobolev exponent and linear comparison yield E^(1+a). Zeros do not require a positive ellipticity bound for DA_s itself. **PASS.** |
| Lemma 2.1, references and iteration | compact-p lemma §3 plus new P7 | The center reference, projection, t rescaling, normalized excess and drift were reconstructed explicitly below. The t^2 gain survives, as does the lower reference size. **PASS.** |
| Lemma 2.1, decrease branch and normalization | compact-p lemma §§4–5 plus P8 | All constants that might vary with s are bounded explicitly or occur only in fixed source estimates. Common lambda_* satisfies both source inequalities, theta is positive, infinite decrease covers critical gradients. Testing with chi^p u and applying the local supremum estimate gives the oscillation bound. Fubini constant extension handles n=2. Entire bounded-gradient affinity follows by scaling. **PASS.** |
| Section 2, expanding domains | I345 §2.3 | Entire Lipschitz limits are weak p_*-harmonic at finite p_*, or infinity-harmonic at epsilon=0. The polynomial/Delta_p inequalities agree at zero test gradients too. The exact infinity lift puts original dimension two into dimension three; the pinned estimate on arbitrarily large balls forces affinity. No convergence of gradients is presumed. **PASS.** |
| Section 3, critical-safe lift | I345 §3 | The branch of phi_sigma,b=1 creates a genuine C2 test of u. The Schur block difference has the required semidefinite sign for each sigma > 0; take sigma to zero only in tr(MH_sigma), not in the Schur Hessian. Lower tests use the negative denominator and reversed comparison. At g=0, M is the vertical rank-one matrix. **PASS.** |
| Section 4, Lemma 4.1 | I345 §4; addendum R4 | b is monotone even though goodness need not be. Two approximate suprema select an actual bad lambda > b/4. The quotient > i gives s_i < i^(-i), and s_i/lambda_i^k tends to zero for each fixed k. The lemma now claims only s_i -> 0, as justified. **PASS.** |
| Section 4, bounded-p exclusion | compact-p lemma; I345 §4 | Every lambda > C r^theta is good using the nonzero lifted derivative. For bounded p_i this contradicts lambda_i > (i/4)s_i^gamma_i once gamma_i < theta. Thus epsilon_i -> 0 is established before finite-viscosity stability. **PASS.** |
| Section 4, geometric compactness | I345 §4; pinned source-03 geometric extraction | Fixed-multiple goodness, slope bounds, enclosing fits, equal-parameter comparisons, bounded normalized coefficients, fix-S-then-increments equicontinuity, local boundedness, same-C0 fits and nonaffinity all remain. The source's PDE identification is expressly replaced. Center/radius coefficient subsequences need not be common to uncountably many pairs. **PASS.** |
| Section 5, constrained rescaling and extension | I345 §5 | Direct gradient/Hessian scaling gives the printed C_i, including epsilon_i lambda_i q_t^2. The exact increment gives q_i·xi_i=1/c_i at both test signs. The nonnegative-part extension agrees at those tests and is continuous and degenerate elliptic globally. **PASS.** |
| Section 5, negative exclusion and transport | I345 §5 | One interior bounded-gradient quadratic contact gives A_i >= -C lambda_i and nu_i >= -C epsilon_i; no pointwise test-gradient bound is assumed. The exact increment yields the printed w_i,delta_i and |delta_i| <= C|w_i| on a larger fixed ball. **PASS.** |
| Section 5, finite effective viscosity | I345 §6; frozen appendix | Compact-jet convergence gives the actual limit PDE. If a != 0, its exact transport representation removes the parallel Hessian component. Substitution h=d ell e+h_perp yields ordinary time coefficient q+d^2-kd and **the same C0**, with no bounds on k,d required. Reduced dimension n-1 >= 1 includes original n=2. Zero viscosity uses the pinned theorem; positive viscosity uses Appendix A. **PASS.** |
| Section 6, Lemma 6.1 | I345 §7; addendum R2; r2 §3.1 | The common-data interface is present as a lemma. Savin's varying-operator proof supports its uniform constants; the Hessian operator-norm convention requires N Lambda_0. No gradient bound on the unknown is inserted. **PASS.** |
| Section 6, Lemma 6.2 | I345 §7; addendum R5 | All hypotheses attach A to the coarse slope. The ellipsoid has the required strict margins, W is small in value, and its exact equation is extended only off the constrained test set. The amplitude identity F_1(dX,dq)=d F_d(X,q) gives a derivative bound proportional to ||W||. Scaling yields Ce/H in the anisotropic Hessian. The actual slope is nonzero; lambda <= e and r <= k_* ell put all fine-cylinder segments in the half ellipsoid. **PASS.** |
| Section 6, vector certificate and neighborhood | new vector Lean source; prior scalar certificate | Paper Q and both exact square identities match the Lean form and assumptions. The common rho, eigenvalue window and Savin norm constants were checked below, separately from the Lean coverage. **PASS.** |
| Section 7, unequal parameters | I345 §8.1 | Common ball gives O(kappa sqrt(lambda)), the short common axis gives O(kappa^(3/2)lambda), and the angular correction is quadratic. Only the subsequent equal-eta chain uses the source norm-comparison lemma. The resulting O(kappa^2 lambda+eta(1+log nu)) proves A'/A -> 1 **before** the coarse parameter is substituted. **PASS.** |
| Section 7, large viscosity closure | I345 §8.2 | H/D <= s lambda^(-2) -> 0; eta/e' -> 0; ell/r -> infinity; lambda <= e'; and error/(lambda r) -> 0. The real nonzero DU(z_i) makes the chosen bad lambda good. No growing-domain bound on V_i is borrowed. **PASS.** |
| Section 8, derivative extraction | I345 §10; source-03 extraction | Dyadic slopes converge uniformly; rho_j=r_j^(1+gamma/2) and residual r_j^(gamma/2) give alpha=gamma/(2+gamma). The two-center comparison remains valid even if its evaluation point is outside the half ball. Restriction and scaling restore the stated estimate. **PASS.** |
| Section 8, value-limit consequence | I345 §10 | Bounded slopes have a subsequence at each center; the limiting Taylor inequality identifies a unique derivative. Thus v gets this same exponent before finite differences are optimized. No independent infinity exponent is silently equated to alpha, and no rate in p is claimed. **PASS.** |
| Section 9 and formal scope | addendum R6/R7; new Lean receipt | Precisely ten algebraic support lemmas are claimed. PDE, near-zero jets, Savin, compactness, rigidity and the main theorem are expressly outside the formal coverage. **PASS.** |
| Appendix A.1–A.2 | frozen appendix; I236 operation trace in r2 | Supporting spatial slopes, strict r^2/2 boundary gap, common time interval, lifted upper test, convex scalar bound and reverse-time base point pay full local Lipschitz regularity. Cone infimum retains order, minimizes in a strict inner margin, remains a supersolution by fixed translation, is locally Lipschitz and recovers original contact. **PASS.** |
| Appendix A.3 | frozen appendix | The exponential flux derivative and its positive full-gradient ellipticity agree with the stated operator. Sup convolution, Alexandrov tests, fixed-epsilon mollification, the one-sided Fatou bound and bounded-gradient flux convergence preserve the weak sign. The optimizer Taylor comparison pays a.e. gradient convergence as epsilon -> 0. Inf convolution reverses the argument without assuming -f solves the same equation. **PASS.** |
| Appendix A.4 | frozen appendix plus P5 | The averaged derivative matrix B is symmetric and elliptic; Lax–Milgram and energy tests give 0 <= w <= d. Solution Harnack makes w zero. Trace identification on every small sphere, rather than an unproved strong principle for d, gives open contact. The m=1 constant extension is valid. **PASS.** |
| Appendix A.5 | frozen appendix plus P4 | Fitted-frame PDE and fit transformations preserve tau,C0. Both the PDE and every fit pass to normalized limits. The affine-slice alternative uses bounded fit p and arbitrary x to force zero second difference of P(t), growth to eliminate its linear time part, and tests to force c''=0. Reflection has the correct signs and fit map. **PASS.** |
| Appendix A.6, extremal normalization | frozen appendix | kappa is finite and positive; normalized measures keep their mean by first-moment uniform integrability. Subquadratic tails pay convergence of varying value integrals. The geometric measure-envelope representation and Jensen sandwich force equality and second moment one. The radius-1/kappa frame puts equality at envelope parameter one, with gap kappa^2/2. **PASS.** |
| Appendix A.6, changed equation and contradiction | frozen appendix plus P6 | The common-time sum argument is applied with horizontal trace directions as well as the characteristic direction. The theorem-of-sums error goes to zero at fixed synchronization penalty first. The variance cost is affine in the characteristic direction and constant under common horizontal translations, giving precisely G_tau >= 0. Positive-time semiconcavity is uniform on compact cylinders. Contact gives W=V; a global quadratic-support maximizer contradicts the positive gap. **PASS.** |

## Checks of the genuinely changed passages

### P7: the reference update, normalization and drift

The manuscript does not repeat the printed fixed-half-ball average of the
linear comparison; it explicitly chooses its center value. Let
e_i(x)=omega^i(x)-w_i, and let l_i be the linearized comparison field on
the fixed inner ball. The established estimates are

    integral_inner |e_i-l_i|^2 <= C E_i^(1+a),
    |l_i(0)|^2 + sup_(B_1/4)|Dl_i|^2 <= C E_i.

For t <= 1/8, integration of
|e_i(x)-l_i(0)|^2 <= 2|e_i(x)-l_i(x)|^2
+2t^2 sup|Dl_i|^2 over B_t gives

    integral_B_t |omega^i-(w_i+l_i(0))|^2
       <= C t^(m+2) E_i + C E_i^(1+a).

Put omega^(i+1)(x)=omega^i(tx). The Jacobian t^(-m), with E_i
always the integral on the rescaled unit ball, gives exactly
E_(i+1) <= C(t^2+t^(-m)E_i^a)E_i. There is no missing t^(-m)
on the linear term. Since projection to the closed unit ball is
nonexpansive and fixes both w_i and every omega^i(x), it decreases
both the error and the proposed reference drift. Thus
|w_(i+1)-w_i| <= C sqrt(E_i). With the manuscript's choices,
C_3 t^2 <= t/4 and C_3 t^(-m)epsilon^a <= t/4, so contraction
is at most t/2. The displayed sum uses the weaker ratio sqrt(t)
and is still valid. Total drift <= 1/8 changes squared reference
size by at most 1/4. Starting from |w_0|^2 >= 1/2 preserves the
required lower size 1/4. Translation repeats this at every center;
the common source Campanato/geometric-series argument then applies.
I checked Uhlenbeck's printed page 234 image for the reason this
particular alteration was necessary; the manuscript alteration is sound.

### P8: constant inventory

The inventory now contains K*, (S+1)^2, 2^(2S+2), fixed cutoff factors,
fixed-exponent Moser c(beta), c'(1), Sobolev and Poincare, as well as
the explicit 4(P-1)^2 Caccioppoli factor and the H_s normalization
factors. The perturbation threshold and decrease factor are chosen
after these common bounds, rather than by assuming an arbitrary
fixed-s constant is locally bounded. The source's preliminary scalar
steps contain no hidden smallness choice that would defeat this use.

### R2 and the new vector certificate

For arbitrary real inner product space E, set
g=||a||^2||h||^2-<a,h>^2 >= 0 and t=sqrt(e). Using
||a||^2+b^2=1, direct expansion gives exactly the manuscript's

    Q = ||bh-tsa||^2+s^2+g,
    3Q-b^2(||h||^2+s^2)
      = ||bh-2tsa||^2+||bh-tsa||^2+3g
        +(3-b^2-2t^2||a||^2)s^2.

For t^2 <= 1 the last coefficient is at least 1+b^2. The lower
bound b0^2/3 follows from b0^2 <= b^2; the upper bound 2 follows
from the original Q by dropping its negative square and using e <= 1.
No coordinate split or a != 0 assumption remains. In the paper's
parameter family b >= b0 > 0 implies b0^2 <= b^2 as needed.

The fresh Lean source theorem is the actual sqrt(e) physical form,
not just a renamed scalar statement. It assumes the unit relation,
0 <= e <= 1 and b0^2 <= b^2 and proves both printed bounds for all
a,h,b,e,s,b0. Its seven proofs were elaborated from source afresh
against the existing pinned mathlib oleans; all seven #print axioms
outputs list only propext, Classical.choice and Quot.sound. The
original three scalar proofs were separately re-elaborated as well.
The mathlib package's detached HEAD file equals the receipt pin.
No lake update/build or write inside formal/ was used. The reusable
runner and complete audit outputs are in [checks/](checks/).

The paper separately pays what the formal theorem does not:
|M_d(q)-M_d(0)| <= 4r+3r^2 < 5r; rho=min(1/8,b0^2/30) therefore
leaves eigenvalues in [b0^2/6,3]. B_d >= 3/4 on this ball, so the
max switch does not affect C2 regularity. For Y >= 0,
tr(MY) <= 3 tr(Y) <= 3N||Y|| and tr(MY) >= (b0^2/6)||Y||.
Thus the operator-norm Savin constants are exactly b0^2/6,3N,
not b0^2/6,3. Endpoints e=A=d=epsilon=0 cause no loss of these
family constants. Parameter derivatives are not required, so sqrt(e)
does not spoil the jet C2 bound. The subsequent amplitude scaling,
not the zero-jet formal result, supplies proportionality to ||W||.

### P3–P6: exact appendix delta

The actual diff equals the recorded `appendix-final.diff` byte for
byte. Its five groups are provenance; split-to-aligned; m=1 Harnack;
PDE-plus-FIT closure; and positive-time semiconcavity. Nothing else
was inserted, removed or altered relative to the reviewed appendix.

For P4, bounded fit parameters at a fixed center/radius follow from
the source's equation-free fit comparisons. Extract them separately
for that pair. On |ell| < R, |h-p ell| < R the limiting coefficients
put the same increment in all sufficiently late fitted boxes; pass
the inequality and use continuity to reach the boundary. The PDE
passes through strict test contacts on finite jets. The function
subsequence remains fixed and C0 is unchanged. This proves all-center,
all-radius existence, rather than asserting an uncountable diagonal
subsequence. The normalized extremal limit consequently stays in the
same PDE-plus-FIT class required by the rigidity proof.

For P5, extend w(x) as w(x,z)=w(x) on a product neighborhood and
B as diag(B(x),1). Fubini and D_z w=0 give the three-dimensional
weak equation. Ellipticity constants become min(lambda,1) and
max(Lambda,1), still finite and positive. Nonnegativity and local
regularity transfer, so three-dimensional solution Harnack restricts
to the original plane. This concerns the linear comparison solution,
not an unjustified Harnack claim for an arbitrary viscosity solution.

For P6, D_xx^2 W <= I/t and t >= t_min > 0 give one spatial
semiconcavity constant 1/t_min on each compact positive-time cylinder.
Envelope continuity is supplied by the stated geometric envelope
interface. After the displayed changed-PDE calculation, Lemma A.2
therefore applies, followed by the contact theorem. There is no
implicit full-gradient or time-Lipschitz assumption on the original V.

## Presentation and remaining objections

**No mathematical or presentation objection remains that conditions this
manuscript gate.** The proofs are concise in places, but the replaced
operations and their quantitative choices are present. It would be harmless
to print omega^(i+1)(x)=omega^i(tx) next to the reference update; this
is already the rescaling referred to in the current text, and the
reconstruction above verifies that the printed estimate has the right
normalization. This is an optional readability suggestion, not a repair
needed for the verdict.

The candidate/pending-review banner describes the status at freeze time;
it is not a mathematical assertion of acceptance. Updating that status,
authorship/license decisions and release assembly are parent tasks and
would create new bytes requiring their own binding. Nothing in this review
certifies worldwide priority or full inhomogeneous regularity.

I checked all 21 pages on the six hash-matched contact sheets, and inspected
pages 4,10,11,18,19,20 individually at their saved full-page resolution.
The new reference update, Gram/SOS certificate, Savin constants, Harnack
lift, fit-limit passage and common semiconcavity constant are all legible.
No clipping, missing symbol, equation overlap or unresolved reference was
seen. The PDF's freshly extracted text equals the consolidation text and
has 21 page breaks. There are 41 unique labels, 11 bibliography keys,
no unresolved internal references/citations, and no actual TeX warning.
The string `Providing info/warning/error messages` is package metadata,
not a diagnostic. I inspected the existing frozen PDF; I did not rebuild
or mutate it. Visual and hash checks support identity/presentation, not
the truth of the proof.

## Reading boundary and runnable evidence

[source-map.md](source-map.md) gives the primary theorem interfaces and
the precise reading boundary. In particular, upstream OpenAI truth is
stipulated; Kotschwar–Ni, Moser, Savin's earlier Harnack theory, weak/viscosity
equivalence, linear Harnack, Lax–Milgram, traces, Alexandrov and standard
compactness remain credited classical inputs, not newly reproved results.
I did not infer the manuscript theorem from a build, hash match, earlier
proof verdict or finite numerical experiment.

Run from the repository root:

    python3 -I frontier/campaigns/2026-10-14/p-gradient-manuscript-review-r1/checks/run_checks.py

The runner verifies the frozen receipts and four reviewed input hashes,
the exact appendix delta, static references, PDF extraction/log, pinned
mathlib HEAD and fresh elaboration plus axiom audit of all ten scalar/vector
support lemmas. It only writes inside this review directory. Its output is
[checks/run-output.json](checks/run-output.json). It is reproducibility
support, not an analytic theorem prover.
