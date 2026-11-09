# Independent adversarial classical-bridge review r3

Recommendation: **EXCLUDE from discovery credit as a routine classical corollary. MATH PASS for the bridge; published-conjecture SOURCE HOLD remains. Credit 0.** Accepted accounting remains 3 additional / 33 total. This is an eligibility recommendation, not a ledger decision or a claim of a previously printed full conjecture theorem.

Reviewed target: `root-mittag-source-subsumption-r3`, task-specified revision label `40baf2c2ad`. No git operation was performed; commit membership is not independently certified. The concrete reviewed object is the worktree byte set bound by `review-freeze.json`: all 31/31 hashes verified before review and copied to `owncopy/`. All 32 target files, including the freeze manifest, were separately inventoried for the before/after preservation check. All review computations and reads of retained sources use my copy. Root's checker was copied as frozen evidence but neither read, imported nor run as independent evidence. The 65-path existing candidate and its 17-module/155-declaration certificate were not edited or replayed; their prior formal completeness is not a new formal audit here.

## Primary evidence actually read

I read repo/batch AGENTS, ledger's standard and accepted/excluded calibration, prior-campaign context, CLASSICAL-BRIDGE, the complete prior `pi-mittag-modulus-final-review-r1/review.md`, Gamma-level ACCEPTANCE and perspective reassessment, and Kilbas review adoption. The prior review's historical 2/32 count is superseded by the current ledger's 3/33; I made no accounting changes.

I visually read all six retained primary page images and checked the actual PDF text bodies: Papadopoulos author PDF pp5–6 ([2], [3], the skew-normal/Owen identity and equal-scale [4]); Patefield–Tandy p1 Eq(1); Mainardi–Pagnini–Gorenflo 2003 p15 Eqs(6.3)–(6.9); Mainardi–Mura–Pagnini 2010 pp12,16 Eqs(4.6),(4.7),(4.18),(4.19). Additional 2010 body text pp10–14 establishes nonnegativity, normalization via the moment formula (4.5) at delta=0, transform proofs, and the distinction between even extension and an iid difference. I independently re-extracted all four PDFs and re-rendered/re-read the same six pages from my own PDF copies. Public URLs, full hashes and actual UTC observations are in provenance.json and live-source-checks.json. Fresh Papadopoulos and both Mainardi downloads match retained bytes; the fresh JSS request did not complete after approximately 145 seconds despite a socket timeout and was stopped without retry. JSS body support is the verified retained publisher PDF, not a fresh retrieval claim. The separate 2015 double-half-normal report and Owen1956 original body are not claimed read. The 2014 author PDF, not an unidentified secondary summary, supplies the exact unequal-scale distribution formula.

## Independent complete derivation

Let independent U~N(0,sigma0²), V=sigma1|Z1| and W=sigma2|Z2| with all sigmas positive. Papadopoulos uses precisely these independent components, with sigma1² and sigma2² the variances of the *unfolded* normals, not the half-normal variances. Put s²=sigma0²+sigma1²+sigma2² and theta_j=sigma_j/sigma0. His definitions give

omega1=s sqrt(1+theta2²)/theta1, omega2=s sqrt(1+theta1²)/theta2,
lambda1=(theta2/theta1)s/sigma0, lambda2=(theta1/theta2)s/sigma0.

Equation [2] is f(x)=2 phi(x/s)[G(x;omega1,-lambda1)-G(x;omega2,lambda2)]/s, and p6 gives G=Phi(x/omega)-2T(x/omega,lambda). T is even in x and odd in lambda by Patefield–Tandy's defining integral. In (f(x)+f(-x))/2 the two Phi differences cancel exactly, leaving

bar f(x)=4 phi(x/s)[T(x/omega1,lambda1)+T(x/omega2,lambda2)]/s.

This coefficient is 4/s, not the equal-scale formula's 8/s unless the two T terms coincide. Eq(1) of Patefield–Tandy yields, for j=1,2, A_j(u)=1/(2s²)+(1+u²)/(2omega_j²),

bar f(x)= [2/(pi s sqrt(2pi))] sum_j integral_0^lambda_j exp(-A_j(u)x²)/(1+u²) du.

Relative to normalized N(0,1/(2A_j)) densities its positive weights are sqrt(2)/(pi s sqrt(A_j)(1+u²)) du. They sum to one by Tonelli and normalization of bar f. Its CF at sqrt(t) is the probability mixture of exp[-t/(4A_j)], hence CM. No iid assumption on the two fixed half-normal scales was made.

The singular sigma0=0 case must not be obtained by plugging zero into theta. Independently, put a=1/(2sigma1²), b=1/(2sigma2²), c=ab/(a+b), C=sqrt(ab/[pi(a+b)]), d1=a/sqrt(a+b), d2=b/sqrt(a+b). Directly integrating the convolution on y>=max(0,-x), completing the square, gives, for x>=0,

f_(V-W)(x)=2C exp(-cx²) erfc(d1 x),

and f_(V-W)(-x)=2C exp(-cx²) erfc(d2 x). Thus bar f=C exp(-cx²)[erfc(d1|x|)+erfc(d2|x|)]. The identity

erfc(d|x|)=(2/pi) integral_0^infinity exp[-d²x²(1+u²)]/(1+u²) du

holds also at x=0. For x>0 differentiating the right side gives -2d exp(-d²x²)/sqrt(pi), and both sides equal one at zero. Hence with B_j(u)=c+d_j²(1+u²), the normalized Gaussian mixing weights are

w_j(u) du = 2C/[sqrt(pi) sqrt(B_j(u))(1+u²)] du.

They are nonnegative and integrate to one; this uses probability normalization, not an unspecified proportionality constant. The conditional real CF is integral exp[-t/(4B_j(u))] w_j(u) du. This proves the zero-noise case directly and validates all constants in root's (C),(D). At extreme unequal scales nothing changes sign. Normal smoothing would simply multiply each conditional CF by exp(-sigma0² t/2), agreeing with the published noisy result. Zero half-normal scales, though unnecessary for the positive M-Wright mixing variable, also give a Gaussian real CF or a point mass when both vanish.

For 0<alpha<1/2 set beta=2alpha. Mainardi2003 Eq(6.9) at time1, using the explicit Gaussian kernel, is exactly

M_alpha(x)=integral_0^infinity exp[-x²/(4tau)] M_beta(tau)/sqrt(pi tau) dtau, x>0.

The factor two in (6.9) is essential: the conditional density is a *half* normal of unfolded variance 2tau, with mass one on x>0. Mainardi2010 (4.18),(4.19) reproduce this, and pp10–12 give nonnegative M_beta of mass one. Therefore two independent copies X,X' of M_alpha have independent scales tau,tau'. Condition on BOTH. Conditional V-W is asymmetric when tau differs from tau'; use its real CF (equivalently the symmetrized conditional density) above, not an assertion that it is iid. Integrate its positive probability mixing kernel against M_beta(tau)M_beta(tau') dtaudtau'. Tonelli gives another probability mixing measure. The unconditional difference IS symmetric by exchange of the two iid inputs. Random-sign symmetrization of ONE input would instead give the real part of E_alpha(iu), a different object; it is not used here.

Mainardi2010 (4.6),(4.7) identify the literal entire series E_alpha(z)=sum z^n/Gamma(1+alpha n) and the Laplace transform of X at positive real z. Both transforms are holomorphic on Re(z)>0: on compact sub-half-planes x^k exp(-epsilon x) is bounded and the integrating measure has mass one. The identity theorem extends equality to that half-plane. Let z=epsilon-iu approach -iu; bounded convergence applies to exp(-zX), and the entire series is continuous. Thus E exp(iuX)=E_alpha(iu). Independence now gives E exp(iu(X-X'))=|E_alpha(iu)|². No assumption about an exponential moment on the imaginary boundary is needed.

At alpha=1/2 use directly M_(1/2)(x)=exp(-x²/4)/sqrt(pi), i.e. a=b=1/4 above; do not invoke an ordinary density M_1. The mixture remains a probability measure. After mixing over scales the Laplace rates may be unbounded; for every t0>0 and integer k, r^k exp(-t r) on t>=t0/2 is bounded. Dominated differentiation proves C-infinity and (-1)^k F^(k)(t)>=0 for all k and t>0. Finally splitting the absolutely convergent literal E_alpha series into even and odd terms gives E_alpha(i sqrt(t))=E_(2alpha,1)(-t)+i sqrt(t)E_(2alpha,1+alpha)(-t), whose two components are real. Squaring the modulus is precisely the source expression. This is the full range 0<alpha<=1/2, not a few parameter instances or just log-convexity.

## Own checks

`own_checks.py` enforces RLIMIT_AS soft=hard=536870912 bytes before importing mpmath; it reads no root checker/results. **77/77 diagnostics PASS**, maximal scaled discrepancy 4.04e-33 at 32 decimal digits, about 1.24 seconds. The recorded ru_maxrss is 506028 KiB (a process high-water measurement, not evidence that all that memory was allocated after the cap). These are diagnostics, not mathematical proof.

Different routes: direct half-normal convolution vs the erfc symmetrized density; direct skew-normal CDF definition [3] vs convolution of the erfc density with normal noise; literal closed half-normal CF differentiated independently through order4 vs a compact angular-coordinate probability Laplace integral, at unequal precisions including 0.03:7 and equal precisions; mixing normalization; actual M_(1/4) characteristic transform from an explicit M_(1/2) scale integral vs its literal Gamma series; general noninteger subordination Mellin moments via duplication at alpha=.07,.25,.413. The finite numerical sample is not presented as verification for all alpha or all derivative orders; the argument above supplies those quantifiers. No Lean rerun was needed or claimed.

## Strongest opposing case, calibration and adjudication

The strongest credit case is real: no cited retained body says that symmetrized differences of arbitrary half-normal scale mixtures are Gaussian scale mixtures, and none states the final conjecture. Recognizing that closure, conditioning independently on unequal scales, taking Fourier transforms, and reaching the boundary transform is a useful new-to-this-project theorem. The source authors' conjecture and prior formal effort are not trivialized. The accepted Gamma-level result also had a short classical proof; length alone cannot decide eligibility. Prior review explicitly demanded a published generic closure or a published short bridge, and could reasonably view deriving closure as substantive residual work.

I nevertheless recommend EXCLUDE under this campaign's actual rule against routine corollaries. The material new evidence is a body-read closed distribution formula for *exactly U+V-W with arbitrary unequal half-normal scales*. Its CDF terms cancel on taking the real CF, and the remaining two T terms are positive Gaussian integrals by the defining formula. No new inequality, strictness mechanism, estimated tail, or limiting probability existence theorem is required. The zero-noise bridge can be supplied either by the displayed elementary convolution above or ordinary weak limiting closure; the direct calculation avoids any unresolved theorem premise. Known M-Wright subordination is already for exactly the required family, with exactly the half-normal kernel. Mixing and transform identification preserve the property by standard probability integration.

I compared Gamma-level acceptance paragraph5 and the full perspective reassessment, rather than adopting its reviewer's overly narrow 'same object required' rule (root expressly rejected that rule). There the accepted content included literal Gamma-series normalization, existence and uniqueness on the whole axis, and a two-successive-shift strictness argument that the generic convexity theorem does not supply. Here the known *same conditional distribution* formula itself displays the entire positivity mechanism after a linear symmetrization; the other established formula already supplies the exact all-alpha randomization. That is a materially stronger subsumption bridge than a generic tool without the needed strictness. The Kilbas, Hoggatt and beta-prime exclusion summaries demonstrate that a final statement need not have appeared verbatim in print for routine-corollary exclusion. This judgment does not assert that same-object coincidence is necessary for exclusion or that every short proof must be excluded.

Falsifier of the bridge/exclusion rationale: a failure of Papadopoulos [2] at unequal scales, a negative mixing weight after correct symmetrization, nonprobability M_beta for some beta in (0,1), or a variance/time mismatch in (6.9) would restore a substantive missing mathematical step. The retained bodies and independent convolution/CF derivation rule those out in the current record. A concrete explanation of a nonroutine residual step absent from this complete chain, or an explicit campaign policy counting newly noticed elementary closure consequences despite complete published distribution representations, would warrant eligibility reassessment. Merely observing that no body states the final theorem does not falsify routine subsumption. Conversely, an actual earlier full endpoint theorem would strengthen exclusion but is not claimed found.

## Exact remaining gaps and limits

1. **SOURCE HOLD persists:** CNSNS157 (2026)109758, DOI10.1016/j.cnsns.2026.109758 conjecture page and surrounding definitions remain unread. Corrected BEUN exact-DOI item has zero bundles/attachments; I inspected the retained metadata and empty-bundles response. Its OA label or abstract is not a journal body. No retries of the same ScienceDirect403, De Gruyter challenge or separate-report Anubis barrier were made. Prior author follow-up/formal success do not clear this hold.
2. **No explicit prior full theorem claim:** the relevant published ingredients have actual-body support, but the assembled final theorem and generic closure are my deductions. Bounded source checking is not a worldwide priority determination. No fresh registry sweep, inaccessible citing-body clearance, MathSciNet/zbMATH clearance or fresh candidate replay is asserted in this narrow exclusion review. These remain acceptance gaps if root rejects the eligibility recommendation; they do not block an independently sufficient routine-corollary exclusion.
3. **Revision provenance limit:** task-specified commit label is recorded; without git I attest the 31 frozen hashes and all-target before/after bytes, not immutable-commit membership. Root provenance's retrieval list includes stray string entries ('url','utc',etc.); these are not successful retrieval records. Own provenance records only structured observations and independently downloaded successful bodies.

Final preservation: all 31 frozen hashes verified again in both root and owncopy, and all 32 target files (including manifest) are byte-identical to the before inventory; see after.json. No mathematical gap remains in the classical chain found by this review. This does not rescind, alter, or independently re-certify the existing complete formal candidate. No shared files, counts, contacts, uploads, browser tabs, credentials, git operations or children were used. All written files are in this review lane.
