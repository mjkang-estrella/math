# Full entropy-bound conjecture: no resolution

Research UTC: 2026-10-30 (local task date 2026-10-29). Credit zero. No PROOF.md,
Lean, manuscript, acceptance or count change. This report preserves completed
method analysis without promoting it to a source result.

## Selection and exact source

Three leads were screened. Wu–Yu–Guo 2312.01819, Tsallis heat-flow complete
monotonicity, is an old r5/r60/r84 screen; the complete r5 original was reopened.
Chan–Kalai–Narayanan–Ter-Saakov–White Gaussian convex-hull/Radon log-concavity
is the old r47/r116/r129 family. The complete r116 original and original r47/r129
scientific descriptions were reopened. Neither was downloaded or pursued here.
The third lead is Almasi–Moradpouri–Shahbazi, arXiv 2503.17880v1,
*Quantum Regular Black Holes and Complete Monotonicity*, and its substantially
revised published version *Regular black holes and complete monotonicity*,
JHEP09(2025)208, DOI 10.1007/JHEP09(2025)208, published 2025-09-26.

The selected precise claim is the published Entropy Bound Conjecture in Section
4.3, printed p16, called Conjecture 4.3 in Section 4.5. It asks whether every
true dressed Schwarzschild black hole in the source class has S>A_h/(4G).
It is NOT the vague unrestricted perturbation assertion of preprint Section
2.3: the journal no longer presents that as a separately labeled conjecture.
The surviving full geometric scope includes the Section 4.5 ansatz

 ds²=-(1-F(r))dt²+dr²/[H(r)(1-F(r))]+r²dOmega²,

positive bounded H, regular center, Schwarzschild classical/asymptotic limit,
and completely monotone expansion theta and Kretschmann K. Source Definition
4.1 also restricts the scales to the mass and Planck length. Natural completely
monotone representations are the actual constructive class of Sections 3–4.
An admissible horizon is a positive root F(r_h)=1; the thermodynamic branch
and mass dependence must be retained. Restricting to H=1 would discard the
documented unresolved part. This lane proves neither the assertion nor its
negation on that full class, and does not claim that the physical word 'true'
has a source-independent mathematical definition.

Before retrieval, all 1,643 full indexed original-role bodies were searched by
ID, both titles, all three authors and perturbativity/curvature aliases; no
matching body was found. After reading the journal, the exact entropy-conjecture,
DOI and dressed/quantum aliases were separately screened with no match.
The index reuses r151's qualified r148/r147/r145 ancestry and refreshes changed
or new immediate original science roles. Generated inventories are not used as
science. Inherited repeated scientific copies remain visible, rather than being
mistaken for independent evidence. No r111–r113 science is removed.

## Source bodies and proof-facing comparisons

Actual preprint and journal bytes, actual current arXiv version/history, and
publisher HTML were obtained. Read published Sections 2–4, particularly
Theorem 3.1, Definition 4.1, equations 4.19–4.23 and 4.25–4.36, and the
adjacent proofs. The abstract's broad bound is not a proof of the full
Section 4.5 scope. Equations 4.19–4.23 establish the restricted H=1 bound by
bounding the incomplete gamma integral by Gamma(3/2). They do not control H.

Followed the source's closest actual entropy reference [55], Belfaqih et al.
2407.12087v1, actual equations 209–212 and 274–276. They concern covariant
holonomy models and a mass-independent lambda, with an explicit model entropy
above Bekenstein–Hawking at the horizon. No universal arbitrary-H implication
is stated in those read passages. The source journal cites a later published
version with an additional author; this lane has not body-compared that VoR.
Thus this companion comparison is partial, not full prior-art clearance.

Current registry heads observed 2026-10-30T00:49:44Z: Omega
b62773edfb6a6f7806de09b593b2e3b6834685c7 (commit 00:43:41Z), OpenAI
4eaee87548250b2682affda7d05d947c05554bae (commit 00:35:35Z).
The fixed 490f6bcc→b62773ed comparison contains 65 commits/38 files;
7ef5c0cc→4eaee875 contains 2 commits/281 files, both below the path cap.
The two inherited earlier 300-path caps REMAIN; these new intervals do not
close them. Complete cached baseline path inventories were target-screened,
not semantically cleared. Read the current actual matching Kretschmann-named
Library body: it is about quantum channels/Stinespring continuity, not curvature.
Read the current isotropic-entropy main file: its bound is for log-concave
densities/covariance, a different object. It imports further theorem bodies;
the main file alone cannot clear every potential subsumer. No current public
proof link resolving this exact conjecture was located. No public exclusion,
worldwide priority claim or full current-registry clearance is asserted.
The actual imported scalar-estimate proof body and changed finite-fiber
topological-entropy theorem were subsequently retrieved and read as well;
their hypotheses concern spectral/probability estimates and compact factor
maps, respectively. Neither supplies the black-hole implication. This is a
bounded comparison of those bodies, not a review of their full dependencies.

## Sustained analysis: the general-H obstruction

Write q=sqrt(H)>0 and I(x)=integral_0^x sqrt(y)/q(y) dy. The journal's lower
bound 4.36 is

 L_H(R)=(32*pi/9) integral_0^R x^4/[q(x) I(x)^2] dx.

At H=1 it is 4*pi*R². It is tempting to hope L_H(R)>=4*pi*R² from positivity,
boundedness and the endpoint values H(0)=H(infinity)=1 alone. That hope is
false, even for smooth positive H>=1. The following is a method falsifier,
NOT an admissible source counterexample (K and theta are not supplied).

Choose a smooth nonnegative cutoff eta equal to 1 on [0,1] and zero on [2,infinity).
For epsilon>=0 let q_e(x)=1+epsilon*x²*eta(x), H_e=q_e². These functions satisfy
all the preceding scalar regularity and endpoint conditions. On [0,1],

 I_e(x)=(2/3)x^(3/2)-(2/7)epsilon*x^(7/2)+O(epsilon²*x^(11/2)).

The remainder is uniformly bounded in absolute value by
(2/11)epsilon²*x^(11/2), using 1/(1+u)=1-u+u²/(1+u).
For 0<=epsilon<=1/100, I_e/I_0 is bounded below by 1-(3/7)epsilon.
Differentiation under the x integral is justified by an integrable constant
times x bound on the derivative of x^4/(q I²), uniformly in epsilon.
Consequently

 d/depsilon [x^4/(q_e I_e²)]|_0 = -(9/28)x³,
 L_H_e(1)=4*pi-(2*pi/7)epsilon+O(epsilon²).

In particular L_H_e(1)<4*pi for all sufficiently small positive epsilon.
This is an analytic all-small-epsilon conclusion, not a numerical fit.
More generally q=1+epsilon*x^m on [0,1] has

 L'(0)/(8*pi)=(3-2m)/[(2m+3)(m+2)],

negative for every integer m>=2. The exact checker verifies the formulas
through m=40 and rational remainder controls; those finite checks are not
the universal argument, which is the displayed differentiation.

The kernel makes the failure transparent. For q=1+epsilon*h,

 L'(0)/(8*pi)=6*sqrt(R)*integral_0^R sqrt(y)h(y)dy
                         -7*integral_0^R y*h(y)dy.

It changes sign at y=36R/49. Positive h near the outer horizon reduces the
bound. Assuming H>=1 is therefore insufficient to make 4.36 prove the claim.
Also L is only a LOWER bound for the entropy area. L<4*pi*R² alone never
implies that the actual area is smaller.

## Coupled curvature route and exact missing step

An independent orthonormal-curvature reduction, with F'=dF/dr, gives

 K=(H F''+H'F'/2)²+2H² F'²/r²
   +2[H'(1-F)-HF']²/r²+4(1-H+HF)²/r^4.

At H=1 this reduces exactly to source 4.3. Together with source 4.26,
theta=q(r² sqrt(F))'/r², it exposes the missing coupled constraint:
choosing a harmless scalar H and a completely monotone theta does not certify
complete monotonicity of K. Squaring signed derivatives in the formula does
not preserve complete monotonicity. For example F=r²/(r+1)^3, H=1 gives

 K=12(r^4-2r³+7r²+2)/(r+1)^10
  =12/(r+1)^6-72/(r+1)^7+228/(r+1)^8
    -288/(r+1)^9+144/(r+1)^10.

Thus even a simple regular mass-linear F has a signed partial-fraction
expansion. The signs do NOT disprove CM: its inverse Laplace density must
be analyzed as a whole. This lane neither assumes an open CM cone under
arbitrary perturbations nor promotes low derivative checks into all-order CM.

There are two further reasons not to turn the lower-bound falsifier into a
source counterexample. First, the journal itself warns that H can depend on
mass. Implicit differentiation of F(r_h,M(r_h))=1 gives
M'=-F_r/F_M, whereas temperature involves F_r with M held fixed. A path
derivative along the horizon is not that partial derivative. Second, if a
regular positive theta has theta(0)=theta0>0 and H(0)=1, then
J(x)=integral_0^x y² theta(y)/q(y)dy~theta0*x³/3. The formal entropy integrand
x^4/[q(x)J(x)^2]~9/(theta0²*x²) is not integrable at zero. The printed
zero-to-horizon entropy formula therefore needs a branch/normalization
interpretation before one assigns it a finite absolute value. This is an
uncredited formulation caution, not a refutation or a repaired source theorem.

The precise unsolved task is to obtain a universal finite, source-faithful
entropy comparison using the actual mass-dependent family, both all-order
curvature CM constraints and a legitimate entropy normalization; or produce
one family satisfying all these premises and a strict reverse comparison.
No such family or inequality is provided here. The scalar first variation
and curvature identities only eliminate unjustified proof shortcuts.

## Eligibility and reproducibility

Strongest objection: the completed work is supporting analysis on a source
whose full geometric/thermodynamic bridge remains unproved. It earns zero,
irrespective of whether the scalar variation itself is routine or new.
No classical or public exclusion is claimed without a complete bridge.
The weighted Bernoulli/Milojevic–Sudakov r154 family, Kazemi and all NEXT
families remain avoided. r155/r156 are untouched.

All executed Python, retrieval, edit finalization and pdftotext helpers run
under the unchanged designated helper_guard.py, AS/group RSS512MiB,
CPU210s, wall230s, nominal40ms sampling, BLAS1 and no bytecode. Native reads
and apply_patch are the permitted exceptions. Sampling cannot exclude
between-sample transients. Initial overly broad native inventory/context
outputs were truncated by the tool; they were not used as absence evidence.
Target screening used full bodies without a global output cutoff. A transient
analyze.py draft containing an import was corrected before any execution;
no failed mathematical run was discarded. Publisher HTML redirected with
a cookie-error query but returned a substantial article body; the journal
PDF is the primary evidence. No access-control bypass was attempted.
