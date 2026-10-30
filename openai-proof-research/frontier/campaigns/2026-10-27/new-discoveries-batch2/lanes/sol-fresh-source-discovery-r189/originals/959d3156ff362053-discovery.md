# r74: literal sharp Chernoff curvature conjecture — unresolved, credit 0

Research date: 29 October 2026 UTC. Solo; assigned lane only. No nomination,
PROOF.md, Lean, paper, git operation, child, browser tab, account, external contact,
post or upload. Root alone owns acceptance and the unchanged counts 7 additional,
37 total. This is a full-source attempt, not a claim of thirty achieved outcomes.

## Context and early screen

Read ancestor openai-proof-research/AGENTS.md and batch AGENTS.md, NEXT, ledger,
prior-campaign-context; read r57–r72 summaries and searched all older batch lane
summaries before selecting. context-reading.json retains the recent texts and
input hashes. The full ledger/context were parsed and copied inside this lane.
No older summary hit for Chernoff/Balabdaoui/Wellner/Palafox/these source IDs was
found in the bounded screen. No worldwide or cross-campaign exhaustive clearance.
The initial broad file listing was truncated; targeted reads followed. The first
combined context read also exceeded tool output limits; saved complete context
and targeted summaries replace that truncated view. Retired Zinn, squared-radius
convolution, Bessel, arithmetic and edge-irregulator work were not pursued.

Four expert-attributed primary questions screened:

1. Melbourne–Tkocz, arXiv:2005.10930v1, Conjecture 5.1: every finite monotone
   log-concave positive sequence x, t ↦ log(t sum x_i^t) concave for all t>0.
   EXCLUDE PRIOR: Melbourne–Palafox-Castillo arXiv:2111.06997v1 Theorem 1.1 proves
   precisely this, even for summable sequences. Read full Section 3: layer-cake
   distribution crossing, matched geometric p-moment, convex-order comparison,
   geometric curvature, and final interpolation. Finite sequences extend by zeros;
   alternatively take positive truncations. Public theorem is 13 November 2021,
   Annals of Applied Probability 33(6A), 2023, 4322–4340. Actual downloaded PDF is
   v1; live abstract lists only v1. Author-hosted route gave404; independent arXiv
   source succeeded. No new credit for rediscovering the theorem or its stronger
   already-refuted concave-sequence analogue.
2. Balabdaoui–Wellner, Bernoulli20(1)(2014)231–244, **Conjecture3.1 pp239–240**:
   for standard Chernoff Z=argmax(W(t)-t²), density f, and
   sigma0 = [-(log f)''(0)]^(-1/2), EVERY sigma≥sigma0 has
   f(x)=rho_sigma(x) phi(x/sigma)/sigma with rho_sigma log-concave on R.
   Selected the FULL printed sharp claim, not just existence of some sigma.
   Author-hosted actual published PDF read; original Section2 proof and Section3
   partial proof read. Its equivalent statement is w(x)≥w(0), all real x,
   where w=-(log f)''. Expert identities and attribution are in the actual paper.
3. Pinelis MO479107 (18 September2024): for every Gram matrix of six unit
   vectors in R³, with u=sum g_ij², v=sum g_ij g_ik g_jk, does u≤15/4 preclude
   u-v<23/8? EXCLUDE PRIOR: GH from MO's actual 19 September2024 answer proves
   u≥3 and 27(u-v-3)²≤(u-3)³. Read full eigenvalue/cubic-discriminant proof:
   rank≤3, trace powers through3, shifted characteristic polynomial
   t³-(u-3)t+2(u-v-3). This gives the exact requested inequality immediately.
4. Pinelis MO481234 (25 October2024): existence of a law on
   {(x,y,z) in [0,1]³:x+y+z=3/2} with all three marginals uniform. EXCLUDE PRIOR:
   actual question explicitly links Bogdanov's same-day MO481225 answer.
   Read its actual piecewise construction: U uniform[0,1]; for U<1/2 set
   (X2,X3)=(1-2U,1/2+U), otherwise (2-2U,U-1/2). Sum is identically3/2;
   both marginals are uniform by the two linear branches. No reliance on an
   unanswered label: source's answer count is misleading here.

MO full text was read through public web search/open; direct HTTP403 attempts
are preserved, not retried. See sources/web-reading-receipt.md for primary URLs,
chronology and access limits. Five-point circles appeared incidentally in a
search and already had a public counterexample; it was not a selected expert
question or a research investment.

## Current registries and closest actual proof bodies

Before substantive computation: screened dated complete named Omega Problems
and **Blueprint** D5 trees cached in r57, and primary live searches, plus live
raw Omega and OpenAI README responses. No GitHub API call: inherited shared
403/429 hold remains. Latest OBSERVED Omega6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3
at15:49UTC is NOT currentHEAD. No current full delta/head clearance. The r57 dev
Blueprint snapshot is3b4135a35caa0ae817cf5eca51d605b098027fd2; it is not Lean.
registry-cache-screen.json records lexical hits, not proof of absence.

Read actual pinned Problems/salek-hayashi-winter-2020-harrow-parallel-chernoff-
exponent.md and actual D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.lean.
The latter's `result : ¬ claim` refutes convergence of a quantum-channel
parallel discrimination exponent to1 using an exponent≥2 witness. Different
objective and source; name 'Chernoff' does not subsume a probability density's
curvature. No Lean compilation or independent validation of this registry claim
is asserted. Other broad Renyi lexical hits were not declared substantive matches.
Pinned OpenAI manuscript catalogue/preprints listing has no exact Chernoff density
match in the bounded lexical screen; this is not a live registry absence claim.

**Important public counterpart:** Zhang–Zhou2607.18619v1, submitted21Jul2026,
Theorem1 proves v>0, v(x)≥4x, w(x)>4|x|, and inf w>0, with normalized
Laplace transform M(s)=Ai(0)/Ai(2^(-1/3)s), v=-(log g)'', f=Cg(x)g(-x).
Read the complete actual PDF and HTML proof: exponential peeling Lemma2,
residual-series Proposition4, Corollary5, Airy convolution Lemma7 and final
compactness argument. Their conclusion inf w>0 does **not** supply w≥w(0).
Their abstract calls the conjecture proved but does not claim the sharp constant
in the theorem/proof. This report does not challenge their proved weaker theorem.
PDF dated22July and HTML dated24August under same v1 have differing layout and
numbering; both bodies agree on these bounds; hashes are saved separately.
The count-ex-machina historical README also lists this public weak settlement.
No additional outcomes can be claimed for strong log-concavity, strict positivity,
tail estimates, compactness, convolution closure or Gaussian concentration.

Eligibility remains HOLD: a sharper numerical constant in an already publicly
settled family could still fail root's substantive-discovery gate. The only reason
to study this precise endpoint is that it is the entire original printed universal
Conjecture3.1. No priority or eligibility PASS is claimed.

## Ordinary proof attempt, route A: finite exponential curvature

The original paper already proposes this route. It is NOT a new mechanism.
Let X_j be independent exponentials of distinct positive rates lambda_j,
b_j=1/lambda_j, and f_m the density of sum_{j≤m} X_j. For t>0,

f_m(t)=sum_j c_j exp(-lambda_j t),
c_j=lambda_j product_{i≠j} lambda_i/(lambda_i-lambda_j).

Write d_k=f_m^(k)(t). The numerator of [-(log f_m)'']'' is

P=-d4*d0³+4*d3*d1*d0²+3*d2²*d0²-12*d2*d1²*d0+6*d1⁴.

A uniform P≥0 theorem for all m,t and the Airy rates would make v convex, hence
w(x)=v(x)+v(-x)≥2v(0)=w(0) by midpoint convexity, proving the FULL source.
Here is the otherwise missing limit justification: the centered reflected partial
sums d+sum_{j≤m}(b_j-X_j) converge in law. Their characteristic functions converge
pointwise and, for m≥K, their moduli are bounded by product_{j≤K}(1+b_j²u²)^(-1/2).
Take K≥6: this majorizes |u|^k times the transforms integrably for each k≤4.
Dominated Fourier inversion gives uniform convergence of derivatives through4.
On every compact set the limiting g is strictly positive, so logarithmic curvature
and its second derivative converge. Since sum b_j diverges, reflected supports
eventually contain any fixed compact set. Thus a uniform finite-rate curvature
inequality passes to Airy g. This is a conditional reduction, not a proof of P≥0.

Exact bounded checks enumerate all3784 subsets of rates{1,...,12} of cardinality
2..8 at t=log2, so exp(-lambda_j t)=2^(-lambda_j) is rational. All P≥0.
Four independent symbolic differentiations in y=exp(-t) agree with the formula.
This is only one time point and finitely many rate sets; it proves no uniform
finite-exponential or Airy claim. Repeated rates are not covered by this checker.

Remaining gap A: prove P≥0 for the Airy rate prefixes at ALL interior times,
uniformly in m, or establish Airy-specific convexity directly. Generic
log-concavity gives only d1²-d0*d2≥0, not this fourth-order inequality.

## Route B: differentiated Airy convolution

Use the actual public Lemma7, not an inferred catalogue claim. Put s=g'/g,
R_x(u)=g(x+u)/g(x), D=s(x+u)-s(x), and
r(u)=2u sum exp(-lambda_j u). The public identity is

A(x)=integral_0^infty r(u) R_x(u) du = x²+s(x)/2.

Since g is log-concave, D≤0, giving A'≤0 and the already-public v≥4x.
A further formal differentiation gives

A'''=integral r R [D³+3D(v(x)-v(x+u))+v'(x)-v'(x+u)] du = -v''/2.

Unlike the first derivative, the integrand has competing signs. Log-concavity
alone does not sign its bracket. No assertion of a signed third derivative of
this integral is made; the additional differentiation/interchange estimates
would also need to be justified before using this as an analytic proof.

Remaining gap B: sign this full integral, or otherwise compare v(x)+v(-x) with
2v(0). Neither dropping its mixed term nor just reusing decreasing R suffices.

## Route C: compact interval and exact obstruction to a shortcut

The public w(x)>4|x| implies the full sharp question reduces to
0≤x≤C with C=w(0)/4 (w is even). The precise cleared numerator is

N(x)=g(0)²[(g'(x)²-g(x)g''(x))*g(-x)²
             +(g'(-x)²-g(-x)g''(-x))*g(x)²]
      -2*(g'(0)²-g(0)g''(0))*g(x)²*g(-x)².

The target is N≥0 on[0,C]; N is even and N(0)=N'(0)=0. A local positive
second derivative bound followed by rigorous compact interval enclosures would
suffice. No such continuum certificate is supplied here. Uncertified Fourier
quadrature at two meshes only estimates w(0)≈3.40518984290345, C≈0.85129746.
It diagnoses v''>0 at81 grid points[-1,1], with smallest sampled value≈0.74907.
Agreement to approximately2.8e-14 is NOT an error bound; neither SciPy Airy
values nor Simpson/truncation errors were enclosed. This cannot establish N≥0.

Even the conjunction of all public final curvature bounds is insufficient for
this shortcut. Set H(x)=x^4+x²-cos(10x)/100 and p proportional exp(-H).
This is an even, positive, analytic integrable density. Its curvature is
W(x)=12x²+2+cos(10x)≥12x²+1>4|x|, since
12t²-4t+1=12(t-1/6)²+2/3>0 for t=|x|.
But W(0)=3 and W(pi/10)=1+3pi²/25<73/25<3, using pi<4.
Thus symmetry, analyticity, strong log-concavity and the public linear tail bound
DO NOT force a minimum at zero. This density is not asserted to be reciprocal-
Airy or PF-infinity. It is a rigorous route obstruction, NOT a source refutation.

## Strongest objection, falsifiers, decision

Strongest mathematical objection: all actual sign requirements remain unproved.
Finite positivity plus a public weak theorem is not the sharp source theorem.
Strongest eligibility objection: the public2026 work already settles strong
log-concavity, and this sharper source constant may be treated as ineligible
family refinement. No 'formulation correction' outcome is sought.

Source falsifier: a certified real x with w(x)<w(0), including exact Airy
normalization and controlled infinite integral tails. Route-A falsifier:
an Airy-prefix m,t with P<0 (this alone would NOT refute the full source).
Eligibility falsifier: any pre-existing complete sharp w≥w(0) theorem or an
actual public proof body deriving the sharp constant, or root's family exclusion.

No complete ordinary proof/refutation. No PROOF.md, Lean/paper investment,
nomination or count change. Full remaining gap is N(x)≥0 on[0,w(0)/4], or a
rigorous admissible negative witness, AND source/priority/substantiveness gates.

## Reproduction

`bash run.sh` runs exact_check.py and attempt.py under the copied recent
capped_run.py: AS/groupRSS512MiB, group CPU210s, wall230s,40ms sampling,BLAS1.
Exact symbolic checks and rational arithmetic are separated from floating
Airy diagnostics. Replay guards report success, peaks below85MiB. No raised
limits. Online collection scripts also used the same guard. Failed source
requests and all initial/replay logs remain. Versions/hashes/UTC/access limits
and the artifact manifest are in provenance.json. No network needed for run.sh;
Python needs sympy, numpy and scipy already present in the environment.
