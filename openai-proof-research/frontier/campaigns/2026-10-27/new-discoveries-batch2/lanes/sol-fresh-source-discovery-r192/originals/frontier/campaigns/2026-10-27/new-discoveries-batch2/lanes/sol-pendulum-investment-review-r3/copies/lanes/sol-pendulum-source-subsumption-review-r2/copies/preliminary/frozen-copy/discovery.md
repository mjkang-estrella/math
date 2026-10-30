# r166 discovery record

UTC 2026-10-30, America/Los_Angeles 2026-10-29. Three precise source claims
screened. One complete ordinary full-scope proof candidate, zero accepted or
independently cleared discoveries. No Lean or manuscript was made.

The selected claim is da Costa–Grinfeld–Pinto–Xayxanadasy,
*Bifurcating solutions in a non-homogeneous boundary value problem for a
nonlinear pendulum equation*, arXiv:1907.13009v1 (July 2019), equation (14)
and section 4.4 Conjecture 1, MathDB343384. For every 0<phi<pi/2, the
actual z-parametrized time map is convex for every 0<z<2. This is the
squared initial ordinate parameter z=y(-L)^2, not the unsquared ordinate,
not just the bounded-orbit interval and not just positivity at stationary
points. The full literal statement is reproduced and proved in PROOF.md.
The current abstract page lists v1 only; the retrieved HTML body explicitly
has that version and still states the conjecture. The paper's Lemma3 is a
local boundary result; equations (21)–(30) and its Smoller discussion were
read, including the reported failed global sign analysis. No inference
from its open label or MathDB's empty solution array is made.

The new route substitutes t=1-cos(2x) in both integrals. Their endpoints
become complementary parameters a=1-cos(2phi) and z. Expanding only
(2-t)^(-1/2) gives positive multiples of M_n(a,z). Complementarity makes
M_0 constant; M_1 is pi(a+z)/2-2sqrt(az), strictly convex. For n>=2 the
moving-endpoint piece becomes the positive convolution of (z-y)_+^(n-1/2)
with (a+y)^(-1/2). Its convexity and that of the fixed-endpoint piece
settle every n. Positive pointwise summation finishes the full conjecture.
This does not differentiate the infinite series. The ancillary strict
curvature lower bound in PROOF.md is one consequence, not another result.

The strongest stress cases are a or z near zero, where direct curvature
formulas have large cancelling terms, and a or z near 2, where convergence
of the binomial expansion slows. Neither is removed from the theorem.
The n=0 moving-endpoint moment by itself is not convex: it is
2 arcsin sqrt(z/(a+z)); its derivative is sqrt(a)/(sqrt(z)(a+z)) and its
second derivative is strictly negative. Thus claiming that *every separate
moment integral* is convex would be false. Complementary endpoint
cancellation is essential in the exceptional orders 0 and 1. For order
1 the negative second derivative of the square root in the combined
closed form supplies strict positivity. No counterexample to the source
claim was found or is claimed.

Failed/retired routes: equation (21) has a negative boundary term when
g=z^2-2(1-a)z-2a<0 (for instance a=z=1). Discarding that term cannot give
a lower bound. Boundary asymptotics are pointwise in phi and do not prove
global convexity. Positivity of the source's modified Phi only at
stationary points would prove a weaker single-minimum conclusion, not
the full convexity claim. A recurrence for M_n and finite derivative
samples suggested positivity but could not establish all n; the
positive-part convolution argument closes that gap analytically.

Bounded checks: analyze.py supplies 63 35-digit direct-curvature versus
independent numerical differentiation controls, and 12 moment-polynomial
derivative profiles sampled at 101 positive ratios each. checks.py compares
the source map with the transformed moments, checks M_0/M_1, verifies the
moment recurrence in orders1–5 at six parameter pairs, tests the order2–5
convolution second-derivative identity (24 controls), and compares six
100-term series with a proved geometric tail upper bound. Floating
roundoff is allowed explicitly; tiny tails below working precision are
not certified to their displayed number of digits. All63 curvature values
also satisfy the proposed universal lower bound. These are diagnostics,
not a universal proof or interval-arithmetic certificates.

The two parked claims, with no sustained attempted resolution:

* Nüsken–Pavliotis, *Constructing sampling schemes via coupling: Markov
  semigroups and optimal transport*, arXiv:1806.11026v1, Definition6 and
  Conjecture11, MathDB339679: convexity of the set G of coupling operators
  annihilating marginal functions for which the closure of the perturbed
  sum of marginal generators generates a Feller semigroup. Finite-state
  rate-matrix convexity does not resolve arbitrary unbounded generators:
  the closure/generation condition is the remaining analytic obstruction.
  The source's actual definitions, Proposition8 and conjecture body were
  read. Conjectures17/19/60 in that paper are context, not extra screened
  candidates. No complete routine-exclusion bridge is asserted.
* Drăgănescu–Spinu, *Sharp estimates for the convergence rate of Orthomin(k)
  for a class of linear systems*, arXiv:1109.2669v3 (14 January2025),
  section5.3 Conjecture12, MathDB322191: for A=I+rho diag(zeta_j),
  |zeta_j|=1 and 0<rho<1, does -rho in Hull(zeta_j) imply q_n->rho?
  Source initial-data/active-support qualifications matter. The actual
  Proposition13 two-dimensional periodicity calculation and Theorem17
  small-rho root-of-unity proof were read. A zero residual coordinate or
  a two-dimensional shortcut is not proposed as substantive new work.
  Full active-support asymptotic dynamics were not solved here.

Historical screen: history-receipt.json reuses r157/r159/r162/r164
original-role records; initial9 changed/new records were refreshed.
Final surname/title refresh records1681 paths and10 changed/new records, with no round cutoff and r111–r113
science explicitly retained. Exact IDs/arXiv aliases and word-boundary
authors were searched. The initial claim-alias screen had no hits. The
expanded author screen found r76 and its review copies through Grinfeld;
their silicosis power-law classification was reopened and is unrelated
to the pendulum boundary-value problem. The final surname-complete refresh
also reopens r111 Costa entropy concavity, unrelated to this pendulum claim.
No reopened old target is renamed
fresh. Generated copies inherited from older inventories are retained
where role qualification is ambiguous, making the search conservative.
The r159 explicitly identified generated echoes are excluded by role.
The complete title strings and all four common surnames are covered by
the stored pattern/receipts, subject to the process timing note below.

Current-public-proof comparison: the observed fixed Omega head is
d36a58e865e46580f127ef7a09d64ccbc2370296 and OpenAI head remains
4eaee87548250b2682affda7d05d947c05554bae. The Omega delta from the user-given
1b21e83 head has7 files across14 commits, with no target path hit. Base full
inventories plus inherited fixed deltas and the current delta were searched
for IDs/title concepts/authors and time-map/incomplete-beta terms. Current
IncompleteBeta Result/Moment and IncompleteBetaShape Result *proof bodies*,
including the two actual Lean Result files, were fetched and read. They
prove gamma-coefficient Turanian signs by fixed-sum beta-shape comparison;
they do not state the complementary-endpoint time-map convexity theorem.
This is a concrete comparison with those bodies, not an assertion that
every dependency or all literature was cleared. No Lean builds were run.

Eligibility remains HOLD. The classical convex-convolution principle is
standard, and an independent reviewer must decide whether the full
exceptional-moment/cancellation bridge is a routine adaptation excluded by
the campaign. Its elementary length alone settles neither decision.
No claim of new-to-literature priority is made. The Crossref title query
returned unrelated records, so it did not establish the published-version
history or rule out a later published solution. Public proof registries
retain the inherited aa026->a19a and a19a->490f300-path coverage gaps.
Path searches do not supply semantic absence clearance. These limitations
are reasons for zero credit and no formal/manuscript investment, even
though the ordinary analytic proof is complete.

Access/process limits: export.arxiv.org API returned429 once and was not
retried or bypassed. Successful arxiv.org primary HTML reads used the
ordinary public source service, not an export-API workaround. Two attempted
MathDB listing query parameters were ignored (identical returned hashes);
the correct /api/search endpoint was then used. Initial shell inventory
used unguarded pwd/rg/head, contrary to the requested helper wrapper; this
is retained as a process defect, not represented as guarded. Subsequent
retrieval, numerical work, hashes and checks use the unchanged designated
helper_guard.py; native bounded reads/apply_patch are used as allowed.
The expanded author check occurred after the initial primary fetch,
although exact IDs and claim aliases were checked beforehand. This order
does not satisfy the strict requested author-before-download sequence;
no eligibility PASS is claimed. All source bytes and failures are retained.

Counts remain9 additional/39 total,next40. Root/independent review alone
can adjudicate a candidate; no shared record was edited.
