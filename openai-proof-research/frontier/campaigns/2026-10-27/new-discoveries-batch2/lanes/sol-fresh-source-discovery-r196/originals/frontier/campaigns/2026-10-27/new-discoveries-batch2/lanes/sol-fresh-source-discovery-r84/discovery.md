# r84: analytic/probability source screen — zero eligible discoveries

2026-10-29 UTC. SOLO; no children. Campaign state read: eight additional,
38 total. No count or shared file is changed. No discovery is nominated.
No Lean, manuscript, or PROOF.md is produced.

## Governing context and early duplicate gate

Read ancestor openai-proof-research/AGENTS.md and batch AGENTS.md, ledger.json,
prior-campaign-context.json and NEXT.md. Their hashes/structured context are in
context.json. All 38 accepted titles were read (prior.log); older contradictory
NEXT running counts are historical, not current. The initial report-filenames.txt
inventories report-like names before candidate selection. The guarded gate
inventoried 3368 all-date named FINDINGS/discovery/SUMMARY/provenance reports,
then extracted bounded matching sections (duplicate-sections.json). A second
filename-first rg pass across ALL .md/.json/.txt under openai-proof-research
found 69 target-containing paths, including nonstandard report names;
all-report-target-filenames.txt and all-report-bounded-sections.json retain
bounded sections/hashes and any size skips. These are lexical screens, not a
proof of semantic global absence. r74/r79/r5 actual relevant exclusions were
read, rather than treating catalogue/search hits as novelty evidence.

Only available r82/r83 artifacts were consulted once for overlap: r82's opening
PROOF statement concerns DeWitt–Keith partition-rank congruences; r83's fetch
list concerns isoclinism/structural geometry. Neither was polled or modified.
r81's FGR work was not repeated. No lasso, special-function, mean, or other
excluded family was adopted. Kanter/GGC and renewal results arose in preliminary
search returns but were discarded before selecting a source target; they are
not additional screened candidates or research outcomes.

## Three screened questions

1. Melbourne–Tkocz's finite positive monotone log-concave sequence question:
   is log(t sum_i x_i^t) concave for every t>0? EXCLUDE PRIOR/DUPLICATE.
   Actual Melbourne–Palafox-Castillo arXiv:2111.06997v1 p1 Theorem1.1 states
   strict concavity on all t>0 for every monotone log-concave sequence in l1.
   Thus it covers the finite source quantifiers. Actual introduction and
   theorem body were read; r74/r79 already record this exclusion. Do not
   present either the theorem or a new numerical instance as a finding.
2. Wu–Yu–Guo arXiv:2312.01819v4 Conjecture1, Eq(11), PDF p9:
   for each Tsallis order 1<alpha<2, each positive integer k and t>0,
   (-1)^(k-1) d^k hhat_alpha(p_t)/dt^k >=0 along additive Gaussian heat flow.
   EXCLUDE PRIOR/DUPLICATE. Actual definition and conjecture body read,
   including its explicit limiting implication for Shannon entropy. Actual
   Gu–Sellke arXiv:2605.11656v1 Theorem1 and Proposition1 pp2–3 give a
   finite 17-atom symmetric mixture with 0.36<H_mu^(5)(1/3)<0.37, where
   H_mu=int p log p. This is the wrong Shannon sign. Smooth Gaussian mixtures
   permit the alpha->1 derivative transfer; r5 already documents exactly
   this exclusion. Time conventions differ by a positive factor two and
   cannot repair a sign. No new transfer/counterexample is claimed.
3. Fontana–Semeraro, The Bernoulli structure of discrete distributions,
   arXiv:2410.13920v1 / ECP30(2025) article93, DOI10.1214/25-ECP741.
   Best new lexical lead: the indexed journal text mentions future study of
   concavity of a fiber-volume functional in Bernoulli parameters. The exact
   journal-only future-work sentence and the definition of its theta-indexed
   family have NOT been body-verified. Its scope is therefore NOT certified.
   The author preprint contains the exact closest volume theorem, but not
   that future-work sentence. The full source question cannot be claimed
   resolved from these materials. Independent sustained calculation below
   tests the natural Poisson-binomial interpretation on all dimensions.
   EXCLUDE ROUTINE/SOURCE-HOLD, credit0; no eligibility request.

## Actual source bodies and access boundaries

arXiv abs2410.13920 lists only v1, 17 October2024; full pinned v1 PDF fetched200.
Read its Theorem2.1 (product-simplex fiber structure), Corollary3.1 PDFp9,
Proposition3.1/Corollary3.3 PDFp11, Proposition4.1 and proof pp14–15,
and Section4.2 pp18–19. In the author's notation F_d consists of all joint
laws on {0,1}^d, D_d is the simplex of sum laws, and P(p) is the fiber with
sum pmf p. The actual source yields, for p in the interior of D_d,

    V_d(p) = H^(2^d-d-1)(P(p))
           = C_d product_{k=0}^d p_k^(binom(d,k)-1),
    C_d = product_{k=0}^d sqrt(binom(d,k))/(binom(d,k)-1)! >0.

This literal fiber dimension and volume constant matter. We do not replace
V by a dimension-normalized root or by log V.

Preprint Proposition4.1 calls its binomial restriction concave but its proof
optimizes the logarithm. Direct differentiation distinguishes these properties.
This is a routine correction, explicitly outside the requested credit standard.
The journal indexed result has related language; without its actual body we
make no claim about journal fidelity, errata, or the exact surviving question.
The institutional journal-PDF URL returned HTTP403 on its sole request.
No retry, credentials, challenge solver, alternate proxy, or access bypass.
A mistaken web open of nonexistent arXiv v2 returned404; v1 was then selected
from actual arXiv history. Publisher ordinary HTML returned only an iframe
wrapper, not a read mathematical body. No browser/tab was used.

## Sustained calculation on the natural independent-parameter interpretation

For every integer d>=2 and theta in (0,1)^d, let p_k(theta) be the coefficient
of z^k in product_i(1-theta_i+theta_i z), and define
L_d(theta)=V_d(p(theta)). Every p_k is positive. The following all-d
calculation is complete ordinary algebra on this explicitly specified object,
not a certified identification of the unread journal-only theta family.

Write n_k=binom(d,k)-1, N=sum n_k=2^d-d-1, and
Phi=log L_d=log C_d+sum n_k log p_k. At theta*= (1/2,...,1/2),

    p_k=2^-d binom(d,k),
    (partial_i p_k)/p_k = 2(2k-d)/d,
    (partial_i partial_j p_k)/p_k
       =4((2k-d)^2-d)/(d(d-1))     (i != j),
    partial_i^2 p_k=0.

Proof: differentiate the generating product once or twice. The relevant
coefficients are binom(d-1,k-1)-binom(d-1,k) and
binom(d-2,k-2)-2binom(d-2,k-1)+binom(d-2,k), with out-of-range binomials zero.
Dividing by binom(d,k) gives the displayed identities including endpoints.
Symmetry n_k=n_(d-k) proves grad Phi(theta*)=0.

The Hessian has common diagonal D and common off-diagonal B, where

    D = -4/d^2 sum_k n_k(2k-d)^2,
    B = D+4/[d(d-1)] sum_k n_k((2k-d)^2-d).

For all d>=2 the binomial variance and ordinary sums give

    sum binom(d,k)(2k-d)^2 = d*2^d,
    sum_{k=0}^d (2k-d)^2 = d(d+1)(d+2)/3,
    sum n_k((2k-d)^2-d) = -d(d+1)(d-1)/3.

The first identity follows from the first two derivatives of (1+z)^d at1;
the second follows by expanding the square and using sums k and k^2;
subtracting d sum n_k yields the third. Consequently

    D-B = 4(d+1)/3 >0,
    D+(d-1)B = -4(2^d-d-1) <0.

Thus Phi has a positive Hessian eigenvalue on EVERY contrast direction
v with sum_i v_i=0, and a negative eigenvalue on the all-ones direction.
Since grad Phi=0 and L_d>0, Hess L_d=L_d Hess Phi at theta*; the same
signs hold for the literal volume. The symmetric vector is a strict saddle,
not a local maximum, for every d>=2. Taylor's formula on any nonzero contrast
line makes the midpoint concavity inequality fail in an arbitrarily small
neighborhood of theta*. This is an all-d statement, not a finite-grid inference.

A fully exact interior witness already exists at d2. Here n1=1 and
L_2=sqrt(2)*(theta1+theta2-2theta1 theta2). At the two points
(1/4,3/4),(3/4,1/4), the factor is5/8, while their midpoint has factor1/2.
This disproves ordinary concavity under the stated interpretation with no
boundary/domain issue. It also disproves log-concavity there.

On the binomial diagonal theta_i=t the same exact formula gives

    L_d(t,...,t)=K_d [t(1-t)]^A,
    A=sum k*n_k=d(2^d-d-1)/2,  K_d>0.

It has its unique maximum at1/2 and is log-concave, but for d>=3 it is not
concave: its second derivative has the sign of
(A-1)(1-2t)^2-2t(1-t), positive near0 since A>1.
At d3,t1/10 the bracket is151/50>0. For d2,A1 the diagonal IS concave,
which explains why restricting to the binomial curve can conceal the
contrast obstruction. These observations do not earn separate credit.

## Registry evidence and precise limits

Read CURRENT-REGISTRIES.json from root-edge-irregulator-final-freeze-r1.
Its complete350197-path Omega tree at1b999d9fda71df7537b62327147496d64a6f66ef
and174524-path OpenAI tree at7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a have
hashes matching the provided record (registry-screen.json). Target lexical
matches and nearest Poisson-binomial structure/direction theorem bodies were
read. They concern Bernoulli sum definitions and Shannon entropy-direction
bounds, not the source fiber volume; this is a bounded distinction only.
Live head requests observed Omega23a4ae6f843d1635869b7656fb6bd681121447a8
and unchanged OpenAI head. The r81-reported baseline->e50 comparison was
independently fetched and its two actual changed documentation bodies
inspected; they concern CDSO graph capacity and Fibonacci renewal laws,
not this volume functional. The additional e50->live comparison and its
access state are in final-prior.log/http.json. No claim of complete current
semantic registry clearance or worldwide priority follows from filenames.

## Exact result/gap, strongest objection and falsifiers

No eligible full source theorem/counterexample is supplied. The volume
saddle calculation above has no residual algebraic premise, but its source
question attribution has a MATERIAL gap: actual journal-only theta-family
and exact quantifiers were not read. Moreover, the explicit d2 witness is
routine from the source's existing product formula. Even if journal source
fidelity is later established, this lane recommends EXCLUSION, not review,
Lean, a paper, or count increment. The all-d Hessian cannot be rebadged as
a separate substantive outcome or parameter-family discovery.

Strongest objection: this is precisely the routine derivative/log-versus-volume
correction prohibited by the assignment. We adopt it. A decisive mathematical
falsifier would be an error in the product-simplex volume formula or in the
coefficient derivative identities. A decisive attribution falsifier would be
journal P(theta) meaning a different fiber, or the question asking about a
volume root/logarithm or a restricted direction. No extension to such an
object is assumed. Source retrieval, novelty limits and eligibility are
separate from the finite exact checks.

## Reproducibility and resources

Run `sh run.sh` in this lane. checks.py uses only Python integer/Fraction
arithmetic: exact Hessian identities for d2..80, exact d2 interior midpoint
witness and d3 diagonal curvature. It is NOT a theorem prover or a substitute
for the all-d derivation. Copied improved helper_guard.py caps every research
helper's address space and sampled process-group RSS at512MiB, CPU210s,
wall230s, nominal40ms process-group sampling, all BLAS thread settings1.
No caps were raised. Guard receipts retain actual peaks and exits; sampling
cannot exclude unsampled transients. No git/shared/other-lane writes,
children, browser, account, contact, public posting or upload occurred.
A temporary filename-list output was initially created in /tmp then moved
into this lane; that brief outside-lane write was a scope mistake, with no
shared research content changed. All subsequent outputs stayed in this lane.
