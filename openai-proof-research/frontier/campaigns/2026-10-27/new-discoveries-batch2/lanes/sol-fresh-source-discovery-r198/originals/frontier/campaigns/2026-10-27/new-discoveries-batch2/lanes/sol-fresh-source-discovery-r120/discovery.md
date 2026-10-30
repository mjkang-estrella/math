# r120 — no eligible candidate

Solo research, assigned lane only. No acceptance or count recommendation. No
Lean, manuscript, git, browser, account action, posting or children.

## Exact questions and primary scope

The actual publisher PDF is Jyothi–Ravi–Lakshmi, *Some remarks on open problems
for Nielsen's beta function*, J. Classical Analysis **27**(1) (2026),119–127,
DOI10.7153/jca-2026-27-09. Despite the search engine's 2025/date snippets, the
actual title page says **2026**; received July30,2025. The local filename
`nielsen2025.pdf` is a retrieval label, not bibliographic evidence. Actual PDF
bytes, HTTP200/date/hash and extracted text are retained. Its p120 prints three
questions attributed to Nantomah's 2023 note, DOI10.13140/RG.2.2.22499.94241.
That original DOI returned403; its response bytes are retained and no bypass or
retry was attempted. Attribution here is to the **printed 2026 primary restatement**,
not a claimed read of the inaccessible 2023 original.

For x>0 let beta(x)=integral_0^infinity exp(-xt)/(1+exp(-t)) dt.
All derivative orders below are integers n>=1 (the ordinary kernel also permits
n=0, but no extra source question is asserted).

1. Problem1: decide monotonicity on the entire positive axis of
   F_n(x)=x beta^(n+1)(x)/beta^n(x).
2. Problem2: decide monotonicity of
   G_n(x)=x beta^(n+1)(x)/(beta^n(x))^2.
3. Problem3: determine the sign of
   H_n(x)=beta^n(x) beta^(n+2)(x)-2(beta^(n+1)(x))^2.

I read actual definitions (1)–(5), the questions, Lemma1 and its sign-changing
weight proof, Theorem1's convolution proof, Corollary1, Theorem2 and proof,
Theorem3 and its three-point proof, and Theorems4–5 and proofs. Theorem2 already
answers Problem2: G_n increases for odd n and decreases for even n. Corollary1
already answers Problem3: H_n<0 for every n>=1. Its deduction from Theorem1
uses index n+1 and coefficient n/(n+1)>=1/2; strictness covers n=1.
Theorem2 then differentiates G_n and uses H_n<0 and beta^n beta^(n+1)<0.
Neither assertion is a fresh result. This lane does not independently certify
every assertion or typographical step in this public paper.

Theorem3 gives F_1(1)>F_1(2)<F_1(3), so Problem1 is already answered negatively
at order1. Exact rational enclosures below reproduce those two comparisons
without trusting decimal zeta/pi evaluations. The history scan subsequently
identified **r51**, which screened this exact Problem1 and read this same paper.
Its SUMMARY, discovery and progress and root handback were read. Consequently
Problem1 is an old screened target, not a fresh discovery target. The all-order
observation below does not rehabilitate it.

## Full all-order route, deliberately excluded as routine

For completeness, the exact all-order answer does not need a difficult
inequality or a stronger complete-monotonicity theorem. This argument is
recorded to close the routine objection, not nominated as a theorem.

Write q(t)=(1+exp(-t))^-1, B_n(x)=integral t^n q(t)exp(-xt)dt>0, and
J_n(x)=integral t^(n+1)q'(t)exp(-xt)dt. Then beta^n=(-1)^n B_n and q'(t)>0.
All integrals and all required derivatives converge for x>0. Integrating the
derivative of t^(n+1)q(t)exp(-xt) gives, with both boundary terms zero,

    x B_(n+1)(x) = (n+1)B_n(x)+J_n(x),
    F_n(x) = -(n+1)-J_n(x)/B_n(x) < -(n+1).

At x→0+, q'>0 and q'(t)<=exp(-t) imply
J_n(x)<=Gamma(n+2), while q>=1/2 implies
B_n(x)>=Gamma(n+1)/(2x^(n+1)); hence J_n/B_n→0.
At x→infinity, q'<=1/4 gives
J_n(x)<=Gamma(n+2)/(4x^(n+2)), and the same lower bound for B_n gives
J_n/B_n<=(n+1)/(2x)→0. Therefore F_n has equal endpoint limits -(n+1)
but is strictly smaller at every interior point. A nondecreasing function
cannot be below its left endpoint limit; a nonincreasing function cannot be
below its right endpoint limit. Thus F_n is neither, for every n>=1.
This does not assert a unique minimum, convexity, or any new source question.

**Strongest substantive objection, adopted at full strength:** this is the
source's own Laplace representation, one integration by parts, its elementary
positive kernel derivative, and two immediate Gamma-integral bounds. The
source already uses this kernel differentiation in Theorem5. The full
all-order bridge above is a routine adaptation even if an exact all-order
sentence were unprinted. In addition, n=1 and this question are old r51
screens. No priority absence investigation could make these routes eligible
under the present instruction. Falsifier of this objection: identify an
actual missing nonroutine step or a hypothesis failure in these explicit
bounds for fixed arbitrary integer n>=1. An unprinted application, longer
formalization, or extending the order index alone is not such a step.

The ordinary argument is complete, but **no eligible full candidate exists**.
No PROOF.md is produced. There is no claimed analytic uniform gap concealed
behind numerical checks: the remaining barrier is eligibility/freshness.
If one were to strengthen the target to uniqueness of a minimum, that would
be a different, presently unattributed question and is not pursued here.

## Closest primary and adjacent screens

Nantomah, *An alternative proof of a harmonic mean inequality for Nielsen's
beta function*, Contrib. Math.4(2021),12–13, DOI10.47443/cm.2021.0028:
actual two-page PDF and full proof read. Conjecture1.1 is explicitly stated
as already proved by Matejicka2019. Lemma2.1 gives the n=0 analogue H_0<0;
Lemma2.2 differentiates s beta'/beta^2; its logarithmic derivative argument
settles the reciprocal harmonic mean. This is a separate public prior result,
not another nomination.

Yang, arXiv:2507.10954v1, *An extension of a complete monotonicity theorem
related to Fink's inequality*, actual primary PDF retrieved. The Nielsen
application (4.12)–(4.18), Proposition3 and proof were read: continuous-order
Laplace moments, alternating-Hurwitz endpoint asymptotics, and a majorized
moment-product comparison. This is close classical/source machinery, not a
proof of a new substantive target here. The old cached text was also read;
fresh PDF source and extracted text are retained separately.

Mehrez–Sitnik arXiv:1805.01462v1 was a preliminary search lead. Actual Theorem3
and both proofs were read: for odd n, a Volterra derivative Turan determinant
is a positive double integral or Cauchy–Schwarz. Its odd-order hypothesis is
essential to the displayed nonnegative weight. No explicit even-order open
question was found in this screen. Inventing that question, or calling the
already printed odd-order theorem a discovery, would violate attribution.
This lead was stopped, not converted to a failed source conjecture.

Old cached Zetalaw APPLICATIONS and actual THEORY proof were read for the
Nielsen k-beta derivative-ratio lead, APP0010. It concerns derivatives of
x beta_k and a different three-factor ratio. The proof uses positive Laplace
moments and log-convexity, with the source's integration-by-parts atom at0.
APP0089 concerns a finite generalized-p-beta normalized derivative and a
public counterexample. Neither badge is used to infer equality with Problems
1–3; both neighboring families remain excluded. Root's r51 Mathieu exclusion
is also preserved, without suggesting its Bernardi result settles a beta ratio.

## Historical and registry scope

`screen-receipt.json` records382685 selected text paths and276677 distinct
SHA256 bodies, streamed under the unchanged guard in41.70s. `pathmap.jsonl.gz`
maps all scanned aliases to hashes; SQLite holds one representative path per
body. The scope is all dates under openai-proof-research, including original
research/rejections/copied reviews/tools/catalogues. It excludes listed
generated content-echo basenames, binaries/compressed bodies, dependency
directories and files above12MB. The precise sizes/paths of cap gaps are saved.
Some generated index/venv text was still scanned; that is noise, not semantic
coverage. Initial broad geometry/analysis matches saturated at120 each and
are expressly **not** a comprehensive history clearance.

A second target-specific stream over all distinct scanned bodies had no
global hit cutoff:616 bodies/2044 matching lines; at most8 excerpts of1000
characters per body. It resolved the exact r51 duplicate, Yang primary,
Zetalaw neighboring proofs and irrelevant Nielsen/Volterra names. The
filtered alias-report mapping and specific body list are saved. This is
lexical retrieval followed by the particular primary/report reads above,
not an assertion that every past report was semantically read.

Required registry receipts were read and reused: Renyi r4 CLEAR_BOUNDED for
0d4df45→d254db,9 first-parent steps/28commits/538paths and the paginated
379-file commit; factorial final review's12-step closure throughc3e8754 and
fresh-coverage.json; historical Renyi r3/factorial prior r2. OpenAI7ef5c0cc
is the inherited unchanged head. These are actual retained receipts, with
their selective-baseline and mainline/transient-sidebranch qualifications.
They are not reinterpreted as semantic clearance for Nielsen. There is no
meaningful survivor requiring a new head/delta round, so no moving-head
requests were made. No worldwide novelty or earliest-publication claim.
User's newer Renyi/factorial disposition supersedes stale tally/context prose.
NEXT was copied as-read separately and is never a scientific freeze.

## Exact checks and handback

`sh run-check.sh` runs the unchanged prescribed guard and `checks.py`.
Its rational Euler-transform intervals enclose the actual alternating
Nielsen derivative series: a_k=(x+k)^(-s) is a positive Hausdorff moment
sequence, so every forward difference is nonnegative and at most a_0.
The omitted transformed tail from j=M is at most a_0/2^M. Positive denominator
intervals then enclose each derivative ratio. At32 terms it certifies
three-point nonmonotonicity witnesses for n=0..12, including the printed
n=1, x=1,2,3 comparison. These are exact finite supporting witnesses, not
the all-order proof, novelty evidence, or source counterexamples to a
conjectured monotonicity direction that the source did not posit.
The helper also verifies all locally retained HTTP response-byte hashes.

The only network failure is the original2023 DOI403; all four PDFs returned
HTTP200. No access bypass. Final verified manifest excludes itself and its
verification receipt to avoid circularity; its digest is bound in that
receipt. No external/shared scientific file was modified.
