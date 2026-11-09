# Analysis round 2 handback

**One complete ordinary-proof candidate: MathDB 326635. Zero qualified discoveries,
zero accepted results, zero submissions.** The candidate proves strict decrease
of *all* Brix–Canuto–Dahmen squared Bessel-zero gap quotients, including the
source convention j_(1,0)=0. Its significance/novelty gates require independent
adjudication; no Lean implementation was begun.

Read `326635-proof.md` for the full proof. The mechanism is a uniform Prüfer-phase
integral estimate, not a finite zero scan: for every n≥1,

    |j_(1,n)^2 - (π²(n+1/4)²-3/4)| < 1/(π n).

An explicit integration by parts establishes that bound from the actual Bessel
ODE. The bound implies strict log-concavity of every positive squared-zero gap
except the first comparison, which is discharged by rational enclosures of the
first three squared zeros. The resulting uniform determinant lower bound is
positive for every index. Only classical existence/simplicity and the leading
zero asymptotic are imported; no uniform McMahon remainder is silently assumed.
`python -I check_exact.py` validates the rational enclosures and determinant
algebra. It passes. The script is validation, not the all-index analytic proof.

## Source fidelity and screening

Four fresh literal records, all integer IDs ≡1 mod3 and outside the initial 30,
were immediately reserved in this lane's `reservation.json`: 345409, 326635,
332377, 356599. Full normalized records are in `literal-records.json`. The actual
primary PDFs were downloaded and the target statements/context read. Downloading
a body is not represented as reading every page of it.

* **326635:** arXiv:1311.0028, printed pp17–18, Conjecture 3. For every integer
  k≥1 the ratio (j_(1,k+1)²-j_(1,k)²)/(j_(1,k)²-j_(1,k-1)²) is monotonically
  decreasing, with j_(1,0)=0. The proof establishes strict decrease for the full
  target. It does not establish the stronger source LGL-grid Conjecture 2 or
  any conditional sharp LGL constant. The current MathDB API response is retained.
* **345409:** Gaunt–Merkle arXiv:2002.01884, Conjecture 3.2. For every r>0 and
  independent Γ(r,1) variables X1,X2, the median of αX1+(2−α)X2 is nondecreasing
  for 0<α<1. **Excluded:** the actual body of Gaunt–Ouimet arXiv:2609.20212v1,
  Theorem 2.1, gives strict increase for every r>0, hence subsumes this exact
  target. The arXiv history page states 25 July 2026 despite the 2609 identifier;
  preserve that source chronology as reported rather than repairing it by guess.
  No independent reproof or proof certification is credited.
* **332377:** Chen–Paris arXiv:1602.00436, Conjecture 1.1. The record's two strict
  Wilker inequalities quantify over every 0<x<π/2 and integer n≥3. **Excluded:**
  the same actual body expressly undertakes its proof, and Theorem 3.1 supplies
  the identical coefficients and full ranges. The exact literal formulas are
  preserved in the record and PDF; no stale open label overrides a source proof.
* **356599:** Brevig–Chirre–Ortega-Cerdà–Seip arXiv:2210.13922, Conjecture 9.1.
  For every pair 0<p<q<∞, C_q/q<C_p/p, where C_p is the *smallest* constant
  |f(0)|^p≤C_p∫R|f|^p for every entire f of exponential type at most π in L^p(R).
  **Parked:** the power trick compares integer multiples, while fractional powers
  of extremizers fail to be entire across their real zeros. The source identifies
  this obstruction; obtaining integer multiples or comparison with p=2 is known
  partial scope and gets zero credit. More precisely, if the normalized minimizer
  envelope I_p=inf_(f(0)=1)∫|f|^p were differentiable, C_p=1/I_p would reduce a
  local monotonicity route to I'_p+I_p/p>0. Formal differentiation suggests
  ∫|φ_p|^p log|φ_p|+I_p/p>0. Neither that all-p entropy sign nor the differentiable
  envelope/uniqueness bridges for 0<p<1 are proved here. This is an exact unpaid
  gap, not a proposed proof. The current API response is retained.

The initial metadata routing also exposed records 325585, 351613 and 347896 with
explicit solved/refuted-source warnings, and 332617/325510/320665 with large
source-definition or specialized dependencies. They were not reserved or
technically investigated and are not added to review coverage.

## Prior history, reservations and current public checks

Read ancestor AGENTS, the requested sibling REPORT/results and Korn REVIEW,
status.json, batch ledger and prior-campaign context, and current ledger/reservation
artifacts. `history-working-screen.json` records hashes and IDs of the current
campaign ledger/reservation files, and searches review/rejection/result/coverage
artifacts for these four IDs: no hits. The existing 30 were checked directly.
The initial exclusion index's conservative history policy remains useful context,
but no claim of full semantic coverage of every rejected problem is made.

Read-only all-ref commit-message and object/path history checks completed: 466,827
object/path lines inspected; no target-ID/topic commit-message match. Related
Bessel paths concern the already credited Bessel–Fourier positivity family and
other modified-Bessel questions, not this squared-zero-gap target. This is a
path/message audit, not a completed all-ref content-diff or semantic audit.

Source retrieval URLs, UTC dates, status codes and SHA256 hashes are in
`source-receipts.json`, `additional-source-receipts.json` and
`mathdb-live-receipts.json`. No GitHub API request was made: the inherited API
rate-limit 403 was respected without retry or alternate-host evasion.

Current public pages were fetched at approximately 03:16 UTC on 6 November:
trureturing's conjectures page and the normal openai/math repository landing page.
The latter embeds currentOid 4eaee87548250b2682affda7d05d947c05554bae, matching the
cached immutable listing. The current trureturing page had no target-author/ID/
source-ID hit; this does not guarantee semantic absence, release completeness,
or latest development-head equivalence. The previously observed omega dev head
bff0276bdd99004a6c0549292f9c57301085af12 is newer than the reused complete listing
at 5a97247bf6ad10485d8891db5430b9e34def4933. **The newer-head delta remains uncleared.**

Reused both siblings' immutable listings and searched 572 existing textual cached
bodies in place. Hashes and search outcomes are in `registry-reuse-screen.json`.
No strong target match appeared. The path routing found no directly named target
in either registry; broad Bessel paths include unrelated questions. Cache policy:
immutable content remains valid at its pinned head indefinitely; a head observation
≤60 minutes old is supporting context only, and never clears a newer head. No
freshness of body content is inferred from retrieval timestamps alone. Neither
current registry nor worldwide novelty is cleared by these bounded checks.

Bounded public searches included the exact ID, authors, squared-zero gaps,
quotients, log-concavity and monotonicity. No exact public Bessel-gap resolution
was located. This is not proof of absence. The older Lorch–Muldoon higher-monotonicity
literature and classical explicit McMahon error bounds are the strongest remaining
subsumption risks. A lawful survey-volume request was separately bounded; its
receipt records the outcome. No missing body is treated as cleared. Source and
registry receipts remain available for a focused independent review.

## Significance and next gate

Unlike the excluded Korn boundary-jet example, 326635 addresses the full displayed
analytic source conjecture without changing its domain, quantifiers or intended
class. The uniform phase estimate and treatment of the origin convention provide
a concrete complete proof mechanism. Shortness is not itself disqualifying, but
it is also not evidence of nonroutine significance: the argument uses elementary
classical phase tools and may be a routine consequence of a published sharp
zero bound. This objection is explicitly OPEN; no discovery credit is awarded.

Recommended next gate: an independent adversarial ordinary-proof and substantive
significance review of `326635-proof.md`, coupled to a focused old Bessel-bound
subsumption audit and the unresolved current-registry delta. Do not start Lean
or package this for submission before those gates pass. Mathematical endpoint:
strict decrease for genuine J_1 zeros; an abstract lemma about supplied numbers
satisfying the estimate is insufficient. The main formal burden is the actual
Bessel/zero/asymptotic/phase/improper-integral interfaces; the arithmetic is small.
The ordinary proof is complete relative to named classical inputs; their Lean
availability has not been audited.

329722 was not revived; 381600, 369163, accepted/in-review campaign targets and
319645 were not pursued. No variable-knot factorization was found or claimed.
No exhaustion is established. All writes stayed in analysis-r2; no children,
Lean implementation, commits, shared edits, browser tabs, external messages,
uploads or public posting occurred. Public submission is outside this research
lane and no result yet passes all qualification gates.

## Additional primary-body subsumption check

The lawful 13,004,884-byte survey volume was successfully obtained (20 MB cap).
It is scanned; pdftotext produces only page breaks. I rendered and visually read
PDF pp69–72, printed pp65–68: Lee Lorch, *Report on some higher monotonicity
properties of Sturm–Liouville functions*, Année 1989/90. Theorem A concerns
higher differences of weighted nodal-interval integrals given derivative signs
of a sum of squares of independent solutions. Theorem B assumes complete
monotonicity of f' and the weight, with positive limiting f. Its stated Bessel
application proves complete monotonicity of the UNSQUARED zero spacings for
order squared greater than 1/4. That does not directly establish the present
squared-gap log-concavity: multiplying those spacings by successive-zero sums
requires an additional sign argument. No direct exact-target subsumer was found
on these pages, but the cited original papers and possible transformed-equation
applications remain unreviewed. Thus this narrows, and does not close, the
subsumption hold. Local rendered page receipts are retained. The web extractor
separately rejected this PDF for content length; local lawful retrieval succeeded.
