# Parent adoption and corrections of the Bessel final review

Reviewed: independent report/provenance bound to the 56-file freeze26b211919f.
All56 hashes match both the parent and reviewer copies. The independent fresh
87/8 strict receipt is byte-identical to the parent receipt65b88b00…cf2fab5.
The six-gate report is adopted, subject to the corrections below and the final
fresh replay of the actual release extraction. This document does not count it.

## Supplemental interval checker correction

The original reviewer checker forms the second product interval as
[1.9805*J2lo/3, 1.9806*J2hi/3], even though J2hi<0. Those are not sound
outward endpoints. The correct interval is
[1.9806*J2lo/3, 1.9805*J2hi/3]. The parent corrected that one sign-ordering
error in a separately retained portable copy, removed the tautological
check(...,True), and replaced the review-lane absolute JSON path with a
release-relative path. The original review/script remain unchanged.

The corrected exact-Fraction code passes every assertion and gives
K in [-0.002701185125459, -0.002199884665157]. Its exact rational interval
is contained in (in fact agrees with) the parent certificate's interval.
The upper bound is still strictly below -1/500 and below the paper's
coarser -653867/300000000. Thus the review's narrower interval and its
claim of a tighter independently certified interval are NOT adopted.
The actual Lean proof instead uses whole-interval Bernstein identities,
including a correctly signed final scalar estimate. None of its bytes,
endpoints, axioms or manuscript mathematics changed. No new review is
needed for a corrected supplemental check that leaves the reviewed proof intact.

The original checker uses local findroot near2.4/5.5 for the optional
mpmath sanity check; the review's 'bisection' description is inaccurate.
These optional numerical calls do not identify the formal zeros. The formal
IVT/monotonicity/least-root proof and exact enclosures do that work.

## Novelty and substantive decision

The main target is the actual published unambiguous universal conjecture,
not the author's illustrative plots. M=2, alpha=2/5 and x=47/50 satisfy the
intended hypotheses with both real parameters strictly interior. The later
published paper retains the same domain; there is no read narrower live
version that excludes this example. Exact identification of genuine zero
indices and a strict quantitative interior violation supply one substantive
refutation. SmallM and elementary technique do not alone make an intended
literal counterexample into a transcription/domain fix. One common outcome
only: no half-power/helper/coefficient/zero-identification extra credits, no
separate slow-decay existence consequence claimed.

The root independently read the actual Young article and relevant Watson
sections, and the reviewer inspected their primary statements. No explicit
prior refutation or immediate general negative theorem was found. The review
incorrectly suggests only an explicit prior computation could subsume the
result: a general NEGATIVITY theorem could also subsume it. A true theorem
cannot imply false positivity, but that logical observation does not prove
novelty. The parent relies only on the actual bounded body comparisons and
searches. 'First disproof' is not adopted as an absolute priority assertion;
'no earlier resolution found in the documented bounded screen' is the claim.
The optional highM numerical scan is uncredited and not needed for eligibility.

## Other provenance qualifications

The exact_bessel_certificate.py / JSON intentionally retain extra already-known
Faà-di-Bruno/elliptic checks from the broader source-screen session. The field
public_prior_checks describes those unrelated checks, not a Bessel prior-art
clearance. It is frozen historical context, mathematically unused and uncredited.
All original56 files are retained with a release location map.

The reviewer was instructed SOLO, but its activity shows an accidental
'placeholder' Pi/GLM5.3Flash default-speed delegate, followed immediately by
its task_cancel call returning cancel_requested. No descendant work is used.
The header/provenance 'no children' claim is therefore qualified, not adopted
literally. Root's attempt to reissue that cancellation returned task_not_found
because it belongs to the reviewer thread; do not misreport that error as
terminal cancellation. This orchestration mistake does not supply or change
any of the source, checker, independent Lean or manuscript evidence. No second
reviewer was used to reach the verdict, and no further agents are started.

Remaining access/coverage limits are in the full independent report. No
worldwide priority claim or external posting/contact/upload/push is authorized.
