# Initial source and subsumption investigation

28 October 2026. No novelty PASS or substantive eligibility decision is asserted.

## Source

The actual arXiv v2 PDF (SHA-256
2334f3217556918ec1aba041d3dd8846246ffa91f0e510fdaecf6a57a2e4fcef)
was downloaded, text-extracted and printed p7 rendered and visually inspected.
Conjecture 2.4 includes n<1, the inclusive nu threshold, all x>0, and optimality
up to the even-order symmetry. Remark 2.5 explicitly identifies the unproved
derivative comparison and says the existing integer-shift proof does not easily
adapt. The candidate proves precisely that derivative comparison, including
the zero-order boundary where the source's divided display is singular.

The live arXiv history has only v1 (1 June 2018) and v2 (9 October 2018).
Crossref verifies Proc. AMS 147(7) (2019), 2937–2951 and DOI
10.1090/proc/14433. Its actual VoR and AM URLs are recorded in crossref.json;
both return 403 challenge pages, correctly saved as HTML. The AMS viewer also
returns 403. Manchester's public repository record was fetched successfully;
its only linked paper is arXiv, despite OpenAlex labelling the repository
location publishedVersion. This metadata label does NOT establish that the
arXiv bytes are the journal body. Published-body comparison remains open.

MathDB API 339406 was fetched successfully and states the same literal question;
its open/empty status is not used as a novelty inference.

## Concrete closest-primary checks already done

1. Yang–Tian, *Convexity of ratios of the modified Bessel functions of the
   first kind with applications*, Rev. Mat. Complut., DOI
   10.1007/s13163-022-00439-w (PMC9361280): actual full HTML obtained via the
   public page; relevant Remark 12 and its cited reference read. It resolves
   Gaunt's DIFFERENT Open Problem 2.12 on an adjacent-order convex combination.
   It does not state Conjecture 2.4 or the noninteger squared-order inequality.
   Its reference [43] leads to item 2, checked at body level. This rules out
   confusing its phrase 'answers to Gaunt's open problem' with our target.
2. Yang–Tian, *The monotonicity rules for the ratio of two Laplace transforms
   with applications*, arXiv:1803.02513v1 / JMAA470 (2019), 821–845:
   actual full PDF/HTML obtained. Section5 Proposition2 and surrounding
   derivation concern x + x K_nu'(x)/K_nu(x) at FIXED order and its monotonicity
   in the ARGUMENT. The theorem does not supply the all-real three-order
   extrapolation in the candidate. A positive subsumption bridge has not been
   established from it; this is not a claim that all conceivable consequences
   have been ruled out.
3. Mao–Tian, *Monotonicity and complete monotonicity of some functions
   involving the modified Bessel functions of the second kind*, C. R. Math.
   361 (2023), 217–235, DOI10.5802/crmath.399: actual journal PDF obtained.
   Introduction, definitions, Theorem16 and Corollaries17–19 read in body.
   It treats K_nu^2-beta K_(nu-alpha)K_(nu+alpha), its order/argument
   monotonicity and ratios of those Turan defects. These are different
   products; no all-real squared-order convexity/three-order linear bound
   was found in the inspected results. A keyword scan is not an exhaustive
   theorem audit of the entire paper.

The candidate's elementary convexity of lambda -> K_sqrt(lambda)(x) may itself
be classical. Its integral proof uses only positivity of the even cosh series.
An existing published theorem stating this convexity, or a sufficiently general
linear three-order Bessel inequality, would likely make the candidate a routine
corollary. That is the strongest substantive objection and remains unresolved.

## Bounded search observations and remaining work

Exact title/conjecture, order-squared/square-root-order convexity and author
followup searches found no explicit solution. The author's current public
publication list was obtained; many later Bessel-integral works concern the
first kind or different powers. Their titles do not constitute full-body
clearance. A 2026 Yang–Zhang preprint found in public citing text explicitly
solves the DIFFERENT Open Problem2.10 (first-kind endpoint majorants); its
full body remains unread and needs screening if this candidate advances.

OpenAlex currently lists ten citing records, retained in openalex-citers.json.
Only the Mao–Tian record has been body-assessed here; do not claim that all ten
are cleared. Other potentially relevant bodies and the generic-order literature
must be checked independently. An exact-ID/arXiv grep of the existing pinned
trureturing Blueprint/docs trees found no match; broader/current registry
coverage is not claimed. No MathSciNet/zbMATH sweep or global priority claim.

All ordinary-proof diagnostics pass: four exact algebra identities, 32 direct
source-tail checks, 54 three-order checks and three zero-order tangent checks.
They are numerical diagnostics, not the all-parameter proof.

No complete Lean theorem, paper, packet, independent mathematical review,
novelty clearance or discovery acceptance exists. Candidate credit remains zero.
