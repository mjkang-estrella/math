# Independent preliminary review: Xu–Sun–Chen Conjectures 2 and 3

Recommendation to parent: **ordinary mathematics PASS; campaign substantive eligibility FAIL (routine source-method adaptation); zero credit, one family.** This is an independent recommendation, not a parent adjudication. Counts remain nine additional, 39 total, next 40. No Lean or manuscript investment is recommended.

## Separate verdicts

| Gate | Verdict | Basis / limit |
|---|---|---|
| Source fidelity | PASS | Actual published PDF, printed pp. 88–89 and 93–94 visually inspected; full Conjectures 2 and 3, including powers and endpoint, agree. |
| Mathematics | PASS with prose erratum | Independently derived derivative numerator and positive finite certificate; minimum is 584325, constant is 786520. |
| Substantive contribution | FAIL under this campaign's strict standard | Complete differentiation/root-substitution/positive-coefficient bridge below adapts the actual source proof method. The changed sign/parity is explicitly resolved. |
| Prior-literature novelty | HOLD / not cleared | No earlier exact public proof established here. Inherited searches are bounded, including two capped older registry intervals. An explicit source conjecture is evidence of an open claim in that source, not proof of global novelty. |
| Formal feasibility | Plausible, unvalidated | Finite exact algebra and elementary positive-real calculus appear formalizable. No literal Lean endpoint or axiom audit exists in this review; this is not formal PASS. |

The controlling standard is the ancestor and batch AGENTS.md: independently validate deductions, read actual primary statements and proof bodies, and never count a routine corollary, parameter instance, mere formalization or another variant of a credited family. Acceptance additionally requires a literal complete Lean endpoint, independent review, bounded prior-source investigation, paper and strict extracted replay. The ledger's current 9/39/next40 and the prior-campaign exclusions were consulted; nothing in those shared files was edited. An open label or the worker's self-exclusion does not decide any gate.

## Authentication and source scope

Before scientific inspection, all 28 files in the supplied root review-freeze were checked against both byte counts and SHA256. Each was copied byte-for-byte to `frozen/`, with independent equality checks. `frozen-before.json` binds these checks and the freeze itself. Original candidate bytes, including the incorrect prose minimum, remain intact. The supplied root DECISION and replay receipt were not used as independent validation.

The journal is *Applicable Analysis and Discrete Mathematics* 20 (2026), 81–102, Shun-Wei Xu, Jun-Ling Sun and Chao-Ping Chen, “New Shafer-Fink type inequalities for inverse trigonometric, inverse hyperbolic and arc lemniscate functions,” DOI 10.2298/AADM250324010X. A fresh direct journal retrieval at 2026-10-30T01:11:15.874328+00:00 through 01:11:17.953499+00:00 returned HTTP 200 and the identical 433500-byte PDF, SHA256 `5d26c5152d10b857f4725010be5ff9f20bb7ea10424c5e4d80e9bf9c368200dc`. URL and response evidence are in `live-source-receipt.json`; the bytes are `live-published.pdf`. The frozen contents page links the volume/issue source. No browser tabs were opened.

Conjecture 2, p. 89, (27), says for **all real x>0**:

    arctan(x) < 53x / [18 + 35(1 + 109x²/105)^(53/109)].

The printed numerator and additive constant are initially 53/35 and 18/35; multiplying numerator and denominator by 35 gives precisely this expression. The exponent applies to the entire parenthesized base, not to the additive denominator.

Conjecture 3, p. 94, (35), says for **all real 0<x<sqrt(11445)/109**:

    arctanh(x) < 53x / [18 + 35(1 - 109x²/105)^(53/109)].

The radical covers 11445 only; its denominator is outside it. Squaring positive endpoints gives 11445/109²=105/109, hence the requested sqrt(105/109) is exact. This endpoint is below 1. Both intervals are open; equality at zero and the hyperbolic upper endpoint are not requested. The root bases are strictly positive throughout the stated domains. Powers mean positive real powers. Conjecture 1 (arcsine) is separate and receives no claim here.

Remark 4 discusses interval-dependent sharpness of other bounds, without adding an exception to either conjecture. Remark 6's comparisons and suggestion of a larger interval are contextual numerical assertions, not additional obligations proved here. Theorem 5's conclusion accidentally says increasing on (0,infinity), despite its hypothesis and displayed proof domain (0,1); that source typo supplies no extension and is not inherited. No contextual exception changes either full conjecture reviewed.

## Independently reconstructed proof

Use epsilon=1 for arctan and epsilon=-1 for arctanh; write F for the corresponding inverse function. Set

    t=(1+epsilon*109x²/105)^(1/109), D=18+35t^53, U=53x/D.

For arctan, t>1; for arctanh, 0<t<1. The bases are positive, D>0, and F'=1/(1+epsilon*x²), whose denominator is positive. Differentiation of t^109=1+epsilon*109x²/105 gives t'=epsilon*2x/(105t^108). Thus

    U'=53[D-epsilon*(106/3)x²t^(-56)]/D²
      =53[1962t^56+105t^109+3710]/[109t^56D²].

Here epsilon*x²=(105/109)(t^109-1); keeping epsilon through differentiation is essential. Also 1+epsilon*x²=(105t^109+4)/109. Subtraction yields

    U'-F'=P(t)/[109t^56D²(105t^109+4)],
    P(t)=584325t^218+10918530t^165-14554225t^162
         +5698350t^109-3433500t^56+786520.

This derivation was independently implemented in `independent_checks.py` from the general family U=A*x/[B+(1+epsilon*C*x²)^(p/n)]. It uses exact rational dense polynomial arithmetic, not the candidate's sparse multiplication and binomial formula. For z=epsilon*x², the general derivative is

    U'=A[B+(1-2p/n)t^p+(2p/n)t^(p-n)]/(B+t^p)²,
    z=(t^n-1)/C, F'=1/(1+z).

Multiplication by the positive denominator t^(n-p)(B+t^p)²(1+z), followed by normalization 109²*35², reconstructs all 219 coefficients of P from A=53/35, B=18/35, C=109/105, p=53, n=109.

Four exact monic synthetic divisions by t-1 have zero remainders and produce Q of degree 214, with **all 215 integer coefficients strictly positive**. Convolution with [1,-4,6,-4,1] reconstructs P coefficient-for-coefficient. Only after these independent operations did the script compare the resulting list with the frozen certificate; they agree exactly. The full independently generated list is in `independent-results.json`. Its minimum occurs at index 214 and equals 584325; Q(0)=786520; Q(1)=6623016520050>0, so the multiplicity at 1 is exactly four. This is finite exact algebra, with no real-number sampling or numerical extrapolation.

Consequently P=(t-1)^4Q>0 for every t>0 other than 1. Throughout both open x-domains, t is positive and unequal to 1, and the displayed derivative denominator is strictly positive. Therefore G=U-F has G'>0. As x tends to zero from the right, t tends to 1, D tends to 53, U tends to zero and F tends to zero. Monotonicity and this limit give G(y)>=0 for each y>0 in the domain; choosing y=x/2 gives G(x)>G(x/2)>=0. This proves both strict inequalities on their complete source intervals.

The root erratum is confirmed: the frozen PROOF.md minimum sentence is false, while its coefficient list, derivative identity and positivity claim are correct. I found no further defect in the candidate's mathematical argument.

## Complete routine bridge and strongest countercase

Theorem 2, actual p. 88 proof, starts with 7x/[2+5(1+x²)^(7/15)]-arctan(x), differentiates, substitutes v=(1+x²)^(1/15), and factors its numerator as

    v^8(v-1)^3 R(v),
    R=[12,36,72,120,180,252,336,394,426,432,412,366,
       294,196,147,105,70,42,21,7] (low-to-high coefficients).

It then uses positivity and the zero limit. Theorem 5, pp. 93–94, sets h=arctanh(x)-7x/[2+5(1-x²)^(7/15)], substitutes w=(1-x²)^(1/15), and obtains w^8(1-w)^3R(w)>0 on 0<w<1. That proves a **lower** bound, not Conjecture 3's upper bound. My general derivative checker also reconstructs the source's v^8 factor and complete R list exactly.

The explicit bridge is: replace (A,B,C,p,n)=(7/5,2/5,1,7,15) by (53/35,18/35,109/105,53,109), use the same differentiation and positive-root substitution, clear positive denominators, and perform the same division/positive-coefficient verification. The old cubic changes sign across 1, explaining the old bound reversal; the new exact quartic factor is positive on both sides, explaining why both new bounds are upper bounds. Thus the arctanh change is checked, not inferred by analogy. There is no unresolved sign lemma: every one of the 215 quotient coefficients has been obtained and checked exactly. No new analytic inequality, extremum-location argument, parameter classification, or domain decomposition is needed.

The strongest countercase to exclusion is real: the authors explicitly leave these claims conjectural, and new parameters and a larger degree can require genuinely new positivity work. Shortness, conjecture status, and the worker's own verdict cannot decide substantive merit. Here the independent calculation resolves that risk in the same monomial positive-coefficient basis used in the actual proofs: four mechanical divisions already give all-positive coefficients on the full positive axis. The new sign work is a finite routine continuation of the source's displayed method, rather than a missing nonroutine bridge. On this campaign's express prohibition of routine source adaptations and parameter instances, I recommend substantive FAIL. This is not a claim that Theorems 2 or 5 logically state these exact conjectures, nor that an earlier public exact proof exists.

## Bounded prior-source coverage and falsifiers

I inspected the frozen discovery/provenance, registry-screen and HTTP records, and the closest OpenAI arctan-center file. That file concerns probability-measure arctan centers, not these approximation bounds. The inherited registry heads are Omega b62773edfb6a6f7806de09b593b2e3b6834685c7 and OpenAI 4eaee87548250b2682affda7d05d947c05554bae, with recorded retrievals around 2026-10-30T01:00:56Z. These are inherited bounded evidence, not a fresh independent global registry audit. In particular the older aa026->a19a and a19a->490f comparisons remain 300-path capped. Lexical paths and aliases cannot establish semantic absence; the worker's 1652-record history screen is likewise not an exhaustive literature proof. No earlier exact public solution is asserted, no worldwide priority clearance is given, and no broad new opinion search was needed once the complete routine bridge resolved the recommendation. The journal alone was freshly fetched here. Its response was successful; no 403/429/challenge occurred. The inherited online-first timeout remains a recorded limit, not bypassed.

Strongest mathematical falsifiers are a different printed scope/power, a derivative sign or scaling error, a nonpositive quotient coefficient, failed exact multiplication, or an interior vanishing root base. Visual source inspection, the generic derivative calculation, synthetic divisions and domain proof address each. Strongest eligibility falsifier would be demonstrating that the source method needs a new structural sign argument here beyond the completed positive-coefficient calculation. I found none. An earlier exact public proof would independently defeat novelty, but absence of one does not defeat routine-adaptation exclusion. Both conjectures form one unified family; neither the second sign, finite certificate nor a possible later formalization is a separate credit.

## Execution and evidence limits

All Python, retrieval and rendering ran through the unchanged designated helper_guard.py: per-process AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s, nominal40ms, single-thread BLAS/OpenMP and PYTHONDONTWRITEBYTECODE=1. Native bounded reads and apply_patch were used as authorized. No cap was raised. Sampling cannot exclude between-sample RSS spikes. One initial independent source-control assertion failed because my test omitted removal of the source's positive v^8 factor before comparison; that reviewer-helper defect was corrected, retained in `failures.json`, and the exact check rerun successfully. It does not affect the target certificate. No other computational failure occurred in this review.

`exact-check-run.json` records the successful independent check; `render-receipt.json` records the four source-page conversions. Run the checker with the designated guard, for example from the project root using the paths in `provenance.json`; no third-party Python package is required. `frozen-after.json` verifies all 28 originals and copies again at handback, including the freeze. `final-hashes.json` records every other final lane file (excluding itself to avoid circularity). This review did not execute the candidate checker, use a root replay as evidence, run Lean, create a paper, edit git/shared/candidate files, change counts, send external messages, upload, or create children. Parent alone adjudicates.
