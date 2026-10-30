# Independent SOLO final review: root-arcsinh-complete-r1 combined candidate

Reviewer: Pi GLM-5.3-Flash-EXL3, thinking=high, standard speed. Solo, no children,
no git operations, no edits outside this lane, no counting/acceptance. Work
performed 2026-10-28. Frozen target reviewed in my own copy
(`candidate-frozen/`), not the live parent; the live root lane was only read
and hash-verified. Review unit: the combined lane at
`root-arcsinh-complete-r1` (candidate at original freeze dcef9ead57 with only
PROOF.md's status paragraph updated, plus manuscript and packet).

## Verdict summary

| Gate | Verdict |
|---|---|
| SOURCE (exact target, actual pages read) | PASS |
| MATH (independent exact + numeric re-derivation) | PASS |
| FORMAL (independent extraction + fresh replay) | PASS |
| NOVELTY / PRIOR-ART (bounded, incl. registries) | PASS, bounded |
| SUBSUMPTION (two-point / restricted-range bridge hunt) | PASS; no located bridge |
| SUBSTANTIVE eligibility | PASS (elementary-shortness caveat recorded) |
| MANUSCRIPT (both pages rendered and read) | PASS |
| PACKET (45-payload zip, manifest, determinism) | PASS |
| Historical-status honesty | PASS (one page-number correction below) |

Overall: **PASS** for root to proceed to its own final archive/acceptance
steps. No count, no ledger edit, no acceptance is issued or implied. This is a
bounded-screen novelty result, not a priority or depth certificate.

## 1. Freeze integrity (before/after)

- `final-review-hashes.json`: all 62 entries verified SHA256-identical in the
  root lane BEFORE my work and again AFTER (script in this lane; identical
  result). The frozen root lane was not edited by me.
- `packet/arcsinh-positive-paper-proof.zip` = SHA256
  6d7ace596617c9deb57c5d12a3f34aabfe0578cbc3ac85b7ba9faba712597a56,
  matching archive.json and the task freeze.
- My own copy `candidate-frozen/`: all 45 `candidate/*` hash entries match;
  37/38 files also match `original-review-hashes.json` (the original
  dcef9ead57 freeze); the single difference is `PROOF.md`
  (48fd34f5… vs b58d4978…), exactly the documented status-paragraph update.
  All five formal `.lean` sources are byte-identical to the original freeze.

## 2. Packet — independent extraction and replay

- Independently opened the zip: 46 entries = `arcsinh-positive/` prefix +
  45 payload files + `arcsinh-positive/MANIFEST.json`. All 45 payload hashes
  match the embedded MANIFEST both in-memory and after extraction to
  `own/extracted/`; no extra files; no `.olean`/`.ilean` anywhere; fixed zip
  timestamps 2026-10-28T00:00:00, uniform external attrs (deterministic build).
- The embedded MANIFEST equals the frozen candidate `MANIFEST.json` exactly.
- Fresh replay FROM MY OWN EXTRACTION (`own/replay/`, copies of the extracted
  `formal/*.lean`, `run_lean.py`, `pins.json`, `verify_candidate.py`):
  `python3 verify_candidate.py` → **PASS** in 16.7 s: 5 modules, 19 unique
  declarations, `warningAsError=true`, all module logs empty, axiom reports
  only propext / Classical.choice / Quot.sound. The verifier asserts the
  absolute Lean 4.34.1 binary path AND its SHA256
  (e8baaa71…d5550) and `--version` string, mathlib
  d13f23b723b8a846827a245b89c10fc7d3f11612, and re-verifies all 8 package
  revisions by `git rev-parse`. No prebuilt oleans consumed anywhere.
- My six replay logs are **byte-identical** to the frozen
  `candidate/verification/*.log` and to the root `extracted-replay/` copies
  (checked all six SHA256s).

## 3. Formal inspection (actual sources and reports read)

- `SourceDefs.lean`: `sourceIntegrand p t = (1 + t^p)^(-(1/p))` with real
  `rpow`; `sourceArcsinh p x = ∫ t in (0:ℝ)..x, sourceIntegrand p t` — a
  genuine `intervalIntegral`. `SourceConjecture := ∀ x, 0 < x → x < 1 →
  StrictConcaveOn ℝ (Ioi 1) (fun p ↦ sourceArcsinh p x)` — the printed
  Conjecture 5.1 quantifier-for-quantifier.
- `Checks.log` (read in full, reproduced byte-identically by my replay): all
  19 actual types printed; endpoints
  `source_conjecture : SourceConjecture` closed and
  `sourceArcsinh_strictConcaveOn {x : ℝ} (hx : 0 < x) : StrictConcaveOn ℝ
  (Ioi (Real.log 2 / 2)) (fun p ↦ sourceArcsinh p x)` with only `0 < x`.
- The t=0 endpoint is handled exactly: continuity on `Icc 0 x` via
  `ContinuousOn.rpow_const`; strictness witnessed at `t = x` through
  `intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt`.
  The diagonal effect enters via `hasDerivAt_entropy_exp`
  (chain rule through `exp(a·q)`), not by specializing a fixed-q statement.
  `entropyExpression` is proven equal to the genuine `Real.binEntropy`.
- No `sorry/admit/axiom/unsafe/native_decide` in any module (regex in the
  verifier plus my own read of all 276 lines). No residual premises beyond the
  stated quantifiers.

## 4. Math gate — independently re-derived

My own sympy run (`own/math_check.py`, outputs in `own/math_check.out`):
- ∂_p log f = H(t^p)/p²: exact (0).
- f_pp = f/p⁴·[H² − 2pH − p³(log t)²u/(1+u)²], u=t^p: exact (0).
- H'(u) = −log u/(1+u)² and H(1)=log 2: exact. So 0<H≤log 2 and for
  p>log2/2, H(H−2p)<0 and the variance term ≤0 ⇒ f_pp<0 for every t>0.
- Strict Jensen integration: gap continuous, strictly positive on (0,x]
  (witness t=x>0), integrand exactly 1 at t=0 ⇒ A strictly concave on
  (log2/2,∞) for every x>0. No derivative-under-integral is used anywhere.
- log2/2 < 1 ⇒ the 2019 statement (p>1, 0<x<1) follows. No optimality of the
  interval is claimed (correct: pointwise f_pp<0 can hold below the threshold
  at some t, and the integral gap is positive even at p0=0.4 in my grid —
  the candidate claims nothing there).
- The Turán consequence: strict concavity at the midpoint + AM-GM + positivity
  of A gives A(p)² > A(p−1)A(p+1); sound (paper p.2 wording "follows from
  positivity and the AM-GM" is acceptable since the strictness comes from the
  cited Theorem 1; a one-word tightening is possible, cosmetic only).

## 5. Source gate — actual PDF pages rendered and read

- `survey2019.pdf` (frozen SHA 8ddfe433…303657, hash-checked in my copy):
  - Title page: Li Yin, Li-Guo Huang, Yong-Li Wang and Xiu-Li Lin; JMI 13(3)
    (2019) 833–854. Attribution in the candidate and bibliography correct.
  - Eq (1.14): arcsinh_p(x)=∫_0^x (1+t^p)^(−1/p)dt (odd extension for x<0) —
    **rendered and read on printed p.834 (PDF page 2)**, not p.835.
  - Conjecture 5.1 verbatim on printed p.847 (PDF page 15): "For x∈(0,1)
    fixed, the function p→arcsinh_p(x) is strictly concave on (1,∞). In
    particular … arcsinh_p²(x) > arcsinh_{p−1}(x)arcsinh_{p+1}(x)" for p>2,
    x∈(0,1) — exactly as the candidate scopes it (concavity primary, Turán
    "in particular").
- Filomat 2015 (frozen text): Conjecture 2.4 is the all-p>0 version, line 291
  (strict concavity on (0,∞)); Theorem 2.6 proves only separate-parameter
  concavity, and its own displayed ∂²/∂p² of the integrand has
  d/dp log(1+t^q)=0 with q fixed. Setting q=p is invalid: on the diagonal the
  entropy term H(t^p) appears precisely because d/dp log(1+t^p)≠0. Bridge
  closed; I verified this failure mode myself from the printed formulas.
- **Correction for root (non-blocking):** the task text, the root
  adjudication note, and the preliminary review all state Eq (1.14) is
  "printed 835". The actual printed page carrying (1.14) is **834** (PDF page
  2; page header 834). p.835 (PDF page 3) starts at (1.15). The candidate's
  PROOF.md itself asserts no page for (1.14), so the artifact is unaffected;
  the error lives in the review-chain prose and should be fixed at root.

## 6. Novelty / subsumption — explicit two-point and restricted-range screen

The adjudication's mandated question: does an ESTABLISHED theorem in the
two-point or restricted parameter range subsume the integrand/source? My own
searches (not inherited):

1. Power means: Bege–Bukor–Tóth (AMI 42) and successors prove M_p(a,b) is
   convex in p for p≤0 and log-concave for p≥0 — the opposite direction; the
   candidate's integrand is 2^(−1/p)/M_p(1,t), not covered.
2. Lp-norm interpolation: ‖f‖_p is log-convex in 1/p (classical) — yields only
   log-concavity of the reciprocal, which does not imply concavity; no
   published concavity of p ↦ 1/‖a‖_p found in any dimension or range.
3. "Sums of order p" literature (Love–Morris, RAIRO-RO 1995): treats the sum
   Σ b_i y_i^p, not its 1/p-th root reciprocal, and its concavity results are
   on p<0. Not our object.
4. Rényi-entropy angle: (1+t^p)^(−1/p) = exp(−(1−p)H_p(w)/p) for the two-point
   w; no published concavity statement for this function of p located.
5. Generalized trig/hyperbolic parameter results (Karp–Prilepkina 2015/2024,
   Zhao 2026, Deng–Peng–Zhong 2025, Darkunde–Ghodechor 2026): all forward
   sin/tan/sinh-type or separate-parameter statements; none gives diagonal
   concavity of arcsinh_p. Consistent with the preliminary review's readings.
6. Public formal registries (read-only, unauthenticated, no captcha bypass):
   - suvrit/count-ex-machina @ HEAD (dbf6737): 142 blobs fully listed; 15
     counterexample topics, none on arcsinh, generalized hyperbolic
     functions, or parameter concavity of means/norms.
   - the-omega-institute/trureturing @ dev (2075fa7): repo is ~1.6 GB, no
     clone; full recursive tree is truncated by the API, so I scanned every
     top-level subtree separately: 105,681+ paths scanned, **zero** path
     hits for arcsinh / inverse-hyperbolic / sinh_ patterns; the 1,472
     `Problems/` entries (fully enumerated) contain no arcsinh or
     parameter-concavity-of-generalized-hyperbolic item. Limit: the `Meta/`
     subtree (internal process metadata) stayed truncated at 49,290 entries.
7. MathDB 325512 refetched live 2026-10-28 (200 via curl after fetch tool
   403; public page, no captcha): still open, "Nothing recorded yet", 0/0
   activity; wording is the original all-p>0 conjecture, not the 2019 target.
8. Targeted web searches (Exa until 429, then DuckDuckGo; logs in
   provenance): no published resolution of Conjecture 5.1 located.

**Adjudication correction independently assessed and CONFIRMED.** I re-verified
the generic identity myself: for f(p)=(Σ a_i^p)^(−1/p), exact sympy algebra in
the two-point case and 40-dps numerics in dimension 5 give
f''/f = (H² − 2pH − p³·Var_w(log a))/p⁴, H=−Σ w log w ≤ log n; concavity
numerically fails at p<log(5)/2≈0.805 for my sample vector and holds above
(`own/generic_check.out`). So (a) the dim-5 low-p counterexample indeed
disproves only unrestricted all-p>0 concavity, and (b) a restricted-range
generic theorem of the form "1/‖a‖_p is concave for p>log(n)/2" is TRUE
elementary mathematics — the sole remaining question is whether it is
published. My screen found no such published theorem, in the norm/mean/
entropy literature or either registry. Under the bounded-screen standard the
candidate is not a routine corollary of any located established result; the
no-priority-guarantee caveat stands.

## 7. Substantive eligibility — PASS with recorded caveat

The strongest objection — "short classical two-point binary-entropy calculus;
possibly routine" — is weighed and survives: the object is the surviving 2019
restatement of an open conjecture (live-open MathDB, no citing-work
resolution), the diagonal entropy term is exactly the content separating it
from the published separate-parameter Theorem 2.6, and no established
same-object bridge exists after the explicit narrower-range screen above.
The machinery is elementary and the source authors' school came within one
line of it in 2015; that is an eligibility judgment call, recorded as such.
One family only: entropy lemma, derivative identity, x>1 extension, old
small-p witness, Turán consequence — all uncounted.

## 8. Manuscript and status honesty

- Both pages of `paper.pdf` rendered (`own/pdf/paper-1.png`, `paper-2.png`)
  and read. Content matches `main.tex` and PROOF.md: same theorem, same Eq
  (3) second-derivative identity, same constants, same scope sentences.
  Quantifier statements, attribution (four JMI authors), the Filomat scope
  paragraph, the Lean-scope paragraph (literal interval integral, no
  differentiation under the integral, three standard axioms, pinned Lean
  4.34.1 / mathlib d13f23b7…1612) and the two-item bibliography all match the
  sources and the formal development. No optimality or priority claim.
  Status wording is honest ("independent review pending", "no discovery
  acceptance or worldwide priority is claimed").
- Historical copies: candidate `SUMMARY.md` ("No paper or packet") and
  candidate `provenance.json` (old PROOF.md hash b58d4978…) are pre-manuscript
  historical artifacts; `candidate/README.md` explicitly marks them
  historical and points to itself and the parent receipt for current status.
  The parent `SUMMARY.md` likewise describes a review packet, not acceptance.
  No false acceptance is implied anywhere. The stale "RACSAM 2025 full body
  UNREAD" claim inside the historical candidate PRIOR-ART-SCREEN.md is
  superseded by the preliminary reviewer's actual full-body read (different
  Wilker-type problem), which the root adjudication records; no confusing
  current claim remains in the current-status documents.

## 9. Access limits and failures (candid)

- Exa rate limit (429) hit twice; respected, switched providers, not retried.
  Brave API key absent. grep.app returned a challenge; not bypassed.
- fetch_content → mathdb.com 403; succeeded once via curl with a browser UA
  on the public page (no login, no captcha interaction).
- De Gruyter 2026 body and any paywalled citing bodies unread (subscription).
- trureturing `Meta/` subtree truncated in the API listing (49,290 shown);
  all other subtrees fully scanned. No MathSciNet/zbMATH.
- No browser/account mutation, no uploads, no messages, no git operations.

## 10. Items for root (none blocking)

1. Correct the Eq (1.14) printed page to 834 in root notes/receipts (the
   candidate itself is unaffected).
2. Optional cosmetic: paper p.2 could name Theorem 1 explicitly in the Turán
   sentence; the dependence is currently implied by "Its … consequence".
3. Root owns any correction, final archive rebuild/replay, acceptance and
   counting; additional count remains 0/30 as far as this review is concerned.
