# T212M independent manuscript review, round 1

Verdict: **PASS_FULL_MANUSCRIPT_T212M**

REQUIRED: none.

Scope of the verdict. The frozen manuscript `../t212m-manuscript-v1/` correctly
supports its full, unchanged statement (Theorem 1.1): for every nonatomic Borel
law G on [0,∞) with iid edge weights on Z², almost surely there is no
bigeodesic, simultaneously over all bi-infinite simple paths, with no direction
or moment assumption, conditional on the stipulated source S (OpenAI, *No
bigeodesics in planar first-passage percolation*, September 24, 2026, revision
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). The verdict does not audit the
truth of S, AH or DH, which are accepted as stipulated or primary inputs under
their stated hypotheses. It makes no acceptance, count (16/20 stands),
publication, staging or commit decision; the parent alone decides those.

## Inputs and authentication

- Externally supplied manifest anchor
  `c71b20126326de8eab4d016b92cca78c9e43440653361899a8335fc2747c7b3f` equals
  the SHA256 of the raw `manifest.json` bytes. The package's own `verify.py`
  (`--root . --anchor c71b2012… --repository-campaign ..`) returned
  `PASS_IDENTITY_ONLY`, 46 payloads, 5 directories, at the start and again at
  the end of this review.
- `public/main.tex` 762b6a39…bc78, `public/manuscript.pdf` f6204f18…e13
  (19 pages, author Myeongjin Kang). The eight section files and
  `references.tex` hashes are recorded in `checks.json`.
- Between the start and end of this review the parent committed the package
  (HEAD moved from 41e40555 to ee8f4781). All package bytes are unchanged; the
  anchor and every hash above still match.
- The 33 source receipts (S at fd4aeeb2) and 10 primary receipts in
  `evidence/` match the private cache bytes. Primary text extractions used:
  AH = arXiv:1609.02447v2 (`ahlberg-hoffman-v2.txt`, f7679476…d4af),
  DH = arXiv:1209.3036v1 (`damron-hanson-v1.txt`, 6f287a47…a72d).

## What the manuscript claims as new, and how each item was checked

The novelty is located only in D, S, P and W (manuscript lines 01-scope 56–63).
Each was re-derived against the manuscript text and the reused primary proofs.

**Cap and equivalence (Section 2, not claimed new).** Parameters (q < 1/1024,
ε < 1/512, two disjoint status bands, g and p_* in lines 02-cap 9–12) give
Lemma 2.1 (L_e ≥ 10, K_e ≥ 2ML_e, tails). Proposition 2.2 (exact preservation
of geodesic bigeodesics) follows from the outermost-contact argument with the
rooted circuit events. Lemma 2.3 is stated with its upward premise explicit
(lines 101–117), which closes the parent's upward-only correction.
Proposition 2.4 (failure of upward finite energy, λ = 1001M+1 with L_e = 10)
is correct and supports the claim that no finite-energy theorem applies as a
black box.

**Metric (Section 3, not claimed new).** Lemma 3.1 (Hoeffding with r = log⁴n,
coercivity constant β = 6√P(t<d) < 1/2, Kingman plus ergodicity, shape
extension) and Lemma 3.2 (linearity of stationary cocycles with an invariant,
possibly random, slope) are correct. Lemma 3.2 replaces the ergodic step of AH
Proposition 9.2. The AH proof of 9.2 already conditions on the invariant
sigma-field, so the replacement is consistent with the reuse.

**D, dominated lifted limiting-graph coupling (Section 4).** The cap is
ergodic, symmetric, has all moments and has unique passage times, so DH
Sections 3–5 apply under A2′ as stated hypotheses (DH 255–335). DH Lemma 6.2
and the triple extraction (DH 1330–1470) are reused at proof level only; I
checked that the extraction uses the ergodic theorem along ς with a random
limit and no finite energy. Lemma 4.1 is correct: the r^{-|F|} density bound
survives pushforward and α-averaging; joint tightness comes from the fixed
pair law; domination passes to Borel sets; caps are continuous at almost every
original configuration; and selected-ray stability uses two uniform
localization events Q_R ⊂ Q_S, strict uncapping, and Fatou, without assuming
almost-sure localization in the Skorokhod realization (lines 56–79).
Remark 4.2 (lines 82–101) is a correct extension. It covers fixed
deterministic finite supports with bounded product density on an upward
event, includes the indicator of a merely measurable upward event in the
lift, and countable choices of site and radius. It explicitly disclaims
random supports and cap finite energy. Both later kernels are in its scope.
Same-status resampling has output density one, and its marked event (old
value low) is upward. The Section 7 tilt only raises edges, and its product
density is bounded by Π_h(1+δ_h Σ_i 1/p_{b,i})^{count} on a finite region.
The wall replaces DH Lemma 6.3 surgery and AH 9.10 Case 1 by raising rungs
above H_m = 4Mm³ with K′ ≥ 8Mm³, with diagonal parity and mass transport.
This replacement is sound, and the DH Lemma 6.4 ceiling is vacuous for an
unbounded cap (line 165). The reference families (lines 167–194) are correct:
"tangent" carries AH's meaning, a unique supporting line (AH 268–269), which
is DH Cor 4.7's differentiability hypothesis. The proofs of AH 5.3–5.6
(AH 824–948) need only the already proved coalescence. AH 4.4/4.6
(AH 649–700) apply because boundary routes for the cap have finite mean.
Hence S's boundary-comparison appendix is genuinely unnecessary.

**S, label and selector transfer (Section 5).** All AH 6–10 uses are declared
proof-level (05-labels lines 2–3). The replacement for AH Lemma 8.6 is
same-status resampling, which is reversible, with δ = g/2 and p_*. Its
constant 3L/(p_*γ) with γ = 1/3 matches the structure of AH (21), where AH's δ
comes from uniform downward finite energy (AH 1555–1944). The S-transfer
through the AH 9.7 cone, with prediction sites carrying density η under an
absolutely continuous non-stationary coupling, and Lemma 5.1's tails
(including empty F0) are correct. Entire extremal-selector preservation via
the AH 9.9 argument plus no-return, the second application of the wall in
place of AH 9.10/9.11, and the all-ray output (AH §10 uses no modification
step; AH 9.13 needs only shift ergodicity, which the mixing cap has) all
follow.

**P, changed-vertex half-plane transfer (Section 6).** The splice X_n^±, the
changed-vertex band (eq:band), the moving barrier along the subsequence n_k
with κ = c/(c+8), and the last-changed-vertex argument are correct.

**Finish (Section 7, S antecedents).** I checked the one-edge budget: the
status-conditional posterior p_{a,i}/r_i ≥ p_* holds and the cap gain is at
least g. I checked the tilt density (eq:density), ∫λ_h = 1 and the L² identity.
The region edge count at height h is at most (12+8/σ)(h+H_0+1), so the
L²-to-TV bound ½√(E L²−1) ≤ p/8 holds uniformly in k and R. The posterior
θ_e = δ_h/(p_{b,i}+δ_h) is correct. The Chebyshev choice max(2⌈m/g⌉,32),
together with a near radius R_0 whose mean is at least 8, gives 3/4. The
spacing ℓ > R_0+1+(R_0+H_0)/σ is fixed before m. It separates a near raised
edge, which lies within lattice distance R_0 of its own site, from the other
site's region. The usable-path bound (8√ε)^j < 1 holds since ε < 1/512.
Hence p/8 ≤ ℓW_I/m for every m, which is a contradiction.

**Use-site table (Section 8).** The table is consistent with the body. The
formal-support counts (14 support and 17 controls) match the scoped formal
review record.

## Closure of earlier gates

- Contribution R1: the gate condition is met by this review together with the
  proof gate. R2: the paid class (eq:paid) includes bounded, unbounded
  finite-mean and some infinite-mean laws, and the new class is exactly the
  infinite case (01-scope 31–41). The scope comparison with DHb Conjecture 1
  is stated as conditional on S. R3: novelty is confined to D/S/P/W, and the
  credits are in place: ADH C.5/(26), Cox–Durrett/Kesten via CT §1.2, AH 9.10
  Case 1 as the wall antecedent, and Boivin via AH §3.1/DH (01-scope 56–72).
  R4: the standing hypotheses are marked at 04-reference line 7,
  05-labels 2–3 and 08-use-sites 3, 16, 32.
- Contribution O1–O5 are closed. O1 is Proposition 2.4. O2 is 01-scope
  45–54. O3 is the Section 3 note "for completeness". O4 is
  04-reference 164–165. O5 is 01-scope 81–82.
- Proof O1–O6 are closed. O1 is 04-reference 168–170. O2 is 04-reference
  190–193. O3 (new labels lie in L_* by absolute continuity) is 05-labels
  101. O4: the selector premise is stated as proved at 05-labels 152, not as
  historical. O5 fixes H_m = 4Mm³ with K′ ≥ 8Mm³ (and K′ ≥ 64Mm³ in the
  diagonal version), 04-reference 121–124, 148. O6 is 04-reference 179–182.
- The parent corrections are present. Lemma 2.3 (02-cap 101–117) is
  upward-only. Remark 4.2 covers the bounded-density finite-support kernels.
  Empty F0 is handled in Lemma 5.1 (05-labels 121). Section references
  resolve: the build logs contain no warnings, and the extracted PDF text
  contains no "??".

## Rendering, credits, reproducibility

All 19 PDF pages were rendered at 70 dpi in a disposable /var/tmp directory
and inspected as contact sheets. I found no clipped formulas, overfull lines
or unresolved references. The title, author, licence statement (prose
CC BY 4.0, code MIT; matches `LICENSE.md`) and
references (S at the pinned revision, AH v2, DH v1, DHb v2, ADH, CT) are
present. The package's build receipts agree with the PDF hash.

## Optional suggestions (non-blocking)

1. 01-scope line 12–13: "Under the stipulated source convention below" could
   read "Assuming the stipulated input S (below)" to make the conditional
   status visible inside the theorem statement itself.
2. 07-finish lines 6–7: say explicitly that the Section 7 tilt is upward on
   its whole support. Then "on their upward events" needs no further
   indicator for that kernel.
3. 07-finish lines 149–151: add one sentence noting that a near raised edge
   lies within lattice distance R_0 of its own site. That is what makes the
   stated ℓ sufficient for disjointness from the other region.
4. 07-finish line 111: the edge count (12+8/σ)(h+H_0+1) could cite its origin
   (two rows plus vertical edges of width 2+2(h+H_0)/σ).
5. 04-reference line 182: the manuscript could name which AH 4.6 hypothesis
   (finite boundary expectation) the cap meets, rather than only "finite mean".

## Reading limits

See `reading-limits.md`. In brief, I did not reread the DH Section 3–5 proofs
(only statements and the A2′ hypotheses), AH Sections 6–7, the body of AH
Section 10, or S's appendix (unused). Correctness there is accepted at
statement level under the cap's verified hypotheses.
