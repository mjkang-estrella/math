# Batch-2 live prior-art chronology audit — three exact targets

Lane: pi-batch2-live-prior-audit-r1. Reviewer: Pi GLM-5.3-Flash (thinking high), solo, no children.
Date of review and all live fetches: **2026-10-28, 21:15–22:05 UTC** (local PDT 14:15–15:05).
Scope: CURRENT-public-proof / exact-subsumption and chronology for three named targets. No rerunning
of formal proofs, no recount, no acceptance, no candidate/ledger/shared writes. No git writes; only
read-only `git show/log`. Only public HTTP/search; no browser tabs, no tokens, no access-control bypass.
All 403/429/challenge responses respected and recorded; no loops.

Method (following root-gaunt-public-proof-adoption-r2/ADOPTION.md): the old pinned-tree greps are
treated as NOT clearance. I fetched the **current** trureturing head and walked **complete** trees
(checking `truncated` flags), read actual claim/def files, and re-fetched MathDB/OpenAlex/arXiv live
rather than using Oct-27 snapshots. Positive identification would require reading the actual claim and
variable definitions, not a title or PROVED badge. Chronology is compared against this project's own
completion history; later independent public counterparts and our own publications are not prior proofs.

Surfaces covered per target: trureturing registry (complete tree walk at current head, Problems
registry, spot reads of every plausibly named file), MathDB live record states and search, arXiv
metadata API (versions, author followups, phrase searches), OpenAlex citation graphs, zbMATH Open,
Semantic Scholar citations, count-ex-machina (complete 183-entry tree), and open-access publisher/author
bodies where lawfully reachable.

---

## Target 1 — Outcome 31: parameter concavity of the generalized inverse hyperbolic sine

**Accepted object** (candidates/arcsinh-positive/acceptance.json sha256 5c71ef71…f2566b; formal
SourceDefs.lean 1c5f71b4…681834, SourceTheorem.lean 28bae292…4702db): `ArcsinhPositive.SourceConjecture`
— for every `0 < x < 1`, `StrictConcaveOn ℝ (Ioi 1) (fun p ↦ ∫ t in 0..x, (1 + t^p)^(-(1/p)))`
(literal Yin–Huang–Wang–Lin JMI 13(3) 2019 833–854 Conjecture 5.1, p847; integrand Eq 1.14 p834),
proved for the strictly larger closed endpoint `p > log 2 / 2` and all `x > 0`
(`sourceArcsinh_strictConcaveOn`). MathDB 325512 is the older **all-p>0** statement — an uncounted
different scope; a public small-p refutation does not subsume the accepted positive theorem.

**Live checks (all 2026-10-28):**

- trureturing current head `4e3c47d90fa25b041f5fb8f679e55f32a3089486` (commit 2026-10-28T21:45:01Z,
  tree `fcaedfebc…`): complete D5 tree (12,393 entries, `truncated: false`) and complete Problems
  registry tree (1,524 entries, `truncated: false`) contain **no** arcsinh / asinh / inverse-hyperbolic
  / Yin–Huang–Wang–Lin entry and no file whose name or digest line matches the integral-in-p concavity.
  Plausibly named candidates (Convexity/StrongConcavityAttainment, ExpRatioCM, KarpZhangGamma,
  KarpSitnikLuke, GammaThermal, GammaGammaNBU) were spot-read at the head; all are different objects.
  The only same-2019-survey registry item in Problems remains the Kilbas–Saigo file (already excluded
  earlier for a different candidate).
- MathDB 325512 re-fetched live: `status: "open"`, no solutions, no comments
  (artifacts/mathdb-325512-live.json, sha256 9f32094f…). MathDB site search returns no sibling record
  on this object (search returns a generic default list; noted as a weak surface, recorded, not treated
  as absence evidence by itself).
- OpenAlex citations of the 2019 survey (W2979841489) re-fetched live: still exactly 18 citing works,
  newest 2026-09-08 (artifacts/openalex-cites-jmi.json). The two that needed actual-body work:
  - **Darkunde–Ghodechor, Dolomites Research Notes on Approximation 19 (2026) 22–30**, DOI
    10.25430/pupj-drna-2026-1-3 (published 2026-01-16, open access). I downloaded and read the actual
    PDF (sha256 b02d57d2…49a43, artifacts/drna2026.pdf/.txt). It resolves exactly three conjectures:
    ln(cosh_p(t)) strictly increasing (Conj 4.1), and two sinh_p(t)/t bound conjectures (3.12, 3.29),
    all on t-intervals with p∈(1,2] or [2,∞). **No parameter concavity of arcsinh_p. Scope-different.**
    (This paper is dated before our acceptance, so even a match would have been prior art — none found.)
  - **Zhao, Mathematica Slovaca, DOI 10.1515/ms-2026-0304 (published 2026-09-08)** — the body that the
    earlier screen left UNREAD. Publisher serves a dynamic challenge/202; I could not lawfully read the
    body and did not loop. However the published abstract (retrieved via search index and the journal's
    own listing) states the paper studies "(p,q)-extension of a problem of Yin et al. … recently solved
    by Deng, Peng and Zhong" and proves "a new inequality for (p,q)-generalized **sine and tangent**
    functions". Two independent abstracts (Springer-indexed and journal) agree it is sine/tangent, not
    the inverse-hyperbolic-sine diagonal integral. Recorded as **scope-different by abstract with body
    access gap** — see unresolved items.
  - Deng–Peng–Zhong RACSAM 2025 (10.1007/s13398-025-01769-2): link.springer.com serves a challenge page
    (3,038-byte interstitial; respected). The prior screen read the publisher abstract; the independent
    Mathematica-Slovaca abstract corroborates that the Deng–Peng–Zhong resolution is of the Yin et al.
    (TJANT 2014) problem, an extension of which (sine/tangent) is the MS paper. Consistent: not our
    2019 Conjecture 5.1.
- arXiv metadata searches (2026-10-28): "generalized inverse trigonometric" — only the two known 2013/2014
  preprints; no 2025–2026 preprint on arcsinh_p parameter concavity. Author followup search (Li-Guo Huang
  + arcsinh): none.
- zbMATH Open live search "arcsinh": 54 records, none on parameter concavity of the inverse-hyperbolic-sine
  integral (artifacts/zb4.json).
- count-ex-machina (github.com/suvrit/count-ex-machina, last push 2026-09-09): complete 183-entry tree;
  only macdonald-schur-convexity and theta-derivative-log-concavity touch convexity vocabulary; nothing
  on-point (artifacts/cem-tree.json).
- Semantic Scholar: 429 on first call (respected; recorded; not retried in a loop).

**Decision T1: no match, bounded.** No current public proof, refutation, or exact subsumer of the accepted
object was located on any surface; chronology is moot because nothing on-point exists at any date found.
The acceptance's own novelty limits (generic reciprocal-ℓp-norm/entropy subsumption risk, root-adjudicated;
no worldwide-priority guarantee) are **unchanged** by this audit.

**Strongest objection / falsifier:** a published or registry theorem proving concavity in p of
∫_0^x (a + t^p)^(-1/p) dt for a general a>0 (e.g., framed as reciprocal power-mean or ℓp-norm concavity)
would subsume the endpoint. The concrete residual access gaps that could hide it: the Mathematica-Slovaca
2026-0304 body (challenge page) and the RACSAM 2025 body (challenge page). Both abstracts indicate
sine/tangent scope; neither abstract mentions the inverse hyperbolic sine diagonal integral.

**Concrete unresolved access gap (T1):** bodies of 10.1515/ms-2026-0304 and 10.1007/s13398-025-01769-2
unread (publisher challenges; both attempts recorded, no retry loops). Bounded risk, low probability by
abstract evidence, but not zero.

---

## Target 2 — Outcome 32: strict convexity of Gamma-ratio level curves

**Accepted object** (candidates/gamma-level-convexity/acceptance.json sha256 363ab43a…5ed2f; formal
GammaDefs.lean 86fa21b2…4520a7, SourceConvexity.lean be59eb44…144e28): `GammaLevel.SourceConvexity` —
for every `c > 1` there is `h` with `∀ x > 0, 0 < h x ∧ Γ(h x) Γ(h x + 2x)/Γ(h x + x)^2 = c` and
`StrictConvexOn ℝ (Ioi 0) h`; `source_remark16a` is the literal published Remark 16(a) instance at c=2
(Garrappa–Gerhold–Popolizio–Simon, JMAA 551 (2025) 129588, Lemma 15 / Remark 16(a), VoR pp12–13).
Known published result is x ≥ 1 (Lemma 15); the accepted theorem is the full x > 0. The same paper's
Kummer-modulus Remark 6 public refutation is a different question and subsumes nothing here. No exact
MathDB record is asserted for Remark 16(a); the separate complete-Bernstein conjectures are not claimed.

**Live checks (2026-10-28):**

- trureturing current head (as above): complete D5 tree and Problems registry contain no Gamma-level-curve
  / Γ(h)Γ(h+2x)/Γ(h+x)^2 convexity entry. The same-paper registry item
  `Problems/garrappa-gerhold-popolizio-simon-2025-kummer-modulus.md` (read at head, sha256 ae189da8…)
  settles Remark 6 only. Gamma-named dirs (GammaGammaNBU = the Gaunt Bessel-tail family; KarpZhangGamma =
  paired gamma-kernel coefficient positivity; GammaThermal = quarter-shifted Gamma channels;
  KarpSitnikLuke = Karp–Sitnik Conjecture 1 refutation; ReciprocalGammaTuran, QGammaTuran) were
  identified and are all different objects; none proves convexity of the level curve of
  Γ(h)Γ(h+2x)/Γ(h+x)^2 on (0,∞).
- arXiv 2410.11852 version list re-fetched live: **v4 is still the latest version** (no v5); no author
  update. Garrappa arXiv feed: nothing since 2024-10; T. Simon arXiv feed: newest is 2606.03661
  (Beta-weighted non-local differential operators) — not this question.
- OpenAlex citations of the JMAA paper (W4409546448, fetched via `filter=cites:`): **exactly 1** citing
  work — "Derivatives of Mittag-Leffler functions: theory, computation and applications"
  (Nonlinear Dynamics, 2025-08-29). Its published abstract (read) concerns derivatives, asymptotics and
  numerical computation of ML functions; no level-curve convexity. Scope-different.
- Semantic Scholar citations of arXiv:2410.11852 (artifacts/ss-cites.json): 4 items — 2610.10574
  (q-fractional integral operators), 2602.07514 (averaged controllability), a fractional telegraph
  backward-problem paper, and the derivatives survey above. All scope-different.
- MathDB: no record asserted for Remark 16(a); live search surfaces nothing on-point (weak-search caveat
  recorded). MathDB 365327 (the paper's other conjecture) is not our target and was not claimed.
- count-ex-machina and trureturing: nothing (as above).

**Decision T2: no match, bounded.** No public proof or subsumer of full-domain (all x>0) convexity of the
Gamma-ratio level curve was located, at any date. Acceptance novelty limits unchanged.

**Strongest objection / falsifier:** an unindexed followup (e.g., a 2025–2026 paper extending Lemma 15
past x ≥ 1, or a v5 of 2410.11852) would subsume. Citation indexes (OpenAlex 1, Semantic Scholar 4) are
not exhaustive; zbMATH Open search for this exact object was not fruitful via keyword (the object is
rarely named in titles). The x∈(0,1) gap is exactly where the source paper says its Hessian method fails,
so a dedicated small-x method paper is the plausible falsifier shape.

**Concrete unresolved access gap (T2):** none material; all located candidate surfaces were readable
(abstracts at minimum) and none is on-point.

---

## Target 3 — Held full Mittag result (lanes/root-mittag-complete-r1 @ ffde452)

**Held object** (formal SourceDefs.lean sha256 04f25c4b…66c5e; PROOF.md d980617d…30cb3; paper.pdf
6994feea…9ad55): `MittagModulus.SourceClaim370772` — for every `0 < a ≤ 1/2`,
`f_a(t) = |E_(2a,1)(-t)|² + t|E_(2a,1+a)(-t)|² = |E_a(i√t)|²` (literal convergent Gamma-denominator
series) is completely monotone on t > 0 (Chorfi–Et-tahri–Maniar–Yamamoto arXiv 2510.03600v1 Conjecture 3,
Eq 5.2 p23 / MathDB 370772). SOURCE publication hold remains. 65 core hashes, 17 modules/155 declarations,
std3 independent replay — not re-run here.

**Project chronology anchor:** commit `ffde45206cbb9f8ff7d11db026b31c6e331372b2` "Freeze complete
Mittag-Leffler source certificate and manuscript for independent review", author/committer date
**2026-10-28 04:08:42 −0700 (= 11:08:42Z)** (read-only git show). Any candidate prior public proof must
predate this to threaten original credit; anything later is a later independent counterpart.

**Live checks (2026-10-28):**

- MathDB 370772 re-fetched live: `status: "open"`, no solutions, no comments
  (artifacts/mathdb-370772-live.json, sha256 646494d8…). Empty metadata is not novelty evidence — but
  no resolution is recorded there now.
- arXiv 2510.03600 version list re-fetched live: **v1 still the only version**; no author update to the
  conjecture source.
- **Same authors' followup, arXiv 2603.16726v1 (2026-03-17), HTML body fetched and read**
  (excerpt artifact): it states "the complete monotonicity of the function |E_{α,1}(−i s^α)| … **seems
  to be difficult; we refer to Conjecture 3 in [15]** … Thus, we **needed to modify the proof without
  using the complete monotonicity**." This is decisive author-side evidence that as of 2026-03-17 the
  conjecture was unresolved by its own authors. (Note their inline object is the modulus with s^α inside;
  the conjecture's own expression is the modulus-squared combination — the authors' wording does not
  change the reference to Conjecture 3.)
- Published journal version CNSNS 157 (2026) 109758, PII S100757042600119X (published 2026-01-16):
  sciencedirect.com returned **403** (respected; single attempt). The published body therefore remains
  UNREAD — this is the standing gap the hold already records; this audit did not clear it and could not.
- **New surface checked this audit: arXiv 2608.08198v3 (2026-08-08) "Complete Monotonicity of the
  Srivastava–Tomovski Function …"** — abstract read (artifacts/abs-2608.html): it determines CM of the
  generalized Mittag–Leffler kernel E^γ,κ_(α,β)(−x) on the **real positive axis** (iff α ≤ κ and κβ ≥ αγ),
  with a Wright-kernel realization. Our object is a modulus-squared combination evaluated via the
  imaginary axis; it is not a Srivastava–Tomovski function and no "t vs √t", "modulus vs modulus-squared"
  bridge exists. **Scope-different**; also dated 2026-08-08, before our freeze — would have been prior
  art had it matched; it does not.
- Probability-angle searches (arXiv metadata + web): no published theorem that the difference of two
  iid M-Wright(a) variables is a Gaussian variance mixture (the Schoenberg-equivalent restatement of the
  conjecture) for 0<a≤1/2. The distinction the hold insists on was preserved throughout: random-sign
  symmetrization ±X has cf Re E_a(iu) = E_(2a)(-u²) — a different, known-CM object family — whereas
  X − X' has cf |E_a(iu)|², our object; Pillai's Mittag-Leffler law (LT 1/(1+s^a)) is not the M-Wright
  mgf. No public complete routine bridge from published results to our literal claim was found.
- trureturing current head: complete-tree walk shows no Mittag-Leffler CM result (only an unrelated
  Dynamics inverse-limit file and an unrelated Adelic complete-monotonicity file, name-checked).
  Problems registry (complete, 1,524 files): no Chorfi/Mittag entry.
- count-ex-machina: nothing (as above). zbMATH Open keyword searches: nothing on-point.
- OpenAlex citations of 2510.03600 were not separately pulled (the paper is 2025-10; its citation graph
  is covered via the authors' own 2603.16726 and the CNSNS published version, both examined).

**Decision T3: no match, bounded; one concrete unresolved access gap.** No current public full-range proof
or published same-object subsumer was located. The authors' own 2026-03 followup affirmatively treats the
complete monotonicity as open. The single concrete gap — the actual published CNSNS 157(2026)109758 body
(403) — is precisely the gap for which the SOURCE publication hold exists, and this audit recommends
**retaining the hold**: an unread published body by the same authors that poses the conjecture cannot be
assumed not to contain a proof of its own conjecture, even though arXiv v1 poses it as open and the
authors' later preprint works around it. No global-priority assurance is claimed.

**Strongest objection / falsifier (T3):** a proof of complete monotonicity (or of the Gaussian-variance-
mixture property of X − X', X iid M-Wright(a), 0<a≤1/2) inside the published CNSNS body or in any
non-indexed followup. A numeric check, a log-convexity-only result, a fixed-a=1/2 result, or a
random-sign-symmetrization theorem would be scope-different, not a subsumer.

---

## Cross-cutting chronology statement

No on-point public item with any timestamp was found for any target; therefore no retro-invalidation or
priority-adjudication question arises. The Gaunt adoption note's blanket "regardless of timing" wording
was **not** applied: had a match been found, its commit/publication date would have been pinned (full
SHA, file hash, author+committer timestamps) and compared with our completion anchors — outcome 31/32
acceptance 2026-10-28 and the Mittag freeze at 2026-10-28T11:08:42Z (commit ffde452). Commit timestamps
alone are not treated as proving first public availability.

## Recommendation (root owns any correction)

- T1 and T2: **no change recommended.** Accepted outcomes 31 and 32 stand as-is; their recorded novelty
  limits are confirmed current as of 2026-10-28 ~22:00 UTC.
- T3: **retain the SOURCE publication hold**; no prior-proof exclusion. The live author-followup evidence
  (2603.16726v1) strengthens, not weakens, the held status. If root ever closes the CNSNS-body gap, that
  decision is theirs alone.
- No counts, no acceptance changes, no formal PASS stamps for external files (no public development was
  recompiled), no ledger writes.

## Recorded access limits (no loops, all single attempts)

- Semantic Scholar API: 429 (one call), not retried.
- ScienceDirect S100757042600119X: 403.
- link.springer.com s13398-025-01769-2: JS challenge page.
- degruyterbrill.com ms-2026-0304: 202/dynamic challenge (body not obtained).
- GitHub contents API Problems/ listing hit the 1,000-entry cap; worked around via git-trees API with
  `truncated` flags verified false — no absence was inferred from truncation anywhere.
