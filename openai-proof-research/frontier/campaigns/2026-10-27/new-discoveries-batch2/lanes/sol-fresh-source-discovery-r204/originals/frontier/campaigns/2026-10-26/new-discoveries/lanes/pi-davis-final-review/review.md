# Independent adversarial final review — Davis Conjecture 3.1 candidate

Reviewer: pi review sub-agent (own lane `pi-davis-final-review`), 2026-10-27.
Subject: parent-davis candidate "Davis rational-function Conjecture 3.1" (MathDB 319187),
source lane frozen at commit b75381797c. All 51 pinned files byte-copied into this lane
before review; originals re-hashed unchanged at the end. Credit remains 0; not counted
in the 19/30 accepted tally.

**Verdict: 5/5 gates PASS, no decisive objections.** Exact per-gate limits below.
The candidate is eligible as a prospective resolution of MathDB 319187; the review found
no mathematical, formal, source, novelty, or manuscript defect that would block acceptance.
This review asserts no worldwide priority and adds no stronger unproved converse claims.

---

## Gate 1 SOURCE — PASS

Independently fetched (my lane, `sources/fresh-*`), not from parent caches:

- **arXiv 0910.5725v1** PDF re-fetched from arxiv.org: sha256
  `cdf45f1b…7837806`, byte-identical to the parent's pinned copy. The abs page
  (fetched fresh) shows submission history with **only v1 (2009-10-29)** — no revisions.
- Read from my own copy (text + rendered p12 PNG `my-arxiv-p12-12.png`, visually read):
  definition x_i = x(x−1)…(x−i+1); P_d(x) = Σ_{i=0}^d (x_i)²(x_{d−i})²/(i!(d−i)!) (p5);
  Lemma 1.6 with quotient q_d = (2/(d+1))x² − (2d/(d+1))x + d/2; equation (2.4) in the
  difference presentation P_{d+1}/P_d = q_d + R_d(x)/P_d(x), deg R_d < 2d; and
  **Conjecture 3.1 on p12**: "If d ≥ 5 and x ≥ ½(d+√(d+2)), then −R_d(x)/P_d(x) ≥
  .995(d−2)/(2x+d−2)." Also Table 4 ("evidence for Conjecture 3.1") and the note that
  .995 is, to three decimals, the largest value that "appears to be true".
- **Revised author copy** `fredijmm.pdf` re-fetched from lehigh.edu: sha256
  `bc090db0…1f4a26ec`, byte-identical to parent's. Rendered and visually read its p12
  (`my-fredijmm-p12-12.png`): **Conjecture 3.1 retained verbatim** (numbering of the
  following theorem differs). Header has blank volume/page fields — it is a
  journal-style revised (Received 2009-10-30; Revised 2010-05-14) manuscript.
- Author publication page (fresh fetch, byte-identical to parent's): lists the paper as
  International Journal of Modern Math **5 (2010) 129–148**; it is the only
  crowd-estimation paper in the list.
- **MathDB 319187 live record** re-fetched from `mathdb.com/api/posts/9f2ed184-…`
  (`fresh-mathdb-319187.json`): **semantically identical to the parent's pinned copy**
  (all fields equal). Every array present and empty: `solutions`, `model_attempts`,
  `human_solves`, `comments`, `replies`, `formulations`, `attachments`; `status: "open"`,
  `lean_formalization_count: 0`, `view_count: 5`.

**Limits (disclosed, unchanged):** the final paginated publisher body of IJMM 5 (2010)
129–148 was **not located**; the reviewed bodies are arXiv v1 and the author-hosted
revised manuscript. The two agree verbatim on Conjecture 3.1, and the candidate's Lean
`SourceConjecture319187` matches them character-for-character in content (199/200 = .995,
strict domain, same P_d, same remainder presentation as eq. 2.4).

## Gate 2 MATH — PASS

I re-derived every step myself and then verified with **my own from-scratch code path**
(`math-checks/indep_verify.py`, sparse-dict polynomials over exact `Fraction`; written
independently of the candidate's `certificate.py`/`check_moments.py`; log
`math-checks/indep_verify.log`, final line `RESULT: ALL PASS`). During development I
found and fixed **two bugs in my own checker** (a sign error in the remainder identity
and a spurious `//1000` in the shift constant) — the candidate's statements survived
every exact test:

1. **Literal objects**: P_d, q_d = 2x²/(d+1) − 2dx/(d+1) + d/2, R_d = P_{d+1} − q_d P_d
   match the source (eq. 2.4 difference presentation).
2. **Remainder-ratio identity** −R_d/P_d = (d−4V)/(2(d+1)): verified as an **exact
   polynomial identity** 2(d+1)R_d·Z + (dZ − 4N_u)P_d = 0 (Z = Σw_i, N_u = Σw_i u_i²)
   for d ∈ {5,6,7,8,9,10,12,15,20,25,30,40,43,50,77}. The needed ingredient
   (i+1)w'_{i+1} = (x−i)²w_i and symmetry of w' were re-derived by hand.
3. **Stationarity** λ_i w_i = μ_{i+1} w_{i+1}, λ_i=(d−i)(x−i)², μ_i=i(x−d+i)²: exact for
   d ∈ {5,8,13,21,34,42} × rational x ∈ {11/3, 7/2, 20, 101/2}, all i, including
   zero-weight boundary terms (λ_d = μ_0 = 0 by construction; no division by x−j).
4. **Moment identity** 2M + BV = (d/2)a² with B = 4Da − D + 2a² − 2a (D=d/2, a=x−d/2):
   re-derived by hand from the index-shift identity with h(i)=(i−D)² (expansion
   λ−μ = −2u(2Da+a²+u²), λ+μ = 2(Da²+Du²+2au²) both re-verified) and confirmed exact
   for 13 values of d × 6 rational a. E[i]=d/2 and M ≥ V² confirmed exactly.
5. **Endpoint (strict)**: high-precision (mpmath, 60 dps) direct evaluation of
   −R_d(x)/P_d(x) − (199/200)(d−2)/(2x+d−2) at the exact real threshold
   x=(d+√(d+2))/2 for **all d = 5…120**: strictly positive in every case (worst margin
   ≈ 4.2×10⁻⁴), plus beyond-threshold samples up to x = threshold+1000 for
   d ∈ {5,9,20,43,100,300}. This is corroboration; the proof is the certificate argument.
6. **Tail certificate d ≥ 43**: verified the exact identity
   320000(a+d−1)²(2T²+BT−Da²) = N(d,a) with T=(200da+d²−d+398)/(800(a+d−1)) and
   N = 800K(a+2d−2)(a²−(d+2)/4) + aL(d) + K(201d²+599d−402), K=d²−d+398, for
   d ∈ {43,44,50,77,100,500,5000} × 4 rational a; verified L(43+t) =
   800t⁴+95600t³+3818000t²+51998400t+42755200 exactly (d=43…119); verified B>0 and
   T>0 on the whole domain (d=43…299) and the strict monotonicity/forcing step
   2V²+BV ≤ Da² < 2T²+BT ⟹ V < T. The algebra is sound; strictness at the exact
   endpoint is preserved (N > 0 strictly).
7. **Finite certificates d = 5…42**: my own implementation (different from
   `certificate.py`) reproduced **all 912 shifted integer coefficients** of
   2000^{N_d}G_d(y+r_d) exactly; all strictly positive; **38/38 lists identical to
   `certificates.json`**; the monic division by f_{⌈d/2⌉}² is exact over ℤ in every
   case; and the threshold inequality m_d/2000 ≤ (d+√(d+2))/2 holds exactly
   ((m_d−1000d)² ≤ 10⁶(d+2), m_d ≥ 1000d). Count 912 confirmed
   (even d: d+1 coefficients, odd d: d coefficients; a few extra trailing zeros
   permitted by the Lean checker are harmless).

**Presentation honesty (as asked):** R_d is used through the source's explicit
equation-2.4 difference; polynomial Euclidean division is *not* separately formalized.
This is sound: the only quotient object ever used is the explicit rational q_d, and the
candidate's identity (7) — H_d = 200(d+1)d!·{cross-multiplied difference} — is exactly
what `PolynomialSources.lean`/`FiniteBridge.lean` prove, so no unformalized division is
trusted anywhere. The Python 912-coefficient certificate is correctly labeled
supplementary; Lean computes and checks the full translated coefficient lists internally.

## Gate 3 FORMAL — PASS

- 51/51 pinned files byte-copied to my lane; **originals re-hashed at the end: all 51
  unchanged** (receipt of the re-check in provenance).
- Fresh isolated replay from **my own lane copy**:
  `python3 verification/verify_candidate.py . --lean-bin …/lean-4.34.1-linux/bin/lean
  --packages …/2026-10-14/formal/.lake/packages` → **PASS, 100 declarations / 19
  modules**, wall time 5m49s. Compiler pinned 4.34.1; mathlib `d13f23b7…` and all 8
  dependencies revision-checked and clean by the script.
- **All 19 module logs empty** (0 bytes each, verified by byte count). `Checks.log`
  contains exactly **100** `#print axioms` reports: 50 × [propext, Classical.choice,
  Quot.sound], 42 × [propext], 8 × no axioms (integer-only list lemmas). No other axioms.
- No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` in any source; additionally
  grepped for `opaque`, `attribute`, `macro`, `elab`, `instance`, `syntax`, `extern` —
  none. Only benign `set_option maxRecDepth/maxHeartbeats` in the 7 certificate modules.
- **Endpoints read from my replay's `Checks.log` types**: `Davis.source_strict_bound {d
  x} (hd : 5 ≤ d) (hx : (d+√(d+2))/2 ≤ x) : 199/200*(d−2)/(2*x+d−2) < −remainder d x /
  P d x` and `Davis.source_conjecture_319187 : Davis.SourceConjecture319187` — closed,
  no residual hypotheses. `SourceDefs.lean` P/quotient/remainder are the literal source
  objects; `remainder d x = P (d+1) x − quotient d x * P d x` is the eq.-2.4 difference.
- Finite path: `certificate_implies_positive` + `source_bound_of_certificate` prove the
  semantics bridge (coeffEval/translate/shift with the proved `√n ≤` threshold bound);
  `small_certificates` discharges d=5…42 via 38 kernel-checked `decide +kernel`
  certificates over integer lists computed inside Lean.
- My replay receipt `build/verified/audit.json` has sha256
  **f499f8723b77920a42950167832268ca47700702919d580cd3f10fdbceabc0d4** — byte-identical
  to the parent's `full100-audit.json` and equal in status/declarations/inventory/
  per-module sources. Independently compared, not merely trusted.

**Limits:** replay used the environment's pinned toolchain and package checkout; kernel
certificate checks are expensive as disclosed (~6 min total). `verify_candidate.py`'s
declaration regex recognizes abbrev/def/structure/theorem/lemma; my supplementary greps
rule out `opaque`/`axiom`/metaprogramming escapes in these 19 modules (1131 lines total,
read in relevant part).

## Gate 4 NOVELTY/ELIGIBILITY — PASS (bounded search, limits below)

Independent searches (my queries, my fetches):

- **OpenAlex live**: `cites:W1568649730` → **0 results**; work record `cited_by_count: 0`.
  This is indexed-citer absence, not global absence.
- **Semantic Scholar**: single request → HTTP 429; **no retry loop** (per policy).
- **MathDB site search** (`/api/search?q=crowd+estimation`): the **only** matching post
  is 319187 itself; `solution_count: 0`, `comment_count: 0`, `status: open`.
- **arXiv** (abs page + API): only v1 of 0910.5725; no follow-up papers found under
  "crowd estimation" or the paper title.
- **Author trajectory**: fresh fetch of Davis's publication list — no later paper on
  this problem; his 2018 Boletín paper (fetched and text-searched) invokes
  Conner–Floyd, not Conjecture 3.1.
- **Web search (exa, 5 varied queries)**: no resolution, no posted proof, no typo or
  endpoint-normalization correction, no stronger or special-function subsumption of
  −R_d/P_d ≥ .995(d−2)/(2x+d−2) surfaced. Nothing that would count as a known immediate
  corollary was found.
- **zbMATH public API**: title query returned no record (inconclusive — this journal may
  simply not be indexed there; **not** treated as absence).

**Limits:** no MathSciNet, Scopus, or Google Scholar sweep; no subscription indexes; the
final journal body is unavailable so an in-journal comparison is impossible; S2 blocked.
This is a serious bounded search with negative result — an eligibility finding, **not a
novelty certificate and no priority claim**.

## Gate 5 MANUSCRIPT — PASS

`main.tex` (sha `78380c17…092759c`) and `paper.pdf` (sha `a72ca7c7…d15e4eae7`) match the
pinned hashes. I rendered all **3 pages** (`build/my-paper-{1,2,3}.png`) and personally
inspected every page. Checked:

- **Statement fidelity**: Theorem 1 is the strict strengthening on exactly the source
  domain (integer d ≥ 5, real x ≥ (d+√(d+2))/2, 199/200 = the source's .995); the paper
  explicitly says the constant's optimality is not claimed and Conjecture 3.9 is not
  addressed. Equations (1)–(7) on pp. 1–2 match the source and PROOF.md; I re-verified
  the paper's doubled H_d normalization by hand: the paper's H_d (with 4x², d(d+1),
  coefficients 200/398/400) equals twice PROOF.md's H_d, and its identity (7)
  H_d = 400(d+1)d!{[(2x+d−2)q_d − (199/200)(d−2)]P_d − (2x+d−2)P_{d+1}} is exactly
  right; the Lean checker's "2H_d" is this same polynomial. The paper's coefficient
  positivity claim (positive constant, nonnegative rest) matches the Lean
  `certificateCheck` semantics, which the strictly-positive Python certificates exceed.
- **Lean scope mapping**: p. 3 names the endpoints and the 100-declaration/19-module
  fresh replay with pinned Lean 4.34.1 / mathlib d13f23b7 — all consistent with my own
  replay; every proof-map entry corresponds to a real checked declaration.
- **Attribution**: Davis is credited with the source results (quotient, Lemma 1.8,
  conjecture, tables); the proposed contribution is correctly scoped as the variance
  rewriting + fourth-moment identity + uniform comparison + exact finite certificates;
  "no absolute priority claim is made"; **discovery credit 0** appears and is respected.
- **Numeric coefficients**: 199/200, .995, d−2, 2x+d−2, 43, 38 degrees, 912 coefficients
  (in PROOF.md), T numerator 200da+d²−d+398, N decomposition constants, L(d) shift
  coefficients 800/95600/3818000/51998400/42755200, m_d formula, 2000/1000 scaling —
  every one independently recomputed in Gate 2. Supplementary counts (174 inputs, 45
  zero-weight cases) match `check_moments.py`'s loop structure.
- **Layout/references**: single reference [1] with arXiv v1 and the revised
  journal-style manuscript link; no hidden markers (`\todo`, invisible text) in the tex;
  date October 27, 2026; "Independent review and final packet acceptance are pending"
  correctly describes status at freeze time.

---

## Summary table

| Gate | Verdict | Decisive objections |
|---|---|---|
| 1 SOURCE | **PASS** | none |
| 2 MATH | **PASS** | none |
| 3 FORMAL | **PASS** | none |
| 4 NOVELTY/ELIGIBILITY | **PASS** | none (bounded; see limits) |
| 5 MANUSCRIPT | **PASS** | none |

**Strongest residual caveats (non-blocking, disclosed):** (a) final paginated journal
body unlocated — conjecture verified from arXiv v1 and the revised author manuscript,
which agree verbatim; (b) novelty is a bounded negative search, not a certificate
(S2 429, no subscription indexes); (c) Euclidean polynomial division is not separately
formalized — sound because only the explicit eq.-2.4 difference is ever used, and the
candidate discloses exactly this; (d) the checker's declaration regex plus my
supplementary greps are the guarantee against hidden declarations — no such declarations
exist in the 19 pinned modules.

Parent handles packet extraction, final replay, and any acceptance. Nothing in this lane
was staged, committed, or posted.
