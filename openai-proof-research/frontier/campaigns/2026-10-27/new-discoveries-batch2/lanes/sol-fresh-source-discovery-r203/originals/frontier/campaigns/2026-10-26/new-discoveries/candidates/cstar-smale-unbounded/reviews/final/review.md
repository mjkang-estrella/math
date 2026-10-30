# Independent FINAL five-gate review — parent-smale-unbounded (no finite C*-Smale mean-value constant at degree 3)

Review lane: `pi-smale-unbounded-final-review` (solo, no children, standard/default speed).
Date: 2026-10-27. Reviewed artifact: my own verified copy `candidate/` of the frozen lane
`parent-smale-unbounded` at freeze commit `14493cae8ab4b17d74fbff135054816d576bfcc7`.

**Verdict up front:**

- **GATE 1 — PROVENANCE/FREEZE: PASS** — 27/27 manifest hashes match my copy before and after the review; all 27 contents are byte-identical to the freeze-commit git blobs; my fresh replay receipt is byte-identical to the parent's `parent49-audit.json` (sha `883a2e6c…53c7a`).
- **GATE 2 — FORMAL FRESH REPLAY: PASS** — 49 declarations in 5 modules, replayed in strict isolation under absolute Lean 4.34.1 with pinned mathlib `d13f23b…`; all 5 module logs empty; `warningAsError=true`; no forbidden tokens; no residual hypotheses; axioms exactly `{propext, Classical.choice, Quot.sound}` (47 declarations) or `{propext}` (2 declarations).
- **GATE 3 — INDEPENDENT MATHEMATICS: PASS** — my own fresh exact checker (22 checks, exit 0, `ALL CHECKS PASS`), written independently of the parent's and preliminary reviewer's scripts.
- **GATE 4 — SOURCE / SUBSTANTIVE ELIGIBILITY: ELIGIBLE (PASS), strictly conditional** — my own decision, with the strongest counterargument recorded candidly and the preliminary objection preserved.
- **GATE 5 — NOVELTY: no subsuming result found** (bounded search; explicit limits in §7) — and **MANUSCRIPT: PASS** (both pages rendered and read; matches the formal endpoints).

**No acceptance is made and no count is taken here. The tally remains 27/30. Credit stays 0 pending parent integration.**

---

## 1. Freeze and provenance (Gate 1)

- Copied the frozen lane into my lane as `candidate/`; verified all **27** relative paths of `final-review-hashes.json` by SHA-256 **before** the review (27/27 match) and **again after** (27/27, no review-induced drift).
- Independently confirmed the disk bytes equal the **git blobs of freeze commit `14493cae8ab4…`** for all 27 paths (27/27), and `git diff --stat` from the freeze commit to HEAD over the parent lane is empty: the lane is genuinely frozen.
- The historical `checkpoint-hashes.json` and `full49-review-hashes.json` manifests were **not consumed**; only `final-review-hashes.json` payload was used, per scope.
- `paper.pdf` sha `065c8bb7…750b62` matches the manifest; `paper.pdf == build/main.pdf` (byte compare); `pdfinfo` reports **2 pages**.

## 2. Formal fresh replay (Gate 2)

Command run on **my copy only** (no original oleans consumed; a fresh `build/verified/` was produced inside my lane):

```
python3 verification/verify_candidate.py . \
  --lean-bin /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean \
  --packages /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

Result: **status PASS, 49 declarations, main theorems `critical_iff`, `deleted_coordinate_unit`, `infinite_cubic_constant`, `no_finite_cubic_bound`, axioms `{Classical.choice, Quot.sound, propext}`**. Exit 0. All five module logs (`Selection.log`, `UnboundedDefs.log`, `UnboundedBounds.log`, `UnboundedGap.log`, `UnboundedConclusion.log`) are **0 bytes**. My receipt `build/verified/audit.json` is **byte-identical** to the parent's `verification/parent49-audit.json` (both sha `883a2e6cd1b6bd70004386dc207d00c7aefc84b95df6a00c15ee7cfa46853c7a`), and I personally read the full `Checks.log` axiom inventory: 47 declarations depend on exactly the standard three axioms, 2 on `propext` only — nothing outside `ALLOWED`.

Substantive reading of all five modules (all 49 actual declarations read, not just titles):

- `Selection.lean` — 4 credited generic two-point selection-rigidity lemmas (from the cstar-sendov campaign); explicitly marked non-claiming infrastructure.
- `UnboundedDefs.lean` — literal witness construction in the actual `C(Time, ℂ)` with `sourceCStarStructure : CommCStarAlgebra FunctionAlgebra` synthesized; `cubicPolynomial`/`cubicDeleted` and the **Polynomial-derivative bridge** (`cubicPolynomial_eval`, `cubicPolynomial_deleted`).
- `UnboundedBounds.lean` — zero-divisor-safe **pointwise** factor argument feeding `selection_rigidity_cmap` (the comment correctly notes the function ring has zero divisors, so the global conclusion comes from connectedness, not from cancellation); uniform denominator `‖y − b‖ ≤ 9/4`, positivity, `‖P'(y)‖ = 3ε`.
- `UnboundedGap.lean` — uniform numerator gap `> 2` at the endpoints `t = 0` / `t = 1` for both branches.
- `UnboundedConclusion.lean` — `InfiniteConstantTheorem` is a genuine **∀C ∃** statement (no hypothesis on ε; ε chosen internally as `1/(16(C+1))`, proved `0 < ε ≤ 1/16`); the critical set is **exactly** `{bp, bm}` with `bp ≠ bm` (both existing, via the `↔` in `critical_iff`); `no_finite_cubic_bound` negates the existence of any nonnegative constant over **all** split cubics with noncritical test element — a fortiori over exact monic split cubics, which is the claimed class.

The 2026 parameterized proof is **not** the old fixed-ε=1/16 certificate: the quantifier over `C` is inside the closed endpoints, and every ε-dependent bound is proved for all `0 < ε ≤ 1/16`, not for one value.

## 3. Independent mathematical check (Gate 3, first half)

My own checker `final-math-check.py` (sha `0f5589049c3038efcd214c680d8b0feb6b75d8a816c5fe7517c79c87b5def703`), output `final-math-check-output.txt`, **22/22 PASS, exit 0**. Highlights, all decisions in exact rational/integer arithmetic with the sole irrationality reduced to exact integer comparisons:

1. `P'(w) = 3(w−q)(w+q)`, `P'(y) = −3ε·1` (symbolic, exact); `P(w) = w(w−√3 q)(w+√3 q)` splits, monic.
2. `P(y) − P(q) = 2q³ − 2y³ − 3εy`; at `t=0` the gap is `2 + 3ε + 2(1+ε)^{3/2}`, which is `> 2` **and** `> 4` for every `ε > 0` — the formal endpoint uses the honest weaker `> 2`, and `27/64 < 2` suffices. The sharpened comparison reduces to the exact polynomial identity `4(1+ε)³ − (2−3ε)² = ε(4ε² + 3ε + 24) > 0`.
3. Denominator: `‖y‖ ≤ 1`, `‖q_ε‖ ≤ √(17/16) < 5/4` (exact integer comparison 17 < 25), so `‖y − b‖ ≤ 9/4 > 0`.
4. Final chain: `C·‖P'(y)‖·‖y−b‖ ≤ 27C/(64(C+1)) < 27/64 < 2` for every real `C ≥ 0`, verified symbolically and at `C ∈ {0,1,2,17,10³,10⁶,10⁹}` in exact fractions, with `ε = 1/(16(C+1)) ∈ (0, 1/16]` throughout.
5. Quantifier structure of both endpoints restated and cross-checked against the Lean statements (no hidden split, no residual hypothesis, ε never 0).

I also independently re-verified the two **PRELIMINARY-DECISION corrections**, since I was told not to inherit them blindly:

- **HIGHERMEAN C×C t-family does not give first-order unboundedness.** For `P_t(x,y) = (x³+tx²+x, y³−3y)`, `t > 18`: the small first-coordinate critical `s = (−t+√(t²−3))/3` satisfies `−1/3 < s < 0` (since `√(t²−3) > t−1` for `t > 2`), and `P₁(s) = s(s²+ts+1) = (s−s³)/2` with `|P₁(s)| < 1/2`. At the critical `(s, ±1)` the divided-difference norm is `max((1−s²)/2, 2) = 2` while `‖P'(0)‖ = 3`, so any constant `C ≥ 2/3` survives via that critical point. The correction is correct: the large criticals failing does **not** imply first-order unboundedness, and the erroneous prose in the preliminary report §4 is properly not adopted. (The existing HIGHERMEAN ∞-family concerns the curvature-times-gap `k = 2` term, a different inequality.)
- **Jatar–Ng does not give the exact scalar Smale constant.** I read the actual v2 abstract: it proves `√(8081/6656) ≤ 𝓑₁ < √(7/5)`, hence `ℳ > 1.1018 > 1` — a **bound** that already refutes the constant-1 conjecture — and exact values only for the **higher-order** constants `sup S_k(P) = C_k^{1/(k−1)}`. The scalar bound 4 remains valid. The correction is correct.

## 4. Source review and SUBSTANTIVE-ELIGIBILITY decision (my own, independent)

**Source facts I verified myself** (actual bodies read, not summaries): Krishna Vestnik 54(2) 2026, pp. 38–47 — Theorem 1.1/1.2 scalar Smale with constant 4; the line "Conjecture 1 holds for polynomials of degree 2, 3, 4"; Conjecture 2.1 (C*-algebraic constant-1/(n−1)/n extension), strong form 2.2 + Proposition 2.1, degree-2 Theorem 2.1; HIGHERMEAN 2.3/Theorem 2.2; DUALSMALE 3.1/3.2/Theorem 3.1. Adamczewski/GPT-6 Astra README — Lean-disproof of K=1 at unspecified large degree, consistent with the constant-4 theorem. Jatar–Ng v2 abstract — `ℳ > 1.1018`. So: **the source question (does Conjecture 2.1 hold?) is publicly closed; the fixed-witness refutation was rightly rejected at credit 0 and stays 0; no first-resolution or unresolved-source-question credit is available. No matching MathDB record for a C*-Smale/CSMALE question was located** (my search surfaced only the scalar MathDB page `p/406536`, which lists Jatar–Ng as an additional reference and contains no C*-algebraic unboundedness result; direct mathdb.com fetch returned HTTP 403).

**Decision: ELIGIBLE (PASS) as ONE substantive new theorem**, under the binding conditions below. My independent reasoning, deliberately not copied from the preliminary report:

1. **The proposition is new and not implied by anything public or internal.** The rejected fixed witness proves only "the constant is > 256/27 ≈ 9.48 defeated at one (P,z)"; the new theorem proves "for **every** C there is a (P,z) defeating C". Neither implies the other, and nothing in the scalar literature (all constants finite: 4, 4−O(1/d), exact higher-order `C_k^{1/(k−1)}`) or in the C×C records implies infinitude in a **connected** algebra. I confirmed the two public C×C records (HIGHERMEAN #14982-family, DUALSMALE #14940) in full: both explicitly mark the connected `C(X)` case and the continuous-selection obstruction as **open**, and HIGHERMEAN's prose `t>18` family is (a) for the k=2 term and (b) in a disconnected algebra, and — per my §3 check — cannot even refute first-order constants ≥ 2/3.
2. **The theorem sits at an exact phase transition, which is real mathematical content about the algebra.** Degree 2 over commutative C*-algebras is bounded (source Theorem 2.1/2.2, constant ≤ 1); degree 3 over the single fixed connected algebra `C([0,1],C)` is already **∞**; scalar is finite at every degree. "No bounded Smale-type mean-value theorem exists for split cubics over `C([0,1],C)`" would stand as a clean impossibility theorem even if Krishna's paper had never existed — the mechanism (pointwise two-branch derivative + connectedness selection rigidity + ε-uniform endpoint gap) is new as a *first-order* obstruction, in contrast to the C×C mechanism of picking different coordinates.
3. **The formal certificate is closed and complete** — this is no longer the proposal-only situation the preliminary review faced; the blocking condition it set (a ∀C formal endpoint + manuscript) has been met and is what I replayed in §2.

**The strongest case against, recorded candidly and retained (the parent may still weigh it):** this is the **same family, same algebra, same degree** as the already-built, already-verified rejected fixed witness; the increment is the parameterization `ε = 1/(16(C+1))` plus sup-norm bookkeeping uniform in ε — modest parameterization labor; the theorem's interest is inseparable from a conjecture whose truth value is publicly settled; and no source text or registry asks the connected-case or unbounded-constant question. Moreover the *qualitative* content "no scalar-type constant extends to degree-3 C*-polynomials" was already implicit in the rejected artifact, since the fixed witness already defeats the scalar universal bound 4 (256/27 > 4, exact). A reviewer applying "exclude refinements of already-resolved questions" mechanically would FAIL this, and that would be a defensible outcome. **I do not FAIL it**, because the strengthened *statement* is a genuinely new, self-contained theorem (an infinite-class impossibility with an exact degree-2/degree-3 and scalar/C*-contrast), because the existing records explicitly leave the connected case open rather than containing it, and because the campaign standard counts substantive general theorems rather than labor — but the objection is preserved verbatim in spirit and the parent retains full judgment. **FAIL was an acceptable outcome for me; I did not stretch the standard to reach 30.**

**Binding conditions** (all already honored by the manuscript and PROOF.md):

- At most **ONE** family outcome; it **absorbs** the rejected fixed witness, which stays at credit **0** and is never a second outcome.
- Never a source-conjecture-refutation or first-resolution credit; scalar prior (Smale 4; degree 2,3,4; Adamczewski; Jatar–Ng) and the source's degree-2 C* theorem are credited, not counted.
- The unformalized HIGHERMEAN/DUALSMALE side observations (e.g. the ε-family's k=2 divergence in the connected algebra, `P''(w)=6w`) are **never** separate credits.
- No absolute worldwide priority claim; bounded-search caveats stay attached.
- This review makes **no count and no acceptance**; tally remains 27/30.

## 5. Novelty / subsumption (Gate 5a)

Wider search than the preliminary review (multiple independent query angles: C*/Banach-algebra mean-value inequalities; Smale constant finiteness/infinitude at fixed degree; continuous selections of polynomial functions and critical-point selection on `C(X)`; MathDB/registries). Sources inspected: MathWorld, Wikipedia/HandWiki, arXiv 2206.08154 (v1 abstract), 2610.21472 (v1/v2 abstract + PDF snippet), 2608.27047, 2303.17586, 2510.16875, the dual-inequality JAT paper, the dynamics approach paper, arXiv 2007.03952 (continuous selections of polynomial functions — generic finiteness of critical points, no mean-value constant content), Michael selection theorem material, GitHub Adamczewski README, VibeMathed page, and — read **in full, not by title** — the local read-only trureturing records `Problems/krishna-2022-cstar-higher-order-smale-mean-value.md` and `…/krishna-2022-cstar-dubinin-sugawa-dual-mean-value.md`.

**Nothing located states, implies, or approximates "the optimal uniform divided-difference Smale constant at fixed degree 3 over one fixed C*-algebra is infinite."** Subsumption analysis:

- **HIGHERMEAN record (C×C, k=2 term):** different inequality (needs `‖P^{(k)}(z)‖`), disconnected algebra, and its ∞-family is prose-only and — per my independent §3 check — does not even bound the first-order ratio away from 2/3. Its "Open" list explicitly contains the connected-`C(X)` case and the source's CSMALE. Does not subsume.
- **DUALSMALE record (C×C, degree 3):** a **lower**-bound conjecture refutation; orthogonal direction; its "Continuous selection — open" note documents that the connected selection obstruction was open. Does not subsume either way.
- **Accepted cstar-sendov (record 16):** shares only the credited selection tool; different conjectures/inequalities; no double counting, but the shared tool must keep the identical crediting description in both records.
- **Scalar literature:** all constants finite; cannot imply ∞ in any C*-algebra.
- **MathDB:** no CSMALE/C*-Smale record located (search snippets only; direct page fetch 403 — see §7).

## 6. Manuscript (Gate 5b)

Both pages rendered to PNG at 110 dpi and **visually read by me** (`render/page-1.png`, `render/page-2.png`):

- Theorem 1 matches `infinite_cubic_constant` exactly: ∀C≥0, monic split cubic with `P'(z)` invertible, **exactly two distinct (existing) critical elements**, strict violation `‖P(z)−P(b)‖/‖z−b‖ > C‖P'(z)‖` at **every** critical element; `P'` described as the literal deleted-factor sum, matching the `cubicPolynomial_deleted` bridge.
- Witness, ε-choice (4), the `>2` gap (honest — the formal endpoint claims `> 2`, not the sharper `> 4` my checker actually proves), and the `27/64 < 2` chain all match the Lean content; no claim exceeds the formal endpoint.
- Prior attribution is honest: scalar counterexamples cited (Adamczewski implied via the K=1 disproof context, Jatar–Ng Theorem 1.3 explicitly), "We do not claim its first resolution", scalar constant 4 valid, degree-2 source theorem credited, credit zero, ONE prospective family outcome, no priority claim.
- 2 pages, `paper.pdf == build/main.pdf`, byte-hash `065c8bb7…` frozen. (My PNG render hashes necessarily differ from the parent's `paper-qa.json` render hashes — different rasterizer session; the frozen artifact is the PDF bytes, which match.)

## 7. Strongest objections, limits, and access constraints

1. **Eligibility objection (retained, §4):** marginal refinement of a resolved-question context; modest parameterization increment; no source or registry asks the question. This is the single most likely ground for a parent-level FAIL and it would be defensible.
2. **Bounded novelty search:** Exa rate-limited (HTTP 429) throughout; searches ran on DuckDuckGo. MathDB direct fetch HTTP 403; MathDB evidence is search-snippet-level plus the prior review's hashed negative finding. Subscription and non-indexed literature uninspectable. A single published sentence "the C*-Smale constant is unbounded at fixed degree in a connected algebra" would flip NOVELTY to FAIL.
3. **I did not re-verify Jatar–Ng's or Adamczewski's internals** (abstract/README level only) — not load-bearing, since the candidate does not depend on them; the dependency runs the other way.
4. **The connectedness step is logical, not numeric**; my checker verifies its exact numeric core (q>0, branches distinct, disjoint closed cover) and I read the Lean selection argument in full; it is correct and standard, but it is the one step whose formalization is a real (already paid) topological cost.
5. **No ledger/tally/packet/acceptance performed by this review**; no contact with other lanes; no agent polling; writes confined to this lane.

## 8. Verdict summary

| Gate | Result |
|---|---|
| Provenance / freeze | **PASS** (27/27 before, 27/27 after, 27/27 vs frozen git blobs) |
| Formal fresh replay | **PASS** (49 decls, 5 modules, logs empty, standard-3 axioms, receipt ≡ parent's) |
| Independent mathematics | **PASS** (22/22 exact checks; both PRELIMINARY-DECISION corrections independently confirmed) |
| Source / substantive eligibility | **ELIGIBLE (PASS), conditional** — one family outcome absorbing the rejected fixed witness (credit 0); objection retained |
| Novelty | **No subsumer found** (bounded search, explicit limits) |
| Manuscript | **PASS** (2 pages rendered/read; matches endpoints and honest scope) |

Overall: the candidate clears all five gates on my independent review. Final acceptance, any count, and packet preparation remain the parent's decisions; nothing here changes the 27/30 tally or the credit-0 status.
