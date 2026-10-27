# Independent preliminary review — parent-smale-unbounded (no finite C*-Smale constant at fixed degree 3)

Review lane: `pi-smale-unbounded-preliminary-review` (solo, no children, standard/default speed).
Date: 2026-10-27. Reviewed artifact: `lanes/parent-smale-unbounded/PROOF.md` + checkpoint sources (all six SHA-256 verified against `checkpoint-hashes.json`).

**Verdict up front:**

- **MATH: PASS** — independently re-derived and verified by my own exact checker (`checks/verify_smale_unbounded.py`, exit 0, all rational decisions in exact integer/Fraction arithmetic, no floating-point decisions).
- **SOURCE: constrained but accurately framed** — the source question (does Krishna Conjecture 2.1 hold?) is publicly closed; the candidate does not claim otherwise. **No MathDB record exists for CSMALE, so no unresolved-source-question credit is available. This constraint is not concealed.**
- **NOVELTY: no decisive prior art found** — nothing public or internal states, implies, or approximates "the optimal uniform divided-difference Smale constant at fixed degree 3 over one fixed C\*-algebra is infinite." Bounded search; see §4 and §6.
- **SUBSTANTIVE-ELIGIBILITY: ELIGIBLE (PASS), strictly conditional** — this is a genuinely new and strictly stronger theorem, not a rebadge of the rejected fixed witness; but it is **not acceptable today** (no formal certificate for the ∀C statement, no manuscript/packet), it must be the **ONE family outcome** absorbing the rejected fixed witness (which stays at 0), and the rejection of the fixed-witness source-refutation credit **stands unchanged**. **No count is made in this review; tally remains 27/30.**

---

## 1. Exact claim under review

For every real C ≥ 0 there exist a monic degree-3 polynomial P over the single fixed commutative unital C\*-algebra A = C([0,1],C), with three continuous roots (fully split), and a noncritical z with P′(z) an invertible nonzero constant, such that P′ is fully split with **exactly two** global continuous critical elements {+q, −q} and **every** critical b violates

  ‖P(z) − P(b)‖ / ‖z − b‖ > C·‖P′(z)‖.

Equivalently the optimal uniform-norm divided-difference Smale constant at degree 3 over A is **∞**. Witness: y = 2t−1, ε = 1/(16(C+1)), q = √(y²+ε), P(w) = w³ − 3q²w, z = y.

## 2. Mathematical review — PASS (independent re-derivation)

I re-derived everything myself and encoded the decisive comparisons exactly. Checker output: `checks/verify_run_output.txt`, `ALL CHECKS PASS`.

1. **Identities (exact, sympy):** P′(w) = 3w² − 3q² = 3(w−q)(w+q); P′(y) = −3ε·1 (constant, norm 3ε, inverse −1/(3ε)·1, so z is noncritical and pointwise-invertibly so); P(y) = −2y³ − 3εy; P(+q) = −2q³; P(+q) and P(−q) exact; P = w(w−√3 q)(w+√3 q), monic with leading coefficient 1 (a non-zero-divisor), hence **exact degree 3**, polynomial and derivative both fully split over A.
2. **Zero-divisor safety / exactly two criticals:** P′(b) = 0 in A ⟺ (b−q)(b+q) = 0 ⟺ pointwise b(t)² = q(t)² ⟺ b(t) = ±q(t) (q(t) > 0 since q² − y² = ε > 0, verified exact). The sets {b = q} and {b = −q} are closed (continuity), disjoint (q never 0), and cover [0,1]; connectedness forces one branch globally. The critical set is exactly {+q, −q}: both exist, none missing, no pointwise-mixing or zero-divisor loophole. This is the correct C(X) argument.
3. **Numerator > 4, uniform in ε:** at t = 0 (branch +q) and t = 1 (branch −q) the pointwise difference is ±(2 + 3ε + 2(1+ε)^{3/2}); its modulus exceeds 4 for every ε > 0. My exact certificate: with u = 1+ε > 1, 2u^{3/2} > 2 ⟺ u³ > 1 ⟺ integer cube comparison, plus 3ε > 0; symbolically 4u³ − (5−3u)² = (u−1)(4u²−5u+25) > 0 covers the sharper comparison. So ‖P(y) − P(±q)‖ > 4 for all ε ∈ (0, 1/16].
4. **Denominator ≤ 9/4:** ‖y‖ ≤ 1, ‖q‖ = √(1+ε) ≤ √17/4 < 5/4 (exact: 25/16 − (1+ε) = 9/16 − ε > 0 ⟺ 16·num(ε) < 9·den(ε)); monotonicity of q−y and q+y in y is exact (y/√(y²+ε) < 1 ⟺ ε > 0), so the suprema sit at the endpoints and ‖y ∓ q‖ ≤ 1 + √(1+ε) < 9/4, strictly positive.
5. **Final chain, exact for every real C ≥ 0:** with ε = 1/(16(C+1)), 0 < ε ≤ 1/16 and
   C·‖P′(y)‖·‖y−b‖ ≤ 27C/(64(C+1)) ≤ 27/64 < 4 < ‖P(y)−P(b)‖,
   hence (dividing by ‖y−b‖ > 0) **every** critical element violates the bound with constant C. Verified for C = 0,…,2000, 10⁴, 10⁵, 10⁶, 10⁹ by integer sweep, and in closed form for all real C ≥ 0 (27C < 256(C+1) always). ε = 0 is never used.
6. **Quantifiers:** the statement proven is exactly ∀C ≥ 0 ∃(P, z) ∀b ∈ Crit(P): ratio > C‖P′(z)‖ — the sup over (P, z) of the best critical ratio divided by ‖P′(z)‖ is ∞ at fixed degree 3 over this fixed A. No hidden "fixed witness + separate unboundedness" split: it is ONE ∀C statement.

**New observations recorded here (not claimed by the parent, must not become credits):**

- The **rejected fixed witness alone** (ε = 1/16) already yields ratio/‖P′(z)‖ ≥ (16/9)/(3/16) = **256/27 ≈ 9.48 > 4** (exact, checker item 5). So the fixed witness already defeats every constant below 256/27, including the scalar universal bound 4: the qualitative content "no scalar-type constant extends to degree-3 C\*-polynomials" was already in the rejected artifact. The new theorem's increment is precisely the quantifier strengthening from "≥ 256/27" to "= ∞".
- The **same family also kills HIGHERMEAN (Conjecture 2.3, k = 2) in the connected algebra**: P″(w) = 6w (verified), so the k=2 term is ≥ 3·‖P(y)−P(w)‖/‖P′(y)‖² ≥ 12/(9ε²) → ∞. The parent does not claim this; if the family outcome is ever pursued it must remain ONE outcome covering everything this family proves.

## 3. Source review — accurately framed; the eligibility constraint stated openly

- Primary source in hand and read: Krishna, Vestnik KRAUNC 54(2) (2026) 38–47, DOI 10.26117/2079-6641-2026-54-2-38-47 (SHA-256 verified). Conjecture 2.1 (weak, constants 1 and (n−1)/n), strong form 2.2 with Proposition 2.1, degree-2 Theorem 2.1; HIGHERMEAN 2.3 / Theorem 2.2; dynamics 2.4; DUALSMALE 3.1/3.2 / Theorem 3.1. The paper proves **no** C\*-wide upper bound at any degree ≥ 3, so the new unboundedness theorem contradicts nothing in print.
- **No MathDB record exists for CSMALE** (per the prior review's site searches and registry #14982). Therefore the source question **cannot be called unresolved**, and this candidate cannot be credited as a source-question resolution. PROOF.md states this honestly; this review confirms it as a hard eligibility constraint.
- The prior review `pi-cstar-smale-preliminary-review` (read in full, hash-verified copy) rightly **rejected** the fixed-witness claim for credit because scalar constant-1 Smale is publicly false (Adamczewski/GPT-6 Astra Lean disproof; Jatar–Ng 2610.21472v2: ℳ ≥ √(8081/6656) ≈ 1.1018 > 1, and sup_P S_k(P) = C_k^{1/(k−1)} exactly — all **finite**). **That rejection stands**; no first-refutation claim is made or endorsed here.
- Scalar contrast (the substance of the new theorem): scalar Smale constant is bounded in all degrees (M ≤ 4, improved by Beardon–Minda–Ng, Fujikawa–Sugawa, Conte–Fujikawa–Lakic, Crane; Jatar–Ng now exact), and the source records the scalar conjecture as **holding for degrees 2, 3, 4** (Tischler line). So at scalar degree 3 the optimal constant is ≤ 2/3, while over C([0,1],C) it is ∞. The scalar high-degree counterexamples are bounded-constant (> 1 but < 4) and cannot imply the ∞ result.

## 4. Novelty / subsumption checks — no subsuming result found

Searched (DuckDuckGo web search, 2026-10-27; Exa/Brave unavailable — rate limit / no key): "Smale mean value conjecture C*-algebra counterexample unbounded constant", "Smale mean value theorem Banach algebra polynomial critical point norm inequality", "Smale mean value constant infinite / no finite constant", "Smale fails degree 3 / cubic", "operator algebra / von Neumann extension", "polynomials over rings with zero divisors mean value". MathWorld and Wikipedia entries read. Found: only the scalar record above, Krishna's conjectures, and scalar work (e.g. arXiv 2608.27047, 2303.17586 — scalar). **Nothing on C\* or function-algebra unboundedness; nothing on the connected C(X) case.**

Subsumption analysis, item by item:

- **trureturing HIGHERMEAN record** (`Problems/krishna-2022-cstar-higher-order-smale-mean-value.md`, read in full): fixed Lean witness in **C×C** (disconnected) at degree 3 for the **k = 2** term; prose family t > 18 giving "no finite constant replaces 4" for the k=2 term in C×C. Different inequality (needs ‖P″(z)‖), different algebra (two-point spectrum; the record itself flags "**Open:** whether … connected X … imply this inequality" and "the connected case [is] not decided"). The t-family would also give first-order unboundedness in C×C in prose (ratio ~ 2t²/9 vs ‖P′(0)‖ = 3), but never states it, and disconnectedness is essential to its mechanism. **Does not subsume** the connected-algebra first-order ∞ theorem; if anything it documents that the connected case was explicitly open in this research line.
- **DUALSMALE record** (`Problems/krishna-2022-cstar-dubinin-sugawa-dual-mean-value.md`, #14940, read): a **lower-bound** conjecture, refuted in C×C at degree 3. Orthogonal direction; the ε-family actually *satisfies* the dual bound at its criticals; its "Smaller constants — open" and "Continuous selection — open" notes are unaffected. **No subsumption either way.**
- **Accepted cstar-sendov (record 16)**: shared *tool* only — connectedness forcing a global branch of a two-branch derivative — which is classical and creditless in both. Different conjectures, papers, inequalities, and results; neither implies the other. No double counting arises, but the shared tool must be described identically in both records and must not be re-credited.
- **Scalar literature (Smale, Beardon–Minda–Ng, …, Adamczewski, Jatar–Ng)**: all constants finite; Jatar–Ng even proves exact finite scalar higher-order constants. **Cannot imply ∞ in any C\*-algebra.**

**Conclusion: the proposition "optimal constant = ∞ at fixed degree 3 over C([0,1],C)" is not stated, implied, or approximated by any located public or internal result.** Bounded-search caveat in §6.

## 5. SUBSTANTIVE-ELIGIBILITY — explicit decision

**Decision: ELIGIBLE as a substantive new mathematical result (PASS), under all of the following binding conditions.**

Why it clears the bar the user set ("new math, not rebadging"):

1. **The proposition is different, not re-proven.** The rejected artifact proved ¬(Conjecture 2.1) with one witness. The prior review's rebadge objection applied to proving the *same* proposition differently. Here the proposition is the strictly stronger ∀C statement, which is **not implied** by the witness, by ¬Conjecture 2.1, or by anything public. A quantifier strengthening from "one counterexample" to "no constant survives" is a new theorem, in the same genre as the optimal-constant determinations this campaign already counts (e.g., record 14).
2. **The contrast is mathematically sharp and lives in an active literature.** Scalar: M ≤ 4 all degrees, exact constants now known (Jatar–Ng), conjecture true at degree 3. C\* over one fixed connected algebra: ∞ already at degree 3. "No bounded C\*-analogue of scalar Smale exists even at degree 3" is a clean impossibility theorem about an infinite class of would-be theorems (one per constant C), witnessed by an explicit infinite family.
3. **It answers, negatively, the connected case that the only existing C\* refutation records explicitly leave open.** The C×C mechanism (supremum picking different coordinates) is unavailable in C([0,1]); the new result shows the obstruction survives connectedness via the continuous-selection gap. That is new information no record contains.

Why it is **not acceptable now, and never as more than one outcome**:

4. **Formal gap is blocking.** The ledger counting standard requires complete Lean verification. The existing 46/5-declaration certificate proves **only the fixed ε = 1/16 instance** (confirmed: constants 1/16 hardcoded in `SmaleDefs.lean`/`SmaleBounds.lean`; endpoint theorems, no ∀C). A new formal endpoint for the ∀C statement is mandatory before any acceptance; none exists and none is claimed.
5. **ONE family outcome, absorbing the rejected artifact.** If ever counted, this is the single outcome of the ε-family. The rejected fixed witness keeps credit 0 and is not a second outcome; no per-degree, per-constant, per-algebra, or HIGHERMEAN-side splits (§2 observations) may be carved out. The scalar prior art and the C×C records must be credited and distinguished in any manuscript.
6. **No source-question credit is available or claimed** (§3). Eligibility rests solely on the campaign's "substantive new general theorem / infinite-class" allowance, and the manuscript must say so.

**The strongest case for the opposite decision, recorded candidly (the parent may still weigh it):** the mathematical increment over the already-built, already-verified fixed witness is a parameterization ε = 1/(16(C+1)) plus sup-norm bookkeeping uniform in ε — modest marginal labor on the same construction; the theorem's interest is inseparable from a conjecture whose truth value is publicly settled; and no source text or MathDB record asks for the connected-case or unbounded-constant answer. A reviewer applying "exclude refinements of resolved questions" mechanically would FAIL this. I do not, because the strengthened *statement* is genuinely new mathematics that would stand as a theorem even if Krishna's paper had never existed, and the user's standard explicitly admits substantive infinite-class results — but if the parent's judgment is that the marginal increment is too small for one of the remaining slots, a FAIL on economy grounds would be defensible and is not contradicted by anything in this review.

## 6. Strongest objections and candid limits

1. **Bounded novelty search.** Exa and Brave were unavailable (rate limit / missing key); searches ran on DuckDuckGo only, plus MathWorld/Wikipedia/known-primary reading. I did not inspect MathDB directly this session (prior review's negative MathDB finding is relied upon and hash-verified as a copied source). Subscription and non-indexed literature uninspectable. A single published sentence "the C\*-Smale constant is unbounded" or a connected-C(X) counterexample would flip NOVELTY to FAIL.
2. **I did not re-verify Jatar–Ng's or Adamczewski's internals** — irrelevant here, since the candidate does not depend on them; the dependency runs the other way (they bound the scalar constant, sharpening the contrast).
3. **No formal endpoint, no manuscript, no packet** exist for the ∀C statement; acceptance requires all of them plus a fresh independent final review. This review makes no formal PASS and invests no Lean.
4. **The connectedness step is a logical (non-numeric) argument**; my checker verifies its exact numeric core (q > 0, q² − y² = ε > 0, disjoint closed cover) and asserts the topological step. A formalization will need the connected-interval argument in Lean — a real but standard cost.
5. **The ε-family's HIGHERMEAN side effect (§2) is unclaimed**; leaving it unformalized is fine, but it must never be counted separately.
6. **If the parent does not pursue the formal endpoint, this candidate expires with credit 0** like the fixed witness — eligibility is not a reservation.

## 7. Provenance

- Reviewed: `lanes/parent-smale-unbounded/PROOF.md` (SHA-256 4b0e62cd…8baf) and all five checkpoint sources — every hash independently recomputed and matched `checkpoint-hashes.json` (krishna-vestnik-54-2.pdf 91ce25a2…50df8; .txt b6c275ca…ffa3c; jatar-ng abstract html fc7bd1d3…f9c5e6; adamczewski README 9282e220…f9c5e6; rejected-fixed-witness-review.md 1046fd80…acda3). Full Krishna journal text and the two trureturing records read in full.
- Own exact checker: `checks/verify_smale_unbounded.py` (SHA-256 e57014ae4ebb407eae502b1429227789953f20adda366a66c73ec84381dd9a9e), run log `checks/verify_run_output.txt` (SHA-256 61b7fc50f7188ae786dd9271913dbd9d2e98619041cde67893e8f6f1df586ae2), exit 0, "ALL CHECKS PASS". All decision arithmetic in Python `fractions.Fraction`/integers; irrational comparisons by exact sign-aware reduction to integer comparisons; symbolic identities via sympy 1.14.0.
- Prior-art searches: DuckDuckGo (provider), queries listed in §4, 2026-10-27; MathWorld `SmalesMeanValueConjecture.html` and arXiv 2610.21472v2 abstract fetched and read. Exa rate-limited (429); Brave key absent — recorded as a search-coverage limit.
- Internal records read in full: `lanes/pi-cstar-smale-preliminary-review/REPORT.md` (via parent's verified copy), `lanes/parent-cstar-smale/PROOF.md` + `formal/*.lean` (fixed ε = 1/16 confirmed), `lanes/pi-euler-turan-final-review/fresh/trureturing/Problems/krishna-2022-cstar-higher-order-smale-mean-value.md` and `…/krishna-2022-cstar-dubinin-sugawa-dual-mean-value.md`, `candidates/cstar-sendov/PROOF.md`.

## 8. Verdict summary

- MATH **PASS** (independent exact verification, all strict inequalities, zero-divisor safety, exactly-two-criticals, full splitting, true norms, exact quantifiers).
- SOURCE **accurately framed**; no unresolved-source-question credit available (no MathDB record for CSMALE; question publicly closed) — constraint stated, not concealed.
- NOVELTY **no decisive prior art found** (bounded search; §6 limits).
- SUBSTANTIVE-ELIGIBILITY **ELIGIBLE (PASS), conditional**: new ∀C formal endpoint mandatory; ONE family outcome absorbing the rejected fixed witness; scalar and C×C prior art credited; never a source-refutation credit; the 27/30 tally is unchanged by this review and no count is recommended or made here.
