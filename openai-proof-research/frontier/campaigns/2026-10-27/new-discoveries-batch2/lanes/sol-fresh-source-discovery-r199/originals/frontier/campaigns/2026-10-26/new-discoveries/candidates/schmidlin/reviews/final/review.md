# Final adversarial review — Schmidlin Conjecture 37 (MathDB 372858)

Reviewer: pi-schmidlin-final-review (independent sub-agent, worked alone, no children).
Reviewed: full MathDB372858 proof packet frozen at parent commit 4a9cebd3ea, 42 files bound by final-review-hashes.json (all re-verified unchanged at start and end of this review; parent originals also re-verified).
Date: 2026-10-27.

## Verdict

| Gate | Verdict |
|---|---|
| 1 SOURCE | **PASS** |
| 2 MATH | **PASS** |
| 3 FORMAL | **PASS** |
| 4 NOVELTY / ELIGIBILITY | **PASS** (bounded screen; material limits disclosed below) |
| 5 MANUSCRIPT | **PASS** |

Overall: **PASS — recommend acceptance as a candidate resolution of the explicit source conjecture**, with the eligibility/novelty caveats in Gate 4 (no worldwide-priority claim is made or supportable).

## Gate 1 — SOURCE: PASS

Independently fetched (fresh bytes in `sources/`):

- `fresh-source2601.21906.pdf`, SHA256 `1cd3cf2811b7019b54a9d6e6b116551dced876d88aa076d72c386a2cd41ebc9d` — **byte-identical to the parent's copy**, 31 pages, title/author match.
- `fresh-arxiv-abs.html` SHA256 `0c75f6fc...` — **identical to parent's**; submission history shows **v1 only, submitted 29 Jan 2026**. No later revisions exist.
- `fresh-mathdb-372858.json` SHA256 `e40de229...` — **identical to parent's**; post 372858 status **open**, `solutions`, `comments`, `attachments`, `model_attempts`, `human_solves`, `formulations`, `replies` all **empty arrays**; statement matches the packet's reading.
- `fresh-openalex.json` — content-identical to parent's (byte diff is key ordering only): work **W7126272241**, type preprint, publication 2026-01-29, **cited_by_count = 0**; `filter=cites:W7126272241` returns **0 works** (queried live).
- `fresh-author-homepage.html` SHA256 `7fe34386...` — **identical to parent's**; Basel DMI page lists exactly one preprint (this one) and no successor paper.

Personally rendered and read from the **fresh** PDF (images in `sources/fresh-page*.png`):

- **pp 3–4**: Π̂(x,α) := Π(x)^{1−α}Π(x+1)^α = Π(x)(x+1)^α on D̂ = ℝ≥0×[0,1]; S_d(x) := √(2π)e^{−d}(x+d)^{x+d+1/2}e^{−x}; D̂_d adds x+α>−d, which for d=1/2 is **automatic** on the source domain. Matches packet.
- **p 10**: m̂_d(x,α) := log(Π̂(x,α)/S_d(x+α)) — the literal log-error. Matches packet.
- **pp 24–25 (Corollary 32)**: b̄★_SC(y) := 1/(12y+18−12exp(1/48)); the b̄★ bound is proven **"if x ≥ 1 holds additionally"**. The source's x≥1 restriction is real and is correctly credited to Schmidlin, not claimed as new.
- **pp 28–29 (Conjecture 37)**: m̂_{1/2}(x,α) ≤ b̄★_SC(x+α) for all (x,α) ∈ D̂_{1/2}, "In other words, the restriction x ≥ 1 in Corollary 32 is not necessary." Exact target confirmed.

No discrepancy between packet and actual source.

## Gate 2 — MATH: PASS

I rederived the chain from the literal definitions and ran **19 independent checks** (`checks/independent_math_check.py`, own algorithm: sympy exact algebra + mpmath 60-digit; results in `checks/independent_math_check_results.json`). All pass.

1. **Literal identity** (proved symbolically with positive-symbol logs, residual 0, plus numerics at ulp level): m̂(x,α) = R(z) − E(z,a), z=x+1≥1, a=α−1/2, R(z)=logΓ(z)−(z−1/2)log z+z−½log(2π), E(z,a)=(z+a)log(1+a/z)−a. Key step: (z−1/2)log z+(z+a)log(1+a/z) = (z+a)log(z+a)−(a+1/2)log z. Denominator rewrite 12(x+α)+18−12e^{1/48} = 12(z+a)−k, k=12(e^{1/48}−1)=0.252622…∈[1/4,1/2) verified.
2. **Both polynomial identities, exact residual 0** (my own sympy expansion, independent of parent's SymPy path):
   - Rational gap: 1/(12(z+a)−1/4) − U(z) + a²/(2z+a) = (Aa³+Ba²+Ca+F)/(2520z⁵(a+2z)(48a+48z−1)), A=120960z⁵, B,C,F as declared.
   - Step certificate: U(z)−U(z+1)−H(z) = P(z)/(2520z⁵(z+1)⁵(2z+1)⁶) with H(z)=(2z+1)(v+v³/3+v⁵/5+v⁷/7+v⁹/(1−v²))−1, v=(2z+1)^{−1}, P(z)=112z⁸+…+2.
   - **Coefficient tables reproduced digit-for-digit** by my own expansion: B(t+1) = 120960t⁶+723240t⁵+1791720t⁴+2353680t³+1729056t²+673512t+108600; Δ(t+1)=4BF−C² at t+1 = 203212800t¹¹+2149822080t¹⁰+10299502080t⁹+29404384380t⁸+55375719840t⁷+71883106764t⁶+65187512040t⁵+40869159443t⁴+17049349100t³+4345739674t²+553547260t+16630775. All positive.
   - Completion identity 4B(Ba²+Ca+F) = (2Ba+C)²+Δ verified exactly, giving numerator > 0 for z≥1, a≥0.
3. **Signs/directions**: E≥0 (log t ≥ 1−1/t); E ≥ a²/(2z+a) for a≥0 (log(1+t) ≥ 2t/(2+t)) — numerically confirmed; U(z) ≤ 1/(12z) for z≥1 — confirmed; negative-a branch 1/(12z) < 1/(12(z+a)−k) for a<0 — confirmed. k≥1/4 from e^u≥1+u, k<1/2 from e^u ≤ (1−u)^{−1} — confirmed numerically.
4. **Full conjecture sweep**: 693-point grid (x∈[0,10] step 1/8, α∈[0,1] step 1/8) and 3000 random high-precision points (x up to 10⁴, α up to 3 — beyond the source domain): bound − m̂ > 0 everywhere; minimum margins +1.66e−5 (grid), +9.1e−10 (random). Boundary cases x=0, α∈{0,1/2,1}, x=1, and near-corner all have strictly positive margin (smallest +7.7e−4 at x=1, α=1/2).
5. **Asymptotic bridge sanity**: R(n)−2/(n−1) ≤ R(n+r) ≤ R(n)+1/n verified numerically for n=2..29, random r∈[0,1] — no violation.

Boundary cases x=0, α=0, 1/2, 1 all checked explicitly. The claimed stronger statement (all α≥0, strict) is what the mathematics and the formal endpoint both give.

## Gate 3 — FORMAL: PASS

Fresh **isolated strict replay from my own byte-copies** (`verification/replay-stdout.log`, receipt `verification/../copy/build/verified/audit.json`):

- Command exactly as specified, pinned Lean 4.34.1 + mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 + 8 deps — all dependency revisions verified clean by the script.
- Result **PASS: 49 declarations, 12 modules, warningsAsError=true, all 12 module logs 0 bytes** (verified with `find -size +0c`: only Checks.log non-empty, as intended).
- **My receipt SHA256 = d54c9c328ec3296b18ca0356d04ab2a08017569be172e0e5e681630a4ccf80ed — byte-identical to the parent's** (independent reproduction, not trusted).
- I read **all 49 `#check`/`#print axioms` lines from my own replay** (`checks` capture below in review appendix): every declaration depends only on `propext, Classical.choice, Quot.sound`.
- I read **all 12 module sources** (`copy/formal/*.lean`):
  - `SourceDefs`: literal `Real.Gamma`, real `(x+1)^alpha` (rpow, expanded via `Real.log_rpow`), literal ratio logarithm `log (interpolatedPi / burnsideStirling)`; `SourceConjecture372858` = ∀ x α, 0≤x → 0≤α → α≤1 → sourceError ≤ 1/(12(x+α)+18−12exp(1/48)) — exactly the source statement incl. domain.
  - `sourceError_expanded` and the entropy bridge `expandedError_identity` are proved, not assumed.
  - Endpoints: `source_strict_bound` has hypotheses **only** `0 ≤ x`, `0 ≤ α`; `source_conjecture_372858` closes from it. **No residual gamma-bound/asymptotic/equivalence hypotheses anywhere**: `gammaError_le_stirlingUpper` needs only `0 < z`; the classical U bound is fully reproved (StirlingStep → GammaStep → GammaAsymptotic → GammaInterpolation → GammaLimit → GammaUpper), with the real-Gamma limit bridged from Mathlib integer Stirling + logGamma convexity, as claimed.
  - Forbidden-token scan (`sorry|admit|axiom|unsafe|native_decide|private|partial|opaque|extern|implemented_by|elab|macro_rules`): **none**. Declaration inventory regex in the script enforces no hidden/duplicate declarations; 49 counted = 49 reported.

## Gate 4 — NOVELTY + ELIGIBILITY: PASS (bounded screen, limits disclosed)

What I checked at primary-body level:

- **No prior resolution found**: arXiv has v1 only; MathDB 372858 open with all solution arrays empty (fresh fetch); OpenAlex W7126272241 has 0 indexed citers and 0 citing works (live query); DuckDuckGo/Exa searches for the conjecture, its statement fragments, and "2601.21906 proof" return only the source, its mirrors (Semantic Scholar, ResearchGate), and the MathDB page. Semantic Scholar citation endpoint was rate-limited (429) on both attempts — disclosed.
- **Source's own related-work**: the paper states (p 3) the combined Stirling–Gautschi two-variable bounds "have not previously been analysed in detail" to the author's knowledge. Wang (2016) [16] appears **only in the bibliography, never in-text** — the source itself does not rely on it for this range.
- **Closest classical lines do not subsume** (my structural checks):
  - The source's own all-x bound b̄⁺_SC (12y+12−6e^{1/12} ≈ 12y+5.48 in the denominator) is **strictly weaker** than the conjectured b̄★ (≈12y+5.75): verified numerically at y=0.5,…,100 that b̄⁺ > b̄★. So the conjecture is a genuine strengthening of everything proven in the source, not an immediate corollary of its Theorem 33/Lemma 31.
  - Classical one-variable uniform bounds (Robbins 1955 three-term; Batir et al. arXiv:1806.03026 — integers only; Wang-type one-variable) give m̂ ≤ 1/(12z), which beats the target only for α within ≈0.021 of 1/2. The "monotone shift" shortcut m̂ ≤ R(z+a) — which together with R(w) ≤ 1/(12w) would make the conjecture an immediate classical corollary — is **false** (violated by up to 2.2e−3, verified numerically). The two-variable rational-gap certificate is therefore substantively needed, not decorative.
  - The parent's accounting is honest: the classical U bound, entropy inequalities, and the source's x≥1 range are all declared uncredited; one combined outcome only; no optimality/priority claims.
- **Material access limits (disclosed)**: Wang 2016 (J. Number Theory 163) is paywalled — ScienceDirect 403, Unpaywall reports no OA copy; I could not read its full body and so cannot exclude with certainty that some uniform parameterized bound therein implies the missing range x∈[0,1). This is mitigated by the source's own survey claim, the failure of every classical reduction route I tested, and 0 indexed citations. No MathSciNet/zbMATH/Scopus sweep was performed. **No global priority conclusion is drawn or supportable.**

## Gate 5 — MANUSCRIPT: PASS

- `paper.pdf` SHA256 97205e1e1c… and `main.tex` SHA256 b0b2f99158… both match the bound 42; 3 pages; all pages rendered and personally read (`checks/paper-page-{1,2,3}.png`).
- Every formula cross-checked against the Lean sources: Π̂, S_{1/2}, m̂ definitions; Theorem 1 quantifiers (x≥0, α≥0, strict) = `source_strict_bound`; R, E; k∈[1/4,1/2) = `sourceK_lower/upper`; Lemma 2 = `entropy_nonneg/entropy_lower`; A,B,C,F and both shifted coefficient lists = `quadCoeff_shift/discriminant_shift` (also match my independent expansions); completion identity = `quadratic_pos`; negative-a step = `stirlingUpper_le` branch of `scalar_bound`; h(z)=R(z)−R(z+1) = `gammaError_step`; H(z) = `stepUpper` (the paper's v²/3+v⁴/5+v⁶/7+v⁸/(1−v²) is exactly (2z+1)·stepUpper's series −1, since (2z+1)v^{2k+1}=v^{2k}); P(z) = `stepNumerator`; convexity sandwich = `gammaError_unit_bounds`; limit argument = `gammaError_nat_succ`/`gammaError_tendsto`.
- Attribution correct: classical remainder to DLMF §5.11 [2]; Mathlib pinned revision d13f23b7… [3] (matches pins.json); **source's x≥1 range credited to Schmidlin (Cor 32)**; zero-credit / review-pending language present ("This candidate currently has discovery credit zero", "Independent … review … remain required").
- The mathematical claim (α≥0) is the actual formal endpoint; one combined outcome; no separate counting for the source-known range; layout/bibliography clean.

## Strongest objections considered (and why they do not block)

1. **"The negative-α half is pure classical."** True: for α∈[0,1/2) the packet uses only U(z)≤1/(12z) and E≥0 plus algebra. But the source conjecture quantifies over all α∈[0,1], and the α≥1/2 half requires the explicit two-variable positive-discriminant certificate, which is genuinely additive (see Gate 4 structural checks). The packet itself flags the classical parts as uncredited. No inflation.
2. **"Wang 2016 might subsume."** Cannot be fully excluded (body paywalled); mitigations listed in Gate 4. This is the single largest residual eligibility risk; it is disclosed, and the acceptance case rests on the explicit source conjecture being resolved, not on priority.
3. **"Strict bound α≥0 overreaches the source."** It is a superset proved by the same endpoint; the source conjecture (α∈[0,1], weak ≤) is closed exactly (`source_conjecture_372858` from `(source_strict_bound …).le`). No endpoint loophole: no normalization or extra hypotheses.
4. **Numerical sampling is supplementary** — I did not rely on it for any step; all load-bearing identities were verified symbolically with residual 0 and are independently proved in Lean.

## Deliverables in this lane

- `review.md` (this file), `provenance.json`
- `copy/` — the 42 frozen bytes, re-verified at start and end
- `verification/replay-stdout.log`, `verification/replay-stderr.log`, `copy/build/verified/audit.json` + all module logs — my own fresh replay (receipt d54c9c32…, byte-identical to parent's)
- `checks/independent_math_check.py`, `checks/independent_math_check_results.json` — my 19 independent checks (all pass)
- `checks/paper-page-{1,2,3}.png` — my own renders of the manuscript
- `sources/fresh-*` — my fresh source fetches (arXiv abs, MathDB, OpenAlex, author homepage, PDF) and `sources/fresh-page*.png` renders of pp 3,4,10,24,25,28,29; `sources/wang2016.pdf` (paywall HTML, access failed — kept as evidence)
