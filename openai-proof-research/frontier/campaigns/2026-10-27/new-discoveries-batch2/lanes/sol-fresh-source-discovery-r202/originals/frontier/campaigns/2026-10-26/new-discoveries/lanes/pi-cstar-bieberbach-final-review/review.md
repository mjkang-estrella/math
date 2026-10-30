# Independent adversarial FINAL five-gate review — C*-algebraic Bieberbach general-coefficient refutation

Lane: `pi-cstar-bieberbach-final-review` · 2026-10-27 · SOLO, no children, standard/default speed, own lane only.
Candidate: `lanes/parent-cstar-bieberbach` frozen at git `14493cae8ab4b17d74fbff135054816d576bfcc7`,
25 frozen paths in `final-review-hashes.json` (paths relative to the candidate).
Tally untouched: **27/30**, credit 0. This review grants no acceptance, no count, no packet.

## Verdict

**FIVE-GATE PASS (SOURCE, MATH, FORMAL, bounded NOVELTY/SUBSTANTIVE, MANUSCRIPT) on my own
verified copy of the frozen bytes.** All gates re-examined fresh; the preliminary PASS was
not inherited. This is a review verdict, not an acceptance decision — the parent decides.

- Copy: `copy/` extracted from `git archive 14493cae8a`. All 25 manifest paths hash-verified
  before review; re-verified after (see `provenance.json`, `hash-verify.log`).
- Extras in the candidate (`checkpoint-hashes.json`, `full28-review-hashes.json`) are historical
  manifests, deliberately outside the final manifest, and were **not** used as replay input.

## 1. SOURCE gate — PASS (fresh)

- **Genuine bytes re-verified.** `sources/author-zenodo-6917925.pdf` in my copy:
  SHA-256 `2d537f04…afd59`, md5 `233c4203…f57c` — both match the recorded values.
- **Live Zenodo API recheck (my own, fresh).** `zenodo.org/api/records/6917925`: record
  6917925, creator "K. Mahesh Krishna" (ISI Bangalore), version 1 with `is_last: true`
  (no later version), file `BIEBERBACH.pdf` size 338374, checksum
  `md5:233c4203a5a0bb4b3877ca5b5ee5f57c` — **byte-identical to my copy**, confirmed live today.
- **Statements read verbatim in my copy** (`sources/author-zenodo-6917925.txt`, Conjectures
  1.2–1.7, Theorem 1.8): Conjecture 1.2 — A unital C*-algebra; f(z)=z+Σ_{n≥2} a_n z^n, a_n∈A;
  converges in norm for all z∈D*(0,1); injective on D*(0,1); conclusion a_n a_n* ≤ n²·1,
  a_n* a_n ≤ n²·1 (elementwise, n≥2). D*(0,1) is literally "all elements of A having norm
  less than 1". Conjecture 1.4 adds norm convergence of f'(z)=1+Σ n a_n z^{n−1}. These match
  the paper's (1)–(2) and the formal `SourceClaim`/`SourceStrongClaim` exactly.
- **Access limits retained and re-confirmed.** Direct preprints.org PDF/landing page fetch
  returned 403 again today. Genuine bytes are the author's own Zenodo deposit; the parent's
  earlier web-tool reading of the actual preprints.org PDF text agrees with it. No binary
  identity between the two versions is claimed. Authorea (10.22541/au.165914617.74476371) and
  OSF (10.31219/osf.io/agvry) deposits of the same manuscript exist as additional mirrors.
- **Version status (fresh):** Zenodo `is_last: true` for v1; Europe PMC PPR529287
  `versionNumber 1`. v1 is the latest accessible version.
- **Scope fidelity:** source hypotheses allow arbitrary (non-invertible) coefficients; the
  witness's a₂ vanishes at t=0, hence is non-invertible, so 1.3/1.5 and Theorem 1.8 are
  untouched. 1.6/1.7 need polynomials; Robertson 1.9–1.13 needs odd powers only (a₂≠0
  disqualifies); Lebedev–Milin 1.15 needs f=e^{g}z (witness F has zeros in the ball). Not
  claimed, correctly. No MathDB id is claimed located; no global-nonexistence claim is made.

## 2. MATH gate — PASS (independent re-derivation + fresh checker)

My own checker `math/final_checks.py`, log `math/final-checks-run.log`, mpmath 400 dps +
exact integer/rational checks; **7/7 PASS**. (An earlier run of my checker had two FAILs
caused by my own truncation/parsing bugs — 300-term truncation is insufficient at |Ktu|≈136
and my complex helper was broken; both fixed, results stable at 400 dps. The failure mode is
independent confirmation that no casual numeric shortcut works.)

1. **Construction/convergence.** A=C([0,1],ℂ), a(t)=8t, c_n = a^{n−1}/n! (n≥1), c₁=1.
   Σ‖c_n uⁿ‖ ≤ ‖u‖ Σ (8‖u‖)^k/(k+1)! < ∞ on **all of A**; derivative series bounded by the
   exponential series, convergent everywhere. Both antecedents of 1.2 and 1.4 hold globally,
   far beyond the required ball.
2. **Closed form.** Σ_{n≥1} (8t)^{n−1}u(t)^n/n! = (exp(8t·u(t))−1)/(8t) for t>0, verified on
   60 random (u,t) with max relative error < 10⁻³⁵⁰; F(u)(0)=u(0) since c_n(0)=0 (n≥2) exactly.
3. **Derivative series identity.** Σ_{n≥2} n c_n u^{n−1} = exp(8t·u)−1 form verified to
   < 10⁻³⁶⁰ relative error (30 random points).
4. **Global injectivity is real content.** Pointwise fiber is NOT injective: u and
   u+2πi/(8t) collide at fixed t (verified to <10⁻⁵⁰). The rigidity is essential and correct:
   F(u)=F(v) ⟹ exp(8t(u−v)(t))=1 for all t, h(t)=8t(u−v)(t) continuous with values in the
   discrete set 2πiℤ, h(0)=0, [0,1] connected ⟹ h≡0 (clopen zero set); for t>0, 8t≠0 gives
   u(t)=v(t), and at 0, F(u)(0)=u(0) gives equality. The collision partner is provably
   discontinuous (jump 2π/(8t) diverges as t→0⁺: 3.927→392.7, verified).
5. **Coefficient failure — exact, no floats.** c₂ = 4t; c₂(1)=4 exactly; (c₂c₂*)(1)=16 > 4=n²
   exactly; the elementwise order fails at t=1 (indeed on t>1/2). Literal C*-order, norm 4>2.

## 3. FORMAL gate — PASS (fresh isolated strict replay on my copy)

- **Replay:** `python3 copy/verification/verify_candidate.py copy` with absolute
  Lean 4.34.1 `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  and packages `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/
  2026-10-14/formal/.lake/packages`. Result: **status PASS, 28 declarations, 4 modules**,
  Lean 4.34.1, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` — the script itself
  hard-fails on any compiler/dependency pin mismatch, and it did not. Log in `provenance.json`.
- **All four module logs are 0 bytes** (ExpRigidity, EntireSeries, FunctionMap,
  SourceCounterexample) under `-DwarningAsError=true`; no `sorry/admit/axiom/unsafe/
  native_decide` tokens (script-enforced).
- **All 28 actual declaration types and axiom reports read personally** from **my**
  `copy/build/verified/Checks.log`. Every declaration depends only on
  propext/Classical.choice/Quot.sound. No analytic, convergence, injectivity, exp-period or
  pointwise-inverse premise survives into the endpoints.
- **Endpoints are closed literal negations.** `source_counterexample : ¬SourceClaim` and
  `source_strong_counterexample : ¬SourceStrongClaim` quantify over arbitrary a, F with
  exactly the source's antecedents (tail-HasSum on {‖u‖<1}; + derivative-series Summable;
  + InjOn) and conclude the elementwise order bounds; the discharge instantiates the actual
  `coefficient parameter`/`witnessMap` and proves the antecedents as theorems
  (`source_series_hasSum`, `derivative_series_summable`, `witnessMap_injective`).
- **Instance is genuine.** `sourceCStarStructure : CommCStarAlgebra FunctionAlgebra` typechecks
  by `inferInstance`; I verified in the pinned mathlib that `CommCStarAlgebra` is a real class
  (`Mathlib/Analysis/CStarAlgebra/Classes.lean`) extending `CStarAlgebra`/`CStarRing` (which
  constrain the type's `≤`), and that `CommCStarAlgebra C(α, ℂ)` instances are declared in
  `Mathlib/Analysis/CStarAlgebra/ContinuousMap.lean`. The order in the claim is therefore the
  genuine C*-order (pointwise, via `ComplexOrder`/`Complex.le_def`), and the norm is the
  actual CMap sup norm. No fake custom instance.
- **No float shortcut.** All load-bearing steps (summability, exp identification, rigidity,
  16≤4 falsity) are exact Lean proofs; my numeric checks are corroborative only, and my own
  checker's two initial failures confirm the recorded cancellation caveat.

## 4. NOVELTY / SUBSTANTIVE gate — PASS as bounded (fresh, independent)

Fresh searches of my own (not inherited):
- **DuckDuckGo multi-angle** ("C*-algebraic Bieberbach" + counterexample/refutation; Banach-
  space univalent coefficient bounds; superposition/exp injectivity): only the source and its
  mirrors (Zenodo, ResearchGate, Authorea, Scribd, europepmc). No prior refutation, no
  subsuming theorem, no author retraction.
- **OpenAlex:** source W4290635513 `cited_by_count: 0`; full-text search for "C-algebraic
  Bieberbach conjecture" returns only the author's own deposits of the same manuscript
  (Preprints/Authorea/OSF). No citing work, no follow-up resolution.
- **Europe PMC:** PPR529287, `citedByCount: 0`, version 1.
- **count-ex-machina** (GitHub, fresh read): 19 admitted cases, none touching C*-algebraic
  Bieberbach or Krishna's conjectures. (Semantic Scholar rate-limited 429; preprints.org 403
  — retained access limits, disclosed.)
- **Wider angles:** Nemytskii/superposition-injectivity hits are classical Lp/Sobolev
  results; the classical several-complex-variable failure of Bieberbach is a different
  setting (not an A-coefficient one-variable power series) and is not cited as proof.

**Substantive:** a new, explicitly posed open question (two conjunct conjectures 1.2/1.4 as
ONE combined outcome) resolved by refutation, with genuine mathematical content (global
injectivity against a non-injective pointwise fiber). Distinct sources/statements/witnesses
from accepted C*-Novak #10, C*-polynomial #11, C*-Sendov #16; the shared connectedness
toolbox is credited, not double-counted. Scalar Bieberbach untouched. The user standard —
genuine new math, not helper/formulation credit — is met; classical tools (Banach summability,
exponential identity, connectedness rigidity) are credited and uncounted.

**Limits:** bounded negative searches; zero citations ≠ proof of no prior art; no absolute
priority claimed anywhere in the candidate or this review.

## 5. MANUSCRIPT gate — PASS

- `paper.pdf` in my copy: exactly 2 pages (pdfinfo + render). **Both pages rendered and read**
  (`render/page-1.png`, `render/page-2.png`).
- **Math-vs-Lean type comparison, line by line:** c_n = a^{n−1}/n! with a(t)=8t ≡ `coefficient
  parameter`; F(u)=Σc_n u^n ≡ `witnessMap`/`entireMap`; aF(u)=exp(au)−1 ≡
  `entireMap_exp_identity`; scalar evaluation ≡ `exp_apply`; F(u)(0)=u(0) ≡
  `witnessMap_at_zero`; the h(t)=8t(u−v) rigidity argument ≡ `witnessMap_injective` via
  `continuous_exp_kernel_zero`; c₂(1)=4 and "16 ≤ 4" contradiction ≡ `coefficient_two_at_one`
  + `coefficient_two_order_failure`; endpoint names, Lean 4.34.1 and mathlib d13f23b… stated
  in the paper match the certificate.
- **Scope/attribution honest:** Conjectures 1.2 and 1.4 only; "the separate invertible-coefficient
  variants are not claimed refuted"; classical scalar theorem untouched; ONE prospective
  outcome; no worldwide priority claim; source [1] cited exactly (Preprints (2022) v1,
  Conjectures 1.2 and 1.4, pp. 2–3, DOI 10.20944/preprints202208.0140.v1); genuine-author
  Zenodo deposit (doi:10.5281/zenodo.6917925) disclosed with the direct-PDF access limit;
  preliminary review passed, **final review honestly marked pending** in the frozen paper —
  accurate at its freeze time; this review completes it.
- `paper-qa.json` binds tex/pdf bytes (hashes match the manifest) and 28/4 counts. My render
  PNG hashes differ from the parent's recorded render hashes only by raster settings.

## Strongest objections (all weighed; none gate-breaking)

1. **Source bytes are the Zenodo deposit, not preprints.org.** The direct preprints.org 403
   persists (re-confirmed today). Text-level agreement between the parent's web-tool reading
   and the Zenodo deposit, plus the live API checksum match and two further mirrors, reduce
   the residual divergence risk to very low but not zero. Properly disclosed in the paper.
2. **Conjecture 1.4's derivative-domain reading.** The extracted text shows "D(0,1)" on the
   f' line (asterisk separated by the line break); immaterial here — the witness's derivative
   series converges on all of A, satisfying any reading of the antecedent.
3. **The `≤` order in the formal claim** is elaborated via the pointwise ComplexOrder
   instance; its C*-order status rests on mathlib's own `CommCStarAlgebra C(α,ℂ)` instance
   chain (CStarRing constrains `≤`), which I verified exists in the pinned revision. The
   `sourceCStarStructure` abbrev is documentation and not referenced in the final proofs —
   acceptable, since the order compatibility is certified by the instance chain itself.
4. **Novelty is bounded and the construction is elementary once seen.** Zero-citation and
   empty-search evidence cannot exclude inaccessible prior art; no priority is claimed, and
   the candidate is explicit about this.
5. **The unbounded-K family is mathematical, not formalized** (fixed K=8 formalized; the
   paper says so) — correctly carrying no count.

## Files in this lane

`copy/` (verified frozen candidate + my replay artifacts in `copy/build/verified/`),
`render/page-{1,2}.png`, `math/final_checks.py`, `math/final-checks-run.log`,
`hash-verify.log`, `provenance.json`, this `review.md`. Written only inside
`lanes/pi-cstar-bieberbach-final-review`. No parent/shared edits, no counts, no git, no
contacts, no posts, no uploads, no agent polls.
