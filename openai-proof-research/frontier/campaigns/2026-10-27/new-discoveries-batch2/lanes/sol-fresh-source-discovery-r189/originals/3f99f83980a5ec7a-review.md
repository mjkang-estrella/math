# Preliminary independent review — C*-algebraic Bieberbach general-coefficient refutation

Lane: `pi-cstar-bieberbach-preliminary-review` · 2026-10-27 · solo, no children, standard speed.
Parent proposal: `lanes/parent-cstar-bieberbach/PROOF.md`, frozen at git `7f42783725`
(`PROOF.md` sha256 `1b6cad19d0bd0b43d4210d0d9389bc6378430b59b0d0ae393fe4dd33e8c2f2ba`,
verified byte-identical to the working copy). Tally untouched: **27/30**, credit 0, no count edits.

**Verdict: SOUND PRELIMINARY — recommend the parent proceed to formal (Lean) stage as an
uncounted candidate.** Source, mathematics, scope, and bounded novelty all check out; no public
refutation or subsuming result found. Objections and access limits listed at the end.

---

## 1. SOURCE gate — PASS (upgraded: genuine PDF now obtained and visually read)

- **Genuine body obtained.** `preprints.org/.../download` is Akamai-403 for both local curl and
  the fetch tool, but the author's own Zenodo deposit (record **6917925**,
  doi:10.5281/zenodo.6917925, creator "K. Mahesh Krishna", version 1, 2022-07-28, 20 pp., pdfTeX)
  downloads cleanly. Its declared md5 `233c4203a5a0bb4b3877ca5b5ee5f57c` matches my download
  exactly (`sources/zenodo-BIEBERBACH.pdf`, sha256 `2d537f04…`).
- **Text identity.** `pdftotext` output is byte-identical (modulo trailing whitespace) to the
  parent's web-PDF-tool text `pi-cstar-polynomial-review/sources/krishna-2208.txt` (diff exit 0).
  The parent's reading was of genuine source content; the mislabelled HTML file was indeed not used.
- **Visual read (parent had none).** Pages 2–3 rendered and read (`sources/page-02.png`,
  `page-03.png`): Conjecture **1.2** (general coefficients: `a_n a_n* ≤ n²`, `a_n* a_n ≤ n²`
  elementwise, antecedents = norm convergence on 𝔻\*(0,1) + injectivity on 𝔻\*(0,1)),
  **1.3** (invertible), **1.4** (strong general form: additionally the derivative series
  `f'(z) = 1 + Σ n a_n z^{n−1}` converges in norm on 𝔻\*(0,1)), 1.5–1.7, and Theorem 1.8 are
  verbatim as the parent quotes. 𝔻\*(0,1) is literally "all elements of A having norm less than 1".
- **Version status.** Europe PMC PPR529287: `versionNumber 1`, published 2022-08-08; Zenodo holds
  only version 1; no later version located. "v1 latest" confirmed as far as accessible.
- **MathDB.** No MathDB record exists for this conjecture (suggestion API checked for
  Bieberbach / C\*-algebraic; existing C\*-records are Novak 351633, Sendov 353909, Schoenberg
  355008, Casas-Alvero 355066, de Bruin-Sharma 355009). Nearest Bieberbach record 329698 is the
  distinct several-variable S⁰(𝔹_n) class problem.

## 2. MATH gate — PASS (independent re-derivation + fresh checker)

All claims re-derived from scratch; every computational claim re-verified by my own checker
(`math/check_bieberbach.py`, run log `math/check-run-20261027.log`, **20/20 PASS**; sha256 in
`provenance.json`):

1. **Construction.** A = C([0,1],C), τ(t)=t, K=8, a₁=1, aₙ=(Kτ)ⁿ⁻¹/n! (n≥2).
   ‖aₙ‖ = Kⁿ⁻¹/n! (‖τ‖=1), so Σ‖aₙuⁿ‖ ≤ (e^{K‖u‖}−1)/K < ∞: the series converges in norm **on all
   of A**, far beyond the required 𝔻\*(0,1). The derivative series is bounded by e^{K‖u‖}−1 < ∞
   everywhere, so the Conjecture 1.4 antecedent also holds globally. ✔
2. **Closed form.** F(u)(t) = (e^{Ktu(t)}−1)/(Kt) for t>0, F(u)(0)=u(0), with a removable
   singularity at 0 — so F(u) ∈ A. Verified in **mpmath 50 dps** over 120 random complex cubics ×
   5 times each, max relative error 1.4×10⁻³⁸. (Caution recorded: plain double precision
   *fails* this check for |Ktu| ≳ 40 by catastrophic cancellation — terms ~e^{|s|} canceling to
   O(1); an artifact, not a math error, but the formal stage must not rely on float sampling.)
3. **Global injectivity — and it is genuinely *global*, not fiberwise.** F(u)=F(v) gives, for each
   t>0, h(t)=Kt(u(t)−v(t)) ∈ 2πiℤ. The checker confirms the pointwise fiber is **not** injective
   (x and x+2πi/(Kt) collide), so the rigidity is essential: h is continuous on connected [0,1]
   with h(0)=0 (the Kt anchor), its image lies in a discrete set, hence h≡0; u=v on t>0 and at 0
   by continuity. Any pointwise collision partner is provably discontinuous at the jump
   (|v(0.2⁺)−v(0.2⁻)| = 3.927 = 2π/(K·0.2)). The parent's challenge question — global injectivity
   vs fiber injectivity — is correctly resolved: global holds, fiber does not.
4. **Coefficient failure.** a₂ = Kτ/2, a₂a₂\* = K²τ²/4; at t=1 this is **16 > 4 = n²**, violating
   the elementwise order bound on the open set t>1/2 (not an endpoint or norm-convention quibble);
   ‖a₂‖=4>2. a₂ vanishes at t=0, so it is **non-invertible**: Theorem 1.8 and Conjectures
   1.3/1.5 are untouched, consistently with the source's own degree-2 invertible theorem.
   Arbitrary K>4 refutes; K→∞ makes ‖aₙ‖=Kⁿ⁻¹/n! unbounded at every fixed n≥2.

**Scope discipline (verified, stronger than the parent claims).** Conjectures 1.9–1.13
(Robertson) require f(z)=z+Σb₂ₙ₋₁z²ⁿ⁻¹, **odd powers only** — this construction (a₂≠0) is not
even of that form, so Robertson is *not* a corollary at all. Conjecture 1.15 (Lebedev–Milin) has
hypothesis (iv) f(z)=e^{g(z)}z; that forces e^{g(z)} invertible for every z, but
(e^{Ktz}−1)/(Ktz) vanishes at z=2πi/(Kt) ∈ 𝔻\*(0,1) for t>2π/K, so (iv) fails — Lebedev–Milin is
not touched either. Conj 1.6/1.7 need polynomials; F is not one. **The refutation is exactly
Conj 1.2 + 1.4**, so the "same-family corollaries = at most ONE outcome" rule has an empty
corollary set here — one outcome, cleanly.

## 3. NOVELTY gate — PASS as bounded, documented, no priority claim

- Local trureturing registry (read-only): only Bieberbach mention is inside the distinct
  higher-order Smale problem file. count-ex-machina cloned fresh: no Bieberbach/Krishna entries.
- OpenAlex W4290635513 and Europe PMC PPR529287: **0 citing works**. Semantic Scholar does not
  index the DOI. DuckDuckGo multi-angle searches surface only the source and mirrors (Zenodo,
  ResearchGate, Authorea, Scribd, europepmc) — no counterexample, no refutation, no retraction.
- Author follow-up sweep (Zenodo API, all 27 "K. Mahesh Krishna" records): no later paper touches
  Bieberbach or C\*-power series; the 2026-09-01 item is the distinct Non-Archimedean Smale work.
- Nemytskii/superposition-injectivity literature hits are classical Lp/Sobolev/almost-periodic
  results; none state or subsume this exponential superposition's injectivity or its use against
  the source conjecture. The several-variable triangular shear failure of Bieberbach is *not*
  an A-coefficient one-variable power series, and the parent correctly does not cite it as proof.
- Limits: ResearchGate/Scholar full citation graphs and the preprints.org page itself were not
  machine-readable this session; this is a bounded negative search, not an absolute-priority
  certificate. (If a public refutation is later found, formal investment should stop and be
  documented, per parent instructions.)

## 4. SUBSTANTIVE gate — PASS as a distinct outcome (no double counting)

- **vs accepted Sendov #16 (MathDB 353909) and the open Smale lane (2206.08154v1 Conj 2.1):**
  different sources, different conjectured statements, different witnesses. The shared ingredient
  is a connectedness/branch-rigidity argument in C([0,1],C) — the same *toolbox*, but here the
  rigidity is a discrete-image + vanishing-anchor argument for an **entire non-polynomial**
  function series, with no polynomial, no roots, and no critical points. This is a new open
  question resolved (by refutation), so it is substantive under the ledger standard and does not
  collide with the other two outcomes. If the Smale lane is later accepted, it counts separately;
  nothing in this lane affects it.
- **Not trivial.** Injectivity is the real content: naive large-coefficient quadratic attempts
  fail injectivity (e.g. over C⊕C, z+3pz² with a projection p collides at 0 and −1/3), and the
  pointwise fiber here is non-injective. The Kt-anchor + discrete-image rigidity is the minimal
  mechanism making the antecedents true while the conclusion fails. Same genre as accepted
  C\*-Novak #10 and C\*-polynomial #11 (source-posed C\*-conjecture refuted in a concrete
  commutative A), which the ledger has already counted as substantive.
- Feasibility of the formal stage is good: everything is elementwise in C([0,1],C); convergence
  bounds, the closed-form identification, the rigidity lemma (continuous map from connected
  space to discrete set), and the order violation are all Lean-able; no analysis of the actual
  Fréchet derivative is needed (1.4's antecedent is series convergence, which the bounds give).

## 5. Strongest objections / limits (for the formal stage)

1. **No genuine preprints.org bytes.** The genuine body rests on the author's Zenodo mirror
   (md5-verified) plus the parent's independent web-PDF reading of the preprints.org copy; the two
   agree byte-for-byte in text. Residual risk that preprints.org v1 differs from the Zenodo
   deposit is very low but nonzero; record it in the paper's source section.
2. **Semantic Scholar and ResearchGate citation graphs unreadable** (429 / bot-walls); citation
   coverage rests on OpenAlex + Europe PMC + search engines. Bounded, disclosed.
3. **Injectivity proof is correct but the formal certificate must encode it globally** (h ≡ 0 on
   [0,1]), not as a sampled or fiberwise argument; also the mpmath-vs-float cancellation caveat
   above means no numerical-witness shortcut is available for the identification step.
4. **No Lean, no paper, no acceptance exists yet** for this lead — this review grants nothing
   beyond "mathematically sound preliminary, proceed".
5. Novelty is bounded: the construction is elementary once seen; no priority claim is made or
   warranted by these searches.

## 6. Recommended next step

Parent: integrate this review; keep credit 0 and tally 27/30; on request, open a formal lane
(Lean certificate for: norm/derivative-series convergence, closed-form identification with
removable singularity, global injectivity via discrete-image rigidity, a₂a₂\* ≰ 4 elementwise,
and the non-invertibility of a₂) plus paper and packet, still ONE outcome covering Conj 1.2 and
1.4 and any same-construction corollaries.

Files in this lane: `provenance.json`, `sources/zenodo-BIEBERBACH.pdf` (+ `.txt`, page PNGs),
`math/check_bieberbach.py`, `math/check-run-20261027.log`, this `review.md`.
Preserved untouched: all other lanes, including `pi-analysis-discovery-r13`.
