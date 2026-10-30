# Preliminary adversarial review — root-bessel-mahler-r15 (Bessel–Mahler all-p asymptotic)

Reviewer: Pi GLM-5.3-Flash-EXL3, thinking=high, STANDARD speed. Solo, no children.
Date: 28 October 2026. Lane: `lanes/pi-bessel-mahler-preliminary-review-r1/`.
Candidate: frozen root-bessel-mahler-r15@9b92b4a0b9, 7 hashes in
`lanes/root-bessel-mahler-r15/review-freeze.json`. **Credit 0. No acceptance by this review.**

## Verdict summary

| Gate | Result |
|---|---|
| MATH (independent) | **PASS** — proof correct; all bounds re-derived and re-verified independently |
| SOURCE fidelity | **PASS** — target statement, page, and equivalence chain verified against the actual PDF |
| NOVELTY / prior art | **NO SUBSUMPTION FOUND** (bounded search; not a priority certificate) |
| SUBSTANTIVE (non-routineness) | **PASS-AS-ARGUED** — no complete published bridge exists; strongest objection analyzed and rebutted below |
| FORMAL (Lean endpoint) | **NOT EVALUATED — no endpoint exists ⇒ no PASS** |

Recommendation to root: eligible to proceed to formalization/paper work **conditional on the
open leads in "Residual risks"**; no automatic credit. The follow-up [21] remains unpublished
as of today; if it appears before acceptance, it must be read in full body before any credit.

## 1. Frozen-artifact verification

All 7 frozen paths re-hashed **before** review work began and **again after** all review writes
(see §7): every sha256 matches `review-freeze.json` exactly. No git/shared/other-lane writes.

## 2. Independent mathematical verification (MATH: PASS)

I re-derived every step from scratch (hand derivation, not inheriting root correctness), then
confirmed by independent computation in my lane.

**(a) Identity (1).** Z_n(r) = c_n ∫_{-1}^{1} e^{rt}(1−t²)^{d/2} dt = Γ(n/2+1)(2/r)^{n/2} I_{n/2}(r),
d = n−1, c_n = Γ(n/2+1)/(√π Γ((n+1)/2)).
Hand check: expand e^{rt} = Σ r^{2k}t^{2k}/(2k)! (odd moments vanish), evaluate
∫_{−1}^{1} t^{2k}(1−t²)^{d/2}dt = B(k+1/2, d/2+1), use (2k)! = 4^k k!Γ(k+1/2)/√π; the
coefficients match the I_{n/2} series term-by-term. No asymptotics used. This is exactly the
source's Claim 2.23 (cited there to DLMF 10.32.2) times c_n.
Independent numerics: direct mpmath t-quadrature vs closed form, 9 points
(n ∈ {4,7,15} × r ∈ {0.5, 3, 40}), relative error < 1e−28.

**(b) Uniform bounds (3).** Upper: pointwise integrand ≤ exp(d·psi(u)) on an interval of
length 2. Lower: on t ∈ [t(u), t(u)+(1−t(u))/d],
(1−t²)/(1−t(u)²) = [(1−t)/(1−t(u))]·[(1+t)/(1+t(u))] ≥ (1−1/d)·1, so the integrand is
≥ exp(d·psi(u))(1−1/d)^{d/2} ≥ exp(d·psi(u))/2 (Bernoulli, d/2 ≥ 1); length (1−t(u))/d ≥
1/[2(1+u)]. All factors verified. Note this lower-interval estimate is uniform in d and u and
makes **no** Debye/uniform-Bessel assumption — confirmed.
Numerics: sandwich holds at 15 points, n ∈ {3,9,40} × u ∈ {0, 0.001, 1, 25, 400}.

**(c) Calculus of H_p.** psi'(u) = t(u) because the envelope term cancels at the maximizer
(u = t/(1−t²)); verified symbolically (my own sympy run agrees with root's). t'(u) = 2/(s(1+s)),
s = √(1+4u²) > 0. u·t(u) = t²/(1−t²) strictly increases 0→∞, so H_p has the unique maximizer
u_p = √(p(1+p)), t(u_p) = √(p/(1+p)); psi(u_p) = p − ½log(1+p); h_p = ½log p +
½(1+1/p)log(1+p) − 1. All re-derived; matches (4).

**(d) Integrability (5) and Laplace bounds (6)–(7).** psi ≥ 0 (psi is increasing in t², = 0 at
t = 0); for u ≥ 1 evaluate the psi-sup at t = ½: psi(u) ≥ u/2 + ½log(3/4). Hence
(1+u)^{1/p}e^{H_p} ≤ C u^{1+1/p} e^{−u/(2p)}: integrable. (6) is immediate from H_p ≤ h_p;
(7) from the mean value theorem with L_p = sup_{[u_p,u_p+1]}|H_p'| < ∞ on
[u_p, u_p+1/d]. Both re-derived; both logarithmic integrals equal d·h_p + O_p(log d). This is
a self-contained elementary Laplace estimate — the root is right that no unstated uniform
saddle-point theorem is invoked.

**(e) Assembly (8)–(9).** Change of variables r = du and the exact identity give
F = [Γ(n/2+1)2^{n/2}]^{1/p} d^n ∫_0^∞ u^{n−1} Z_n(du)^{−1/p} du; inserting (3) gives exactly
the stated sandwich with J_d weights; log-algebra checked term by term. Stirling
(1/p)logΓ(n/2+1) = (n/(2p))log n − (n/(2p))log 2 − n/(2p) + O_p(log n) collapses (9) to
log F = n[(1+1/(2p))log n − 1/(2p) + h_p] + O_p(log n) = o(n) + n·log(const),
const = n^{1+1/(2p)} e^{−1−1/(2p)} √(p(1+p)^{1+1/p}).

**(f) Constant matches the source exactly.** I read the actual page-32 render
(`renders/source-conjectures-p32.png`): Conjecture 5.2 RHS is
(n^{1+1/(2p)}/e^{1+1/(2p)} · √(p(1+p)^{1+1/p}))^n e^{o(n)}. Identical. The source proves only
p = 1 (its own words) and states the I-denominator integral is one "we could not trace in the
literature."

**(g) The "also proves Conjecture 5.1" claim — verified independently.** I initially found an
apparent exponential mismatch (2^{(1−p)/(2p)}) between 5.2's constant, Corollary 3.8's
prefactor, and 5.1's constant, which would have been a **fatal source-fidelity gap**. I resolved
it by deriving Corollary 3.8's prefactor myself from Definition 1.7/(1.3) and the exact
∫_B e^{⟨x,z⟩}dx = (2π)^{n/2} I_{n/2}(|z|)/|z|^{n/2}:

  M_p(B_2^n) = nπ^n / (2^{n/(2p)} p^n Γ(1+n/2)^{2+1/p}) · F_{n,p}  (exact),

verified **exactly** against the definition-based computation M_p(B) = |B|∫e^{−h_{B,p}} at
n = 2 (p ∈ {0.5, 1, 2}) and n = 4 (p ∈ {0.5, 2}) — ratio 1.0 to displayed precision in all five
cases. A 300-dpi crop of the PDF confirms the printed prefactor is 2^{n/(2p)} (my first
low-res read of "2^{n/2}" was wrong). Combining with (e) and Stirling reproduces exactly the
Conjecture 5.1 constant (2π√((1+p)^{(1+p)/p}/p))^n of Lemma 3.6/Conjecture 5.1. The root's
claim stands. (An apparent n^{-1/(2p)}π^{−1/(2p)} subexponential factor from Stirling's
prefactor is absorbed in O_p(log n).)

**(h) Independent end-to-end numerics.** My own evaluation of the **original** integral
(exact w = log u substitution; no inequalities; separate from the root's J_d route), matched the
root's `checks.json` diagnostics at **all 12 overlapping (p, n) points to ~1e−12**, and gives
(log F − headline)/log n bounded by |·| ≤ 3.1 across p ∈ {0.25, 0.5, 1, 2, 5, 8} and
n ∈ {12, 40, 120, 300}, with the expected O_p(log n) drift. This confirms the O_p(log n)
claim empirically. (A first naive quadrature attempt of mine failed numerically — complex
values from negative-u sampling — and was discarded; the failure was in my script, not the
mathematics; kept as `independent_check.py` with a note.)

**No gap found.** The proof is complete, self-contained, and stronger than the conjecture
(O_p(log n) for every fixed p > 0, plus Conjecture 5.1).

## 3. SOURCE fidelity (PASS)

- Target: Mastrantonis arXiv:2411.10439v2 [math.FA], 26 Nov 2024 (v2 stamp verified in the
  frozen txt and the arXiv abs page), Conjecture 5.2, printed p. 32, equivalent (source's own
  words, "in view of Corollary 3.8") to Conjecture 5.1. MathDB 365832 relates.
- The candidate quotes the exact integrand r^{n+n/(2p)−1}/I_{n/2}(r)^{1/p} and the exact
  constant; verified against the page image.
- The proof does **not** use the source's functional Santaló Theorem 1.11 or the K-comparison
  Corollary 5.4 (nor Lemma 5.3/Gaunt); it re-proves what it needs from Claim 2.23's exact
  identity. No silent reliance — confirmed by reading PROOF.md's dependency list.
- The p = 1 case is excluded from any credit claim. ✓

## 4. NOVELTY / prior-art investigation (bounded; no subsumption found)

1. **Author follow-up [21] ("Lp-Legendre transforms and Mahler integrals: Asymptotics of the
   extremizers", in preparation 2024): not found.** The author's arXiv listing (7 papers,
   checked via three independent index mirrors) contains no such paper as of today; the most
   recent math items are 2401.10836 (Lp-polar Santaló, published 2025) and 2401.10992
   (Two-dimensional Blocki/Lp-Mahler/Bourgain, Indiana UMJ 2026-03-27). Title/abstract
   clearance is **not** claimed as clearance — but no public body exists to read. **This lead
   must be re-checked at acceptance time.**
2. **Closest document — the author's 2025 UMD PhD thesis** (primary public body, downloaded
   and read in the relevant section, sha256 a55377b6d43de69b8b1f1096d062603b38b606945f4c2e7758ec4f13cdef05a7):
   §5.5 "Asymptotics" (thesis pp. 214–217) restates the identical conjectures (5.50/5.51) and
   says verbatim "We prove Conjectures 5.50 and 5.51 **for p = 1**", and repeats that the
   Bessel-denominator integral "we could not trace in the literature". **General p is open in
   the closest author document.** Thesis Chapter 5 is the same content as 2411.10439; its
   §5.5.2 handles only p = 1 via the exact K-coefficient comparison (Lemma 5.54) for odd n.
3. **Pinned OpenAI catalogue** (sources/CONTENTS.md): family 087 resolves the classical
   symmetric/nonsymmetric geometric Mahler conjectures — a **different question** (no Lp
   Bessel-integral asymptotics; the only "Bessel" hit in CONTENTS.md is an unrelated XY-model
   entry). No subsuming item. Not audited upstream (per AGENTS.md).
4. **Local prior registries:** exact-ID/title grep (365832, bessel+mahler) over prior campaign
   ledgers, findings, notes, reviews: no prior candidate family on this question. Coverage
   bounded — not a priority certificate.
5. **Web search** for independent resolutions of the Bessel-denominator integral / M_p(B_2^n)
   asymptotics (2025–2026): nothing found beyond the source/thesis themselves. Bounded search.

## 5. SUBSTANTIVE (strongest objection, analyzed)

**Strongest objection (the "standard one-page Laplace" route):** reduce I^{−1/p} via the
source's own Gaunt-based Corollary 5.4/5.53 to a K-integral
∫ r^{n+3n/(2p)−1} K_{n/2+1}(r)^{1/p} dr, apply a published **uniform** asymptotic of K_ν(r)
(with ν = n/2+1 and r/ν in a range including the relevant peak), and finish with Laplace's
method — a routine corollary of classical tools, which would exclude discovery credit.

**Why this does not currently exclude credit:**

- *No such bridge is exhibited anywhere I could locate.* The source and thesis — experts who
  explicitly wanted this asymptotic and had the K-reduction on the same page — stopped at
  p = 1 and handled it by an **exact** coefficient comparison instead, calling the
  I-denominator integral untraced in the literature. That is evidence the "one-page" route is
  not routine even for its authors.
- *The uniform asymptotics needed are not the standard ones.* At the Laplace peak of the
  I-integral, r* = (n−1)√(p(1+p)) while ν = n/2, so ν/r* → ∞ as p → 0⁺; for fixed p the ratio
  ν/r* = 1/(2√(p(1+p))) is an O(1) constant. Any applicable published theorem must be uniform
  in **both** ν → ∞ and r/ν ∈ (0, ∞) (full uniform-Debye regime) **with error control that
  survives raising to the power 1/p and integration against a large power of r**. DLMF §10.41 /
  Watson give pieces of this, but no located published statement yields the exact exponential
  constant for the present integrand without substantial additional work. On the K side the
  saddle is genuinely two-dimensional (K's integral representation saddle in s AND the r-
  integration), which is more, not less, work than the root's route.
- *A complete explicit bridge is the required standard, and it does not exist on paper.*
  Per campaign rules, "any classical tool exists" does not make a result routine; a complete
  written reduction from a named published theorem to the exact statement would. None found.
- *The candidate is strictly stronger than the conjecture* (O_p(log n) vs e^{o(n)}) and covers
  all p > 0 with explicit uniform-in-r integral bounds — beyond what any generic "Laplace
  principle" citation would give, and independently useful (e.g., the bounds (3) themselves).

**Falsifier for this objection (what would flip SUBSTANTIVE):** a published theorem giving
two-sided bounds of the form c₁·(lower) ≤ r^{−ν}(...)-normalized I_ν(r) ≤ c₂·(upper) valid for
all r ≥ 0, all ν ≥ ν₀, with constants depending only on the ratio r/ν (or an explicit uniform
Debye expansion with error e^{O(ratio²)}) — plus a written derivation reaching the exact
Conjecture 5.2 constant and the O_p(log n) error in ≤ ~1 page. I searched for such a
statement; none located. (The root's bounds (3) are exactly of this shape for the specific
normalization Z_n — which is part of why they are valuable.)

## 6. FORMAL gate and remaining Lean bridges (no endpoint ⇒ no PASS)

No Lean certificate exists. A literal endpoint would need, at minimum (cost estimate,
experienced Lean 4/mathlib, sequential days):

1. Exact identity (1): termwise integration of the I-series against (1−t²)^{d/2}, beta-integral
   evaluation, duplication formula for (2k)!. mathlib has `besselI` (via series?) and `Beta`/
   `Gamma`; the termwise swap is the heavy part. ~1–2 days.
2. psi, t(u), H_p: elementary real analysis; unique-maximizer proof via monotonicity of
   u·t(u); ~0.5–1 day.
3. Uniform bounds (3) and c_n bounds (2): Bernoulli inequality instances, interval estimates; ~0.5 day.
4. Integrability (5) and Laplace bounds (6)–(7): explicit L_p, C_p constructions (e.g. via
   interval splitting); ~1–2 days.
5. Sandwich (8) + Stirling (mathlib has Stirling-type asymptotics? may need the explicit
   O(log n) form) + final constant algebra; ~1 day.
6. For the **full-source** Conjecture 5.1 endpoint additionally: Corollary 3.8's exact
   prefactor (my §2(g) derivation), Lemma 3.6 Gaussian value, and the e^{o(n)} ⟹ statement
   translation. ~1–2 days.

Estimated total: ~1–2 weeks sequential; no `sorry`/axioms beyond the three allowed lemmas.
Conditional-Laplace-lemma shortcuts would **not** meet the gate (root's own note is correct).

## 7. Residual risks (must-clear before any acceptance)

1. **Follow-up [21] may appear** (announced "in preparation" 2024; author active through 2026).
   If it appears, its actual body must be read before credit; abstract clearance insufficient.
2. **Uninspected venues:** the thesis bibliography's items [31]–[35] (the paper's [12]–[16])
   were not individually read; they are classical Bessel-integral references the author used
   for p = 1 and are unlikely to contain the general-p denominator integral (the author says
   it is untraced), but a body-level check of any that concern I-denominator integrals is
   advisable at acceptance time.
3. MathDB 365832 label state was taken from root's record; I did not re-query MathDB (site
   reliability). An open label is not novelty evidence either way.
4. Bounded search: no claim of absolute priority.

## 8. Files (this lane only)

- `independent_check.py`, `independent_check.json` — identity (1) direct-quadrature check,
  sandwich points; (contains the discarded naive-quadrature attempt with diagnosis).
- `independent_check2.py`, `independent_check2.json` — exact w-substitution evaluation of the
  original integral, 16 (p, n) points, err/log n bounded.
- `cross_validate.py` — 12-point match vs root `checks.json` (~1e−12).
- `check_cor38_n2.py`, n=2/n=4 prefactor verification scripts and runs.
- `cor38-26.png`, `cor38crop-26.png` — page-26 renders (Corollary 3.8).
- `provenance.json` — sources, hashes, dates.

## 9. Verdict

- MATH: PASS (independent derivation + independent computation).
- SOURCE: PASS (actual p. 32 read; constants exact; 5.1 implication verified via independently
  re-derived Corollary 3.8 prefactor, confirmed numerically at n = 2, 4).
- NOVELTY: no subsuming prior art located in a bounded search; closest documents (source v2,
  2025 thesis) leave general p open. Not a priority certificate.
- SUBSTANTIVE: the routine-corollary objection is analyzed and currently rebutted; no complete
  published bridge exists. Rebuttal stands unless the §5 falsifier is exhibited.
- FORMAL: no endpoint — **no PASS**; cost table above.
- No credit recommended or counted by this review. Candidate **eligible to continue** to
  Lean/paper stages at root's discretion, subject to §7 risk re-checks.
