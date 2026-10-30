# Independent adversarial review — KILBAS-CLASSICAL-REDUCTION (root-new-targets-r13)

Reviewer: pi GLM-5.3-Flash (thinking=high), SOLO, no children. 28 October 2026.
Lane: `lanes/pi-kilbas-classical-review-r1`. No shared/ledger/lane edits; no acceptance or count actions taken.

## Verdict

1. **Ordinary proof validity: PASS.** The root's ordinary argument is complete, correct,
   and every step survived independent rederivation (analytically, not only by citation).
   Constants match the source statement literally. alpha=1, x=0 and the full parameter
   range are covered.
2. **Substantive eligibility: NOT ELIGIBLE for discovery credit.** Two independent and
   decisive grounds:
   - **(New finding, decisive) A public machine-checked resolution of this exact
     conjecture already exists** — "trureturing" (The Omega Institute) public mdbook +
     pinned Lean certificate with axiom closure exactly {propext, Classical.choice,
     Quot.sound}. Details in section 5.
   - **(Concurring with root) Even without that, the result is a routine corollary of
     published general theorems**: the two bounds are an instantiation of a *generic*
     sandwich valid for **every** killed subordinator exponential functional, and the
     only special content is a two-line beta-integral verification that the gamma-ratio
     is a killed subordinator exponent.
3. Root's recommendation **NO DISCOVERY CREDIT** is **CONFIRMED**, on stronger grounds
   than root stated (root did not know of the public resolution).

Total remains 32/60; candidate credit 0. No acceptance/count/ledger actions.

## 1. Frozen inputs verified unchanged

All 26 files bound in `lanes/root-new-targets-r13/review-hashes.json` re-hashed with
sha256sum: **26/26 OK, zero mismatches** (checker output retained in provenance).

## 2. The target, read from the primary source (arXiv:2012.05666v1, cached PDF+text)

- Definition (text lines 19–24): E_{α,m,l}(z) = 1 + Σ_{n≥1} [∏_{k=1}^n
  Γ(1+α((k−1)m+l))/Γ(1+α((k−1)m+l+1))] z^n, for α,m>0, l>−1/α.
- **Conjecture 4.5 (lines 1066–1068):** for α∈(0,1], m>0, l>m−1/α, x≥0:
  1/(1 + x·Γ(1+α(l−m))/Γ(1+α(l−m+1))) ≤ E_{α,m,l}(−x) ≤ 1/(1 + x·Γ(1+αl)/Γ(1+α(1+l))).

**Layout caution (review finding O1).** The PDF text extraction renders the conjecture's
compound fractions ambiguously. A naive linear reading suggests an extra outer factor
1/Γ(1+α(l−m)) (my checker's first reading), which is *false* (it would violate the bound
at x=0 whenever Γ(1+α(l−m))>1... verified for α=1, m=3 against e^{−x/m}). The correct
reading — bounds are literally 1/(1+x/φ(0)) and 1/(1+x/φ(1)) with φ as below — is pinned
by four independent facts: (a) the source's own Theorem 3.4 (the l=m−1 case, stated by
the source as covering the conjecture there) displays 1/(1+x·Γ(1+α(m−1))/Γ(1+αm)) whose
slope at 0 equals the exact asymptotic of Remark 3.5(a); (b) the large-x constant of the
lower bound then equals the source's Prop 4.3 constant exactly; (c) at x=0 both bounds
equal 1 = E_{α,m,l}(0) for all parameters; (d) the public trureturing resolution quotes
the journal Conjecture 4 in linearized form exactly matching this reading. The root's
file states the correct form.

## 3. Step-by-step independent verification of the root's ordinary proof

Notation: a = 1+α(l−m) > 0 (exactly the hypothesis l > m−1/α), b = αm > 0,
φ(s) = Γ(a+bs+α)/Γ(a+bs), s ≥ 0. Then a+bs = 1+α(l+(s−1)m).

**(i) φ is a killed-subordinator exponent — VERIFIED by my own derivation.** For
0<α<1, with u = e^{−t}, one integration by parts using
d[(u/(1−u))^α]/du = α u^{α−1}(1−u)^{−1−α} du (boundary terms vanish like
h(1−u)^{1−α}→0 at u↑1 and u^{a+α}→0 at u↓0) gives exactly

  ∫_0^∞ e^{−(a+α)t}(1−e^{−h t})/(1−e^{−t})^{1+α} dt
    = (Γ(1−α)/α)·[Γ(a+h+α)/Γ(a+h) − Γ(a+α)/Γ(a)],   h = bs,

i.e. φ(s) = φ(0) + ∫_0^∞ (1−e^{−s y}) ν(dy) with ν(dy) = (α/(bΓ(1−α)))
e^{−(a+α)y/b}(1−e^{−y/b})^{−1−α} dy > 0 after y = bt. Near 0, ν(dy) ~ C y^{−1−α};
∫_0^ε y ν(dy) < ∞ since α<1; exponential decay at ∞. So ν is a valid Lévy measure,
φ = κ + ψ Bernstein with κ = φ(0) > 0 killing. **This is genuine Bernstein status —
not merely logarithmically complete monotonicity and not a reciprocal/CM mix-up**
(hypothesis check requested by the task). At α=1: φ(s) = a+bs, a killed drift — the
general theorem below covers it and everything re-derives directly.

**(ii) Moment formula — VERIFIED by my own derivation, exact indexing.** For
ξ an unkilled subordinator with exponent ψ = φ−φ(0), ζ ~ Exp(κ) independent,
I = ∫_0^ζ e^{−ξ_t}dt, the simplex/Laplace-transform computation with increments
ξ_{t_i} − ξ_{t_{i−1}} gives exactly

  E[I^n] = n! / ∏_{k=1}^n (κ + ψ(k)) = n! / ∏_{k=1}^n φ(k),   n ≥ 1,

the product starting at k=1 over the **full killed** exponent. Independently confirmed
against the cached primary sources: Bertoin–Yor survey, Theorem 2(i)
(E[I_T^k] = k!/((q+Φ(1))···(q+Φ(k))), Φ unkilled, q killing) and Patie, eq. (1.2)
(E[I_φ^n] = Γ(n+1)/∏_{k=1}^n φ(k) with φ the *possibly killed* exponent) — the two
conventions agree and both match the root's indexing. Also verified numerically:
killed pure drift (exact integral) and a compound-Poisson killed subordinator
(Monte Carlo, checker T6).

**(iii) Coefficient identification — VERIFIED term-by-term.** The k-th factor of the
source's c_n is Γ(1+α(l+(k−1)m))/Γ(1+α(l+(k−1)m)+α) = 1/φ(k). Hence
E[e^{−xI}] = Σ (−x)^n c_n = E_{α,m,l}(−x). **Caution (O7):** the product does **not**
telescope (denominator step is b = αm, numerator step α; equal only if m=1). Any
attempt to rewrite c_n = Γ(1+αl)/Γ(1+α(l+nm)) is wrong for m ≠ 1; my checker
initially asserted this and correctly failed. The root's proof does not use
telescoping — the term-by-term match suffices and is exact.

**(iv) Entire-function identification — AIRTIGHT.** c_n > 0 (arguments
1+α(l+(k−1)m) > 0 since l > −1/α) and |c_n|^{1/n} → ∞, so the KS series is entire.
Monotone convergence gives E[e^{rI}] = Σ r^n c_n for r ≥ 0 (finiteness *derived*,
since the positive series converges), whence e^{|x|I} ∈ L¹, and dominated convergence
gives E[e^{−xI}] = Σ(−x)^n c_n for x ≥ 0. The root's two-step justification is exactly
this and is correct. (I ≤ ζ alone would NOT give E[e^{|x|I}] < ∞ for large |x|; the
positive-series step is essential and present.)

**(v) Lower bound — VERIFIED.** ξ_t ≥ 0 ⟹ I ≤ ζ pathwise ⟹ E[e^{−xI}] ≥
E[e^{−xζ}] = κ/(κ+x) = 1/(1+x/φ(0)), and 1/φ(0) = Γ(1+α(l−m))/Γ(1+α(l−m+1)) — the
conjectured lower constant literally. Consistency: φ(0) equals the source's Prop 4.3
asymptotic constant Γ(1+α(l+1−m))/Γ(1+α(l−m)) exactly (checker T7), so the generic
lower bound is asymptotically sharp here — no contradiction, strong coherence.

**(vi) Upper bound — VERIFIED, direction and independence correct.** Patie (abstract
and eq. (1.3); Bertoin–Yor Theorem 2(ii) for the killed case) supplies a positive J
**independent of I_φ** (pairwise independence — exactly what is needed) with
I·J =_d Exp(1) and moments E[J^n] = ∏_{k=1}^n φ(k), so E[J] = φ(1). Conditional on I,
r ↦ exp(−xIr/φ(1)) is convex, so Jensen gives
E[e^{−xIJ/φ(1)} | I] ≥ exp(−xI·E[J]/φ(1)) = e^{−xI}; taking expectations,
E[e^{−xI}] ≤ E[e^{−xIJ/φ(1)}] = 1/(1+x/φ(1)) = φ(1)/(φ(1)+x), with
1/φ(1) = Γ(1+αl)/Γ(1+α(1+l)) — the conjectured upper constant literally. The
direction is right (a decreasing-but-convex integrand; the bound needs E[J] = φ(1)
*exactly*, which the moment formula at n=1 provides).

**(vii) Generality.** Nothing above uses special structure of φ beyond "killed
subordinator exponent". Hence the **generic sandwich** φ(0)/(φ(0)+x) ≤ E[e^{−xI_φ}] ≤
φ(1)/(φ(1)+x) holds for *every* killed subordinator — a two-line consequence of
Bertoin–Yor Theorem 2 plus pathwise domination. The conjecture is the generic sandwich
instantiated at one explicit exponent. This is the precise sense in which the result is
a routine classical corollary. Note the trureturing resolution's own "PROVED in prose"
triage item states the same genericity (any φ(s) = A + ds + ∫_0^1(1−λ^s)K(λ)dλ).

## 4. My independent numerical checker (corroboration only — not proof)

`checker.py` (this lane; mpmath 1.3.0 + numpy, single process, peak RSS 85 MiB <
512 MiB, no pools). All PASS:

- T1/T1b: Lévy-representation identity for 7 (a,b,α,s) combos incl. α=0.95, max rel
  err 7.0e-14 (quadrature-limited); by-parts closed form rel err 3.1e-16.
- T2: ν integrability incl. the y^{−1−α} singularity.
- T3: ∏_{k=1}^n 1/φ(k) equals the literal KS c_n term-by-term, n = 1,2,5,12,40
  (rel err < 1e-50). Telescoping explicitly *refuted* (see O7).
- T4: conjectured bounds ≡ 1/(1+x/φ(0)), 1/(1+x/φ(1)) (rel err < 1e-50), after fixing
  the compound-fraction reading (O1).
- T5: full sandwich φ(0)/(φ(0)+x) ≤ E_{α,m,l}(−x) ≤ φ(1)/(φ(1)+x) on the literal KS
  series for 5 parameter sets (incl. α=1 and a near-boundary a=0.01 case) over
  feasibility-filtered x-grids up to x=5000, with exact lgamma-profile adaptive
  precision (the alternating sum peaks at up to ~10^3000; naive summation is garbage —
  documented). Upper bound tight at 0 (slope 1/φ(1)); lower constant = Prop 4.3 constant.
- T6: killed moment formula — drift case exact; compound-Poisson+Exp-killing MC:
  E[I²] rel err 0.004 (se 0.003), E[I³] 0.009 (se 0.005).
- T7: φ(0) = Γ(1+α(l+1−m))/Γ(1+α(l−m)) exactly (Prop 4.3 constant).

## 5. Decisive prior-art finding (new, beyond the root's file)

A public project ("trureturing", The Omega Institute, GitHub) publishes a **complete
resolution of this exact conjecture**, machine-checked in Lean:

- Problem page: https://the-omega-institute.github.io/trureturing-mdbook/Problems/boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds.html
  — quotes the journal Conjecture 4 in linearized form 1/(1+[Γ(1+α(l−m))/Γ(1+α(l−m+1))]x)
  ≤ E ≤ 1/(1+[Γ(1+αl)/Γ(1+α(1+l))]x) — identical content to the root's target.
- Blueprint: .../Blueprint/D5/S3/Analytic/KilbasSaigo/Result.html — "Theorem 1.1 (The
  full parameter range) ... Machine-checked in Lean ... Resolves ... (proved)".
- Pinned certificate (fetched and confirmed to exist):
  https://github.com/the-omega-institute/trureturing/blob/e0dbe734370db2a0299eccbfcd168b88980cfad7/D5/S3/Analytic/KilbasSaigo/Result.lean
  containing `theorem result : claim` with `claim` the two-sided estimate; the page
  states axiom closure {propext, Classical.choice, Quot.sound} — the same allowance as
  this campaign. Commit e0dbe734370db2a0299eccbfcd168b88980cfad7.
- Their proof route is analytic (positivity of signed derivative series via the beta
  kernel K(r) = (α/Γ(1−α)) r^{a+α−1}(1−r)^{−1−α} — the *same* kernel as the root's Lévy
  density under r = e^{−t} — plus scaling equations, and ODEs at α=1). It also states
  both constants' optimality and the generic-sequence extension. Their page reports no
  earlier literature settlement (Koide figshare concerns boundary Conjecture 3.7;
  Karp–Kuznetsov 2403.05708 supplies representations; Beghin–Leonenko–Simon–Vaz
  2606.03661 cites without settling), i.e. this public result appears to be the first.

I did not audit their Lean development (out of scope and unnecessary for the
disposition): the *existence* of a public machine-checked resolution with the exact
statement, plus the root's own routine-corollary character, settles eligibility under
the campaign rules ("Never count a known theorem, public proof/refutation, routine
corollary..."). An open MathDB label (348998) is not novelty evidence and does not
rebut a public resolution found outside MathDB.

## 6. Objection ledger (strongest first)

- **O1 (resolved, review finding).** Conjecture layout ambiguity; naive linear reading
  is false. Resolution: section 2's four-way pinning. Root's file states the correct
  form; constants literal.
- **O2 (resolved).** Bernstein status of φ could have been merely logarithmic-CM or a
  reciprocal mix-up. Refuted: explicit positive Lévy density derived, integrability
  verified (analytic + T1/T2).
- **O3 (resolved).** Moment indexing (∏ from k=1 over the *killed* exponent, no q
  double-count). Refuted: independent derivation + Bertoin–Yor Thm 2(i) + Patie (1.2)
  + T6 numerics.
- **O4 (resolved).** Jensen direction / independence requirements. Refuted: needs
  J ⊥ I (Patie states pairwise independence) and E[J] = φ(1) (moment n=1); direction
  verified; also generic.
- **O5 (resolved).** Entire identification could fail for |x| ≥ κ via domination by
  e^{|x|ζ}. Refuted: the root's two-step argument (positive series first) is airtight.
- **O6 (decisive, unresolved-against).** Public machine-checked prior resolution
  exists (section 5) → ineligible regardless of routine-corollary judgment.
- **O7 (caution recorded).** The coefficient product does not telescope (b = αm ≠ α);
  only the term-by-term match is valid. Root's proof avoids telescoping.
- **O8 (limitation recorded).** The published Mathematics 9 (2021) 217 full body was
  not re-read in this review (MDPI 403 / EPFL 429 respected; no retries, no bypass).
  Relied on the cached arXiv v1 primary (the pinned target), the lane's prior
  search-rendered read of the published Conjecture 4, and the trureturing quotation of
  the journal statement. Residual risk that the journal conjecture differs materially
  from arXiv v1 Conjecture 4.5 is negligible but nonzero; disposition unchanged under
  either reading.
- **O9 (standing rule).** All numerics above are corroboration, not proof; the validity
  finding rests on the analytic derivations and published theorems.

## 7. Classification

- **Ordinary proof validity: VALID** (complete, correct, literal constants, full range
  incl. α=1 and x=0; recorded separately from eligibility per instructions).
- **Substantive eligibility: EXCLUDED** — (i) publicly resolved with a Lean certificate
  (known/public result); (ii) routine corollary of published general theorems
  (Bertoin–Yor Theorem 2 / Patie (1.2)–(1.3)) plus a two-line beta-integral
  computation; no new mechanism. **Discovery credit: 0. Total remains 32/60.**
- Root's recommendation NO DISCOVERY CREDIT: **CONFIRMED**, with the additional
  decisive prior-art evidence the root did not have.
- No Lean/paper investment is warranted for a routine corollary (concur with root).
- No acceptance, count, ledger, git, or external-posting actions performed.
