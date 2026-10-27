# Preliminary adversarial review — parent-cstar-smale proposed C*-Smale counterexample

Reviewer lane: `pi-cstar-smale-preliminary-review` (solo, no children, standard speed).
Date: 2026-10-27. Verdict up front: **MATH and SOURCE pass; NOVELTY/SUBSTANTIVE fails on
decisive prior art — the exact source question is already publicly resolved (negatively)
via the scalar instance A = C. Do not count. Stop per instruction.**

## 1. Source review (PASS)

Primary source obtained and read in full (text extraction, conjecture visually
cross-checked against arXiv v1):

- K. Mahesh Krishna, *C\*-algebraic Smale Mean Value Conjecture and Dubinin–Sugawa Dual
  Mean Value Conjecture*, **Vestnik KRAUNC. Fiz.-Mat. Nauki, 2026, 54(2), 38–47**,
  DOI 10.26117/2079-6641-2026-54-2-38-47, EDN NMXQAM, first online 2026-09-14,
  MSC 46L05, 30C10. Publisher PDF saved at `sources/krishna-vestnik-54-2.pdf`
  (SHA-256 `91ce25a2...9a50df8`), extracted text `krishna-vestnik-54-2.txt`.
- arXiv:2206.08154v1 (2022-06-16) is the only arXiv version; the journal body matches it
  with renumbered statements.

Exact published **Conjecture 2.1 (weak CSMALE)**, journal p. 43:

> Let A be a commutative C\*-algebra. Let P(z) := (z−a₁)···(z−aₙ) be a polynomial of
> degree n ≥ 2 over A, a₁,…,aₙ ∈ A. If z ∈ A is not a critical point of P (i.e.,
> P′(z) ≠ 0), then there exists a critical point w ∈ A of P such that
> ‖P(z)−P(w)‖/‖z−w‖ ≤ 1·‖P′(z)‖  **or**  ≤ ((n−1)/n)·‖P′(z)‖ = ((deg P−1)/deg P)·‖P′(z)‖.

Conventions confirmed in the journal body: the derivative is the ordered-deletion sum
Σⱼ ∏_{k≠j}(z−a_k), explicitly "a derivative strictly in the algebraic sense", not
Fréchet/Gâteaux; "critical point" means P′(w) = 0. The strong form is Conjecture 2.2
(p. 43), with source Proposition 2.1: 2.2 ⇒ 2.1. Theorem 2.1 verifies degree 2 only.
HIGHERMEAN is journal Conjecture 2.3 (p. 44); dynamics is 2.4; DUALSMALE is 3.1/3.2 —
all distinct from this target.

**MathDB**: no record found for CSMALE (site searches over mathdb.com; the registry
preregistration #14982 also records "No MathDB page was located"). Related MathDB
records exist for the sibling conjectures (353908/353909 Sendov, 351633 Novak,
355008/355009 polynomial moments) but none for 2206.08154 Conjecture 2.1. OpenAlex
confirms the published record W4283072905 with the DOI above; its cited-by list
(4 works) contains only Krishna's own Bieberbach/Corona preprints.

## 2. Mathematical review (PASS — independently re-derived)

Independent derivation (not copied from parent), fully checked by my own exact checker
`checks/verify_parent_smale_counterexample.py` (all decisions in exact Q(√17) integer
arithmetic; no floating-point decisions; output in `checks/verify_run_output.txt`):

- A = C([−1,1], C): commutative unital. y(t)=t, q(t)=√(t²+1/16) ∈ A with
  q² − t² = 1/16, so q ≥ 1/4 > 0 and q > |t| everywhere.
- P(w) = w³ − 3q²w = w(w−√3·q)(w+√3·q): genuine fully split degree-3 source polynomial
  with roots 0, ±√3·q ∈ A.
- Source deletion derivative P′(w) = 3w² − 3q² = 3(w−q)(w+q): fully split. At z = y:
  P′(y) = 3t² − 3(t²+1/16) = −(3/16)·1, a constant of norm 3/16, invertible; z is
  genuinely noncritical (stronger than needed).
- **Zero-divisor-safe critical classification**: P′(w)=0 ⟺ (w−q)(w+q)=0 in A. Since
  q(t) ≥ 1/4 > 0, the pointwise factors never vanish simultaneously; {t : w(t)=q(t)}
  and {t : w(t)=−q(t)} are disjoint closed sets covering the connected interval, so
  **every** critical element is globally +q or globally −q. No pointwise-mixing or
  zero-divisor loophole. This is the correct C(X) argument and avoids any global
  integral-domain inference.
- Failure quantification: P(y) = −2t³ − (3/16)t; P(±q) = ∓2q³. At t=−1 (branch +q) and
  t=+1 (branch −q): |P(y) − P(w)| = (70 + 17√17)/32 ≈ 4.3779 > 4 (exact: 4913 > 3364).
  Both denominators y∓q are invertible (q−|t| = (1/16)/(q+|t|) > 0), with exact norms
  (√17+4)/4 ≈ 2.031 ≤ 9/4 (parent's conservative bound: 1 + √17/4 ≤ 9/4, exact since
  17 < 25). The conjecture would force ‖P(y)−P(w)‖ ≤ (3/16)·9/4 = 27/64 ≈ 0.4219 —
  contradiction. Exact ratio ≥ (70+17√17)/32 ÷ ((√17+4)/4) ≈ 2.156 ≫ 3/16.
- Both disjuncts of Conjecture 2.1 fail for every critical element (2/3 < 1 a fortiori);
  Conjecture 2.2 fails by its own Proposition 2.1. No formal endpoint exists and none is
  claimed; my checker is a computational corroboration with exact core, not Lean.

Objections found: **none mathematical.** Minor presentational notes for the parent:
(a) PROOF.md says "||q|| ≤ 5/4" — true but loose (exact √17/4); (b) the parent line
"P(q)=−2q³, with q=√17/4>1 ... >35/16+2>4" is correct but the cleaner exact constant is
(70+17√17)/32; (c) the parent's "Scalar Smale is untouched" framing is now factually
outdated — see §3.

## 3. NOVELTY / SUBSTANTIVE: DECISIVE PRIOR ART — STOP

The source conjecture is **universal over all commutative C\*-algebras**. The scalar
field C is itself a commutative unital C\*-algebra (spectrum a point — connected), and
over C the deletion derivative is the ordinary derivative. So **any** scalar
counterexample to constant-1 Smale is literally a counterexample to published
Conjecture 2.1, in all its forms (constant 1; (n−1)/n; strong 2.2). Such counterexamples
were public **before this campaign (2026-10-26)**:

1. **Adamczewski / GPT-6 Astra, Sep 2026** — machine-checked Lean 4/Mathlib disproof of
   the constant-1 Smale statement (Google DeepMind Formal Conjectures
   `MeanValueProblem.mean_value_problem`, negation proved, Comparator-checked, only
   propext/Classical.choice/Quot.sound; witness: large unspecified degree, normalized
   p(0)=0, p′(0)=1, |p(c)/c| > 1 at every critical point). Repo:
   github.com/tadamcz/mean-value-problem (README archived in my `sources/`). MathWorld
   records it as a released proposed counterexample with independent mathematical review
   *not yet reported* as of 2026-09-07.
2. **A. Jatar, T.-W. Ng, arXiv:2610.21472** (v1 2026-10-15, v2 2026-10-21 — both
   pre-campaign), *Smale's mean value constant and admissible univalent Blaschke
   pairs*: proves ℳ = ℬ and **ℳ ≥ √(8081/6656) ≈ 1.1018 > 1**, explicitly "a new
   disproof of Smale's mean value conjecture" (constant-1 form), with polynomials of
   arbitrarily large degree having S(P) > 1.1018. Tuen-Wai Ng (HKU) is a leading expert
   on exactly this constant (Beardon–Minda–Ng line). The paper itself credits and
   improves the Adamczewski M > 1 result. Abstract and body read by me; saved abstract
   HTML in `sources/`.

Consequence: **the exact source question of parent-cstar-smale — "does published
Conjecture 2.1 hold?" — is already answered NO in public literature.** The parent's
counterexample proves the same proposition (¬Conjecture 2.1) with a different witness.
Under the ledger counting standard ("a substantive new mathematical result addressing an
exact unresolved source question; exclude already published/posted proofs,
re-formalizations, ... equivalent corollaries") this **cannot be counted**, regardless of
the witness's independent interest. The refinements the witness offers — degree 3,
non-scalar connected algebra C([−1,1]), fully split polynomial and derivative — refine
*where* failure occurs but do not resolve any unresolved source question; no source text
or MathDB record poses "does 2.1 fail in connected C\*-algebras / at degree 3 / for split
data?" as an open problem. The registry note in
`pi-euler-turan-final-review/fresh/trureturing/Problems/krishna-2022-cstar-high-order-smale-mean-value.md`
listing "the paper's CSMALE conjecture ... open" predates these two works and must be
updated by the parent; its HIGHERMEAN/DUALSMALE refutations are unaffected (different
conjectures, and I did not rediscover or credit them).

## 4. Distinctness vs accepted C\*-Sendov (record 16) — would have been distinct, moot

Had the source question been unresolved, this would have been a **distinct substantive
outcome** from accepted `candidates/cstar-sendov`: different source paper and conjecture
(Vestnik 54(1) 56–63 Conjectures 3/4 / MathDB 353909 vs Vestnik 54(2) 38–47 Conjecture
2.1), different inequality (uniform-small derivative mean-value ratio vs critical-root
proximity/convex-weight hypotheses), different algebra (C([0,1]) with three
constant-modulus roots vs C([−1,1]) with scalar-function roots), different failure
mechanism (value-gap vs derivative-norm). The shared *tool* — connectedness forcing a
global branch of a two-branch derivative — is classical and receives no credit in
either; no artificial splitting or helper credit arises. Neither result implies the
other. But the scalar prior art above is decisive against the candidate itself, so this
comparison is recorded for the parent's ledger notes only.

## 5. Candid access limits

- Jatar–Ng is a three-week-old preprint; MathWorld notes "their quantitative disproof
  has not been independently verified here". I did not re-verify their proofs; the stop
  relies on the works being public, on-point, and expert-authored, not on my own check
  of their arguments. If both works were somehow withdrawn and discredited, the
  candidate would need full re-review.
- The Adamczewski proof is machine-generated; no independent human mathematical review
  is reported. Its Comparator check binds only the Formal Conjectures statement.
- No MathDB record for Conjecture 2.1 was found; absence from MathDB is not proof of
  absence of a record (login-walled features not inspected).
- Semantic Scholar API rate-limited (429); citation coverage relies on OpenAlex (4
  citing works, all Krishna's own), DDG/parallel searches and the registry
  preregistration. Subscription indexes and non-English literature beyond the Russian
  journal pages uninspectable. This does not affect the verdict, which rests on found
  (not missing) prior art.
- I did not verify the Adamczewski Lean build locally (no Lean investment per brief).

## 6. Provenance

- Publisher PDF `sources/krishna-vestnik-54-2.pdf`, SHA-256
  `91ce25a22c800a36e979e3ec29581b46ff1b9370e3c08c06f868578f49a50df8`, fetched from
  https://krasec.ru/wp-content/uploads/2026/09/Krishna.pdf on 2026-10-27.
- Parent source copies: `lanes/parent-cstar-smale/sources/smale.{pdf,txt}` (arXiv v1).
- Jatar–Ng abstract page `sources/jatar-ng-2610.21472-abs.html`, SHA-256
  `fc7bd1d3...f9c5e6`; body read via arXiv HTML v2. Adamczewski README
  `sources/adamczewski-mean-value-problem-README.md`, SHA-256
  `9282e220...f9c5e6` (full hash in provenance.json).
- Own checker: `checks/verify_parent_smale_counterexample.py`, SHA-256
  `73a3fcaf74c028bbff9f663306519c73cc56940c8b0a376fdaf1874fa1ea7418`; run log
  `checks/verify_run_output.txt`; exit 0, "ALL CHECKS PASS".
- MathDB check: site-restricted searches (mathdb.com) on 2026-10-27 — no CSMALE record.
- OpenAlex: work W4283072905 (the DOI record); cited-by: 4, all Krishna Bieberbach/
  Corona preprints (none addresses Conjecture 2.1).

## 7. Verdict

- SOURCE: PASS (exact published Conjecture 2.1 obtained, pp. 43, 38–47, DOI/EDN
  recorded).
- MATH: PASS (independent exact re-derivation; no loophole; counterexample valid).
- NOVELTY/SUBSTANTIVE: **FAIL — decisive prior art** (scalar refutations of the
  constant-1 Smale conjecture, which subsume Conjecture 2.1 via A = C, posted
  2026-09 / 2026-10, pre-campaign).
- Recommendation to parent: **do not accept, do not count**; update the registry note
  that CSMALE is open; optionally retain the verified witness as an uncounted
  strengthening record with the scalar prior art cited. No formal PASS/claim is made
  anywhere above; no formal endpoint exists for this candidate.
