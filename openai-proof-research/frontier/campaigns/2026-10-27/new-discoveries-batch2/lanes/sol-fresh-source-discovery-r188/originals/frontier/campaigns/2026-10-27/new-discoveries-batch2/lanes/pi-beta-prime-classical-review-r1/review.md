# Independent classical-subsumption review: root-beta-prime-addition-r19

Reviewer: pi GLM-5.3-Flash (thinking=high), solo adversarial classical-subsumption
review. Date: 2026-10-28. Target: `lanes/root-beta-prime-addition-r19` @ commit
89ad601d58, `review-freeze.json` binding 19 files. This lane is the only file
written by this review. No shared, ledger, candidate, or other-lane writes; no
git actions; no child agents; no external messages.

## Verdict

**CONFIRM EXCLUSION as a routine classical corollary; credit 0 stands; no Lean
or paper investment.** Root's recommendation is upheld. The Ferreira–Simon
Conjecture 1 resolution is fully subsumed, by routine substitution, by a
concrete published-classical product formula for modified Bessel functions
(Durand 1978, eq. (5.2)–(5.3) at m=0), whose mathematical content this review
verified independently and exactly. One provenance caveat is recorded (G5): the
reviewer could not independently view the printed journal display through any
lawful automated route; the exclusion does not rest on the root's transcription
alone, because the transcribed formula was independently verified to be exactly
true, and the authors' own 2026 erratum leaves the relevant section untouched.

## G1. Freeze integrity — PASS

All 19 `review-freeze.json` SHA-256 values were recomputed **before** any
review action and matched exactly (`/tmp/betaprime-before-hashes.txt`; working
copy made at `/tmp/betaprime-review-copy/`). Re-verified unchanged at the end
of this review (see provenance.json `freeze_after`). Frozen originals were
never modified; all review work used the copy and this lane.

## G2. Primary-source fidelity of the target statement — PASS

- Published Conjecture 1 was read from the lane's cached AMS full-text HTML
  (`published-conjecture1-extract.txt`) and independently from the arXiv v2
  text (`ferreira-simon-v2.txt`): for every a>0, b∈(0,1/2),
  B'(a,b)+B'(a,b) =d B'(2a,b)·(1+√(B_{a,1/2}/B_{b,1/2-b})), variables on a
  side independent. The cached extract and arXiv v2 agree verbatim.
- Theorem A (a=1/2 all b via limit), Theorem B (a=1-b or a=1/2), and
  Proposition 5 are the known partial cases; the conjecture asks for the
  remaining (a,b) rectangle. Quantifiers and the independence convention match
  the root's PROOF.md statement.

## G3. Independent re-derivation of the ordinary proof — PASS

Every load-bearing step of PROOF.md was re-derived or independently verified;
no gap found.

1. **Conditional identity (2).** u/G₁+(1-u)/G₂ =d (1+2√(u(1-u))/√W)/G₃,
   W~Beta(b,1/2-b), verified four independent ways: (a) exact-closure of the
   Bessel bridge (G4); (b) reciprocal-moment identity at 55 dps on the root's
   45-point grid (checks.json) **and** on a fresh harder grid (b∈{0.02,0.3,0.49},
   u∈{0.01,0.5}, m∈{1,5,30}) to worst rel. error 4.0e-40
   (`_mp_checks.json`); (c) Monte Carlo on the LT form with corrected Beta
   sampling (rel. diff 1.1e-3–4.2e-3, within MC error; `_mc_endtoend.json`);
   (d) the phi-form bridge integral (E) to ≤3.0e-36 on
   b∈{0.1,...,0.499} (`_mp_checks.json`, `_smooth_checks.json`).
   Determinacy: Q ≤ G_{2b}/(1+c) and R ≤ G_b/(1+c) both hold — the reviewer
   re-derived the bound (1+c)V(1-V) ≤ u+(1-2u)V as a zero-discriminant perfect
   square (1+2s)V²−(2u+2s)V+u = (1+2s)(V−(u+s)/(1+2s))², s=√(u(1-u))), so the
   local-mgf uniqueness argument is sound.
2. **Series side.** Reviewer re-derived E Q^m = A_m·₂F₁(m/2,(m+1)/2;
   b+m+1/2; 1-c²) with A_m=(2b)_m(b)_m/(2^m(b+1/2)_m) from scratch via
   r=2V−1 and even-term beta moments; matches PROOF.md §2 (an initial slip in
   the reviewer's own quick computation, dropping the (2b)_m prefactor, was
   found and corrected; the root's A_m is right).
3. **ODE side.** The pointwise identity
   c(1-c²)g_cc+[1-2b-2(m+1)c²]g_c−m(m+1)c·g = m·∂_t H was verified at 50-digit
   precision at 50 random (t,c,b,m) points (worst residual 5.6e-51 relative to
   the largest term; `_mp_part.py` pipeline). Endpoint vanishing of H needs
   2b+m>0 and 1/2−b>0 — both hold — so the IBP gives (5). The chain-rule
   transform of (5) to the Gauss equation (8) was re-verified symbolically
   (residual 0), and the Taylor recurrence (9) was re-derived symbolically
   coefficient-by-coefficient for n=1..4. Analytic uniqueness at z=0 is correct:
   Gauss exponents are 0 and 1−C=1/2−b−m<0, so the analytic solution is fixed
   by y(0) alone; no nonanalytic uniqueness claim is used. Since c∈(0,1] always
   (c=2√(u(1-u))), z=1−c²∈[0,1) lies inside the ₂F₁ convergence disk — the
   proof needs no continuation beyond it.
4. **Boundary value.** I_m(1)=2^{-2b-m}B(1/2−b,2b+m) verified to ≤1.3e-36
   rel. error for (b,m)∈{(0.4,1),(0.49,2),(0.25,1),(0.1,3),(0.45,5)}
   (`_im1_fixed.json`), and the reviewer re-checked the duplication-closure
   2(b)_m I_m(1)/B(b,1/2−b) = A_m symbolically (ratio reduces to
   2^{1-2b}√πΓ(2b)/Γ(b+1/2)=1).
5. **Splitting.** G=A₁+A₂~Gamma(2a) independent of U=A₁/G~Beta(a,a) is
   standard beta–gamma algebra; 4U(1−U)~Beta(a,1/2) verified by two-branch
   density transform to ≤8.1e-41 and by the mean (`_mp_checks.json`); the
   independence bookkeeping in §4 is correct, and the resulting identity is
   literally Conjecture 1 with the source's independence convention.
6. **No Lean endpoint is claimed**, and none is needed for an exclusion; no
   formal certificate was checked or required.

## G4. The classical bridge — mathematically CONFIRMED

The transcribed Durand display (D), K_q(x)K_q(y)/(xy)^q =
[2^{q-1}Γ(q)/Γ(2q)]∫₀^∞ w^{-q}K_q(w)sinh^{2q}φ dφ, w=√(x²+y²+2xy cosh φ),
was tested **directly and exactly** (mpmath 35–40 dps, endpoint-singularities
smoothed by φ=s^{1/(1-2q)}-type maps):

- q=0.3, 1.7: rel. err ≤ 2.4e-41 (confirms the shape in its primary range);
- q=−0.1: 2.6e-36; q=−0.25: 4.3e-23; q=−0.45: ≤1.3e-36; q=−0.49: ≤1.8e-36;
  q=−0.499: ≤1.2e-36 (`_mp_checks.json`, `_smooth_checks.json`). The negative-q
  range — the one the conjecture needs — is covered, and the constant
  2^{q-1}Γ(q)/Γ(2q) plus both powers are pinned exactly (any transcription
  error in them would give O(1) disagreement).
- Exact-closure cross-check: the reviewer independently reduced the
  transcribed (D) at q=−b to the normalized bridge (E) and confirmed the
  constant closes exactly: 2^{-b-1}Γ(−b)/Γ(−2b) = 2^b√π/Γ(1/2−b) (duplication),
  and with x=2√(λu), y=2√(λ(1−u)), w=2√λ√(1+c coshφ) the coefficient of the
  (1+c coshφ)^{b/2}K_b(w) integral becomes exactly 4√π/(Γ(b)²Γ(1/2−b)) =
  4/(B(b,1/2−b)Γ(b)), i.e. precisely the [2/B(b,1/2−b)]∫f_b(λ(1+c coshφ))·
  sinh^{-2b}φ dφ of (E) — independently re-derived before running any numerics.
- With W=sech²φ the measure [2/B(b,1/2−b)]sinh^{-2b}φ dφ is exactly the
  Beta(b,1/2−b) law (re-derived; verified numerically), and f_b is exactly the
  Laplace transform of 1/Gamma(b) (re-derived via Euler integrals and
  MC-checked). Uniqueness of Laplace transforms then gives (2) verbatim.
- The end-to-end literal conjecture was then falsification-tested at the
  Laplace-transform level by Monte Carlo on five (a,b,λ) points spanning
  a∈{0.4,...,2}, b∈{0.1,...,0.45}: agreement 0.01%–0.8% (`_mc_endtoend.json`),
  i.e. the literal Conjecture 1 identity holds as the bridge says.

**Conclusion:** the conditional identity and the full conjecture are routine
analytic consequences of the classical product formula; no unsolved analytic
step remains after substitution. The root's own ODE proof is a second proof of
the same transform relation, not a route around subsumption.

## G5. Durand 1978 provenance — confirmed with one recorded caveat

Verified by this review:

- The paper exists exactly as cited: L. Durand, *Product formulas and
  Nicholson-type integrals for Jacobi functions. I: Summary of results*,
  SIAM J. Math. Anal. 9(1) (1978) 76–86, DOI 10.1137/0509007; Math. Rev. 57,
  862 (1979); MaRDI item Q4150001; 50 indexed citations; listed as
  publication #50 on the author's official Wisconsin publication list
  (fetched and archived in this review).
- **The 2026 erratum was retrieved and read in full** (Cohl–Durand, SIAM J.
  Math. Anal. 58(1):698–699, DOI 10.1137/25M1794759, published 2026-02-18;
  full text via MaRDI IPFS). It corrects: the kernel form (2.10) (wrong lower
  bound t₁+t₂ and a spurious 2^{α+1/2}-type factor), typographical errors in
  the trigonometric Nicholson formula (2.13), and Laguerre items (4.10),
  (4.12). **The confluent §5 product formulas, including (5.2)–(5.3), are not
  among the corrected items**, so they stand as published per the authors'
  own erratum. This supports the root's related claim about 2508.08085.
- DLMF §10.32/§10.43 contain the equal-argument product formula
  (10.32.17: K_μ(z)K_ν(z)=2∫K_{μ±ν}(2z cosh t)cosh((μ∓ν)t)dt) but not the
  general x,y weighted form — consistent with Durand being the concrete named
  source, and with the root's statement that DLMF 10.32.17–18 do not present
  (D) in this form.

Caveat (lawful-access limit): the reviewer's shell/fetch retrievals of the
ResearchGate author-uploaded PDF, the RG publication page, epubs.siam.org, and
a Wayback copy all returned 403/404; no author-hosted copy of the 1978 paper
exists on the author's site. The printed p.84 display therefore rests on the
root's public-web-reader transcription, which this review could not re-view
page-by-page but did pin mathematically to 1e-36 (G4). Given the exactness of
that verification, the erratum scope, and the paper's documented content, this
caveat does not overturn the exclusion; it is recorded in provenance.json.

## G6. Non-credit and scope checks — PASS

- **2610.06073v1 Theorem 1** (lane-cached HTML read): assumes shaping
  parameters α_k = n_k+1/2 with n_k∈ℕ — half-integer shapes only. It does not
  cover 0<b<1/2 and is not the exclusion. No MathDB record was identified for
  Conjecture 1; none is invented or mutated.
- **First-campaign Mills credit** (accepted #18, MathDB 351688, Mills-ratio
  complete-monotonicity fortieth-derivative obstruction) is a different
  conjecture of the same paper and is not recounted here. Total remains 30/60
  first-campaign + 0/30 additional; this review counts and accepts nothing.
- No polling of other lanes; no reads of Mittag/Kilbas final lanes.

## Strongest falsifiers nominated (all tested, all failed to break the result)

1. End-to-end literal Conjecture 1 LT identity (MC, five parameter points):
   confirmed to MC error. A structural error in the bridge or its independence
   bookkeeping would appear here at O(1); it does not.
2. Exact Durand constant 2^{q-1}Γ(q)/Γ(2q) at q→−1/2⁻ (where Γ(q),Γ(2q)<0 and
   sinh^{2q} is near-singular): verified to ≤1.8e-36; a wrong power of 2
   (e.g. the 2^q vs 2^{q-1} footnote issue) or swapped w-power would fail here.
3. Independence in §4 (G independent of U; fresh W,G_b independent of (G,U)):
   re-derived; a hidden dependence would break the MC check asymmetrically;
   it does not.
4. Determinacy bound Q ≤ G_{2b}/(1+c): re-derived as an exact maximum; the
   claimed inequality is tight, not merely sufficient, so the mgf argument is
   valid.

## Reviewer artifacts (this lane)

- `_mp_part.py`, `_mp_checks.json` — Durand direct test, bridge (E),
  fresh-grid reciprocal moments, 4U(1−U) check (mpmath, ≤512 MiB, single
  process; peak RSS 19.6 MiB).
- `_smooth_checks.py`, `_smooth_checks.json`, `_im1_fixed.json` —
  smoothed-endpoint re-tests near the singular boundaries.
- `_mc_endtoend.py`, `_mc_endtoend.json` — corrected MC falsifier for the
  conditional identity and the literal conjecture.
- Working notes and this file. A superseded draft with a scipy nested-quad
  attempt and one buggy Beta-sampling draft were removed from the lane after
  the corrected mpmath/MC pipeline replaced them; the correction is documented
  in `_mc_endtoend.py`'s docstring.

## Disposition

Root's recommended EXCLUSION is **confirmed**: routine classical corollary of
Durand 1978 (5.2)–(5.3) at m=0 via the recorded parameter bridge; credit 0;
accepted total unchanged at 32/60 (30 first campaign + 2 additional). No Lean,
paper, formal, or count actions. The two documents in the target lane are
sound as written; the only correction this review would suggest to root (no
lane write performed) is that the provenance note could additionally cite the
2026 erratum's full corrected-item list, which this review retrieved
independently.
