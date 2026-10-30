# Preliminary adversarial review — parent-kadar-yu PROOF.md (commit 6c62aeb10e)

Reviewer lane: `NEW/lanes/pi-kadar-yu-preliminary-review` (solo, no children).
Date: 2026-10-26. Subject: prospective complete hand resolution of MathDB 372352 /
Morris–Martin arXiv:2512.24535v1, Conjecture 4.5.1 (p35), credit 0, tally 14/30
untouched. **No formal PASS is claimed.** Verdict: **conditional PASS** on the
mathematical and source gates after independent re-derivation and machine
verification on source-printed data; eligibility supported by bounded search;
formal bridge is viable but not yet an endpoint (see Gate 5).

---

## Gate 1 — SOURCE: PASS

All source claims in PROOF.md §1 were checked against the actual manuscript
(`parent-kadar-yu/sources/2512.24535.pdf`, SHA-256
`2d6f180b…ed6bf5c86` — re-hashed and matching provenance):

| Parent claim | Source location | Status |
|---|---|---|
| Gram matrix = αI + real symmetric constant (3.2.3) | item (3.13), Eq (3.2.3) | verified verbatim |
| Tail chain: diagonal α, off-diagonal 1; no cross-tail coupling (3.2.4) | Eq (3.2.4); basis B(l,n) in (3.2.1) (tail = adjacent pairs u_{j,j+1}, j ≥ l+4) | verified; Figure 2 and (3.2.5) confirm incl. d=2 |
| Mixed-length pencil Γ_{l,n}, n_k ≥ l+4 | item (3.17) | verified |
| Extension appends one row/col: 1 at old endpoint e, diagonal α | Eq (3.2.17) and block (3.2.6) | verified; endpoint e = u_{l+3,l+4}b_k |
| det Γ_{l,n} = C^(λ) ∏_k P_{n_k}, C monic, independent of n | Proposition 3.25 (via 3.18, Lemma 3.24, Thm 3.19) | verified |
| P reduced ⇒ consecutive P coprime; ramping = polynomial + reduced + monic + deg +1 | (3.2), (3.7) | verified — reducedness is part of the ramping property, so the parent's "only consecutive coprimality used" is legitimate |
| Recurrence is **minus**: (3.2.7), (3.2.9) print α·det − det; (3.1.1) prints **plus** | §3.1, §3.2 | typo confirmed; classical convention (P^U_2=x, P^U_3=x²−1, P^U_{−n}=−P^U_n in (3.1.3)) is only consistent with **minus**. Parent correctly uses minus and claims no credit. **Warning: anyone formalizing from (3.1.1) as printed would derive a wrong theory; the sign must be pinned to (3.2.7)/(3.2.9).** |
| Conjecture: squarefree for every k ≥ −1; eventually constant #roots outside [−2,2]; ∪_{k≥0} interior roots dense in [−2,2] | Conjecture 4.5.1, p35 (read in text and in `kadar-source-35.png` render) | matches parent's rendering exactly; "Fix l" is effectively l ≥ −1 since λ ⊢ l+2 |

MathDB live record (`parent-kadar-yu/sources/372352-live.json`): status open,
lean count 0, "no resolution reported (as of December 2025)". The record's claim
that 1601.04382 and 1510.01758 "state this conjecture" is **wrong** — both
abstracts fetched fresh: 1601.04382 = Tran, *Connections between discriminants
and the root distribution of polynomials with rational generating function*;
1510.01758 = Kelley–Owen, *Estimating the Number Of Roots of Trinomials over
Finite Fields*. Neither mentions Kadar–Yu. The parent's companion-grouping
warning is confirmed.

## Gate 2 — MATH: PASS (independently re-derived and machine-checked)

I re-derived every step of PROOF.md §2–§5 myself and additionally built two
exact symbolic verification scripts using **only data printed in the source**
(evidence/):

* `verify_identification.py` — Eq (3.2.5): the printed 15×15 Gram matrix of
  ∆^{(11,λ)} for J_{1,13} (λ=(3), ϵ=+1; λ=(1³), ϵ=−1), head rows/cols 1–7,
  8-vertex unit tail. Published inputs: C^(3)=(α−2)²α², C^(1³)=(α−2)²(α+2)³,
  P₅,P₆ from §3.3, P₄ from Remark 3.33.
* `verify_d2_figure2.py` — Figure 2 (rendered at 300 dpi and transcribed;
  symmetric-transcription assertion enforced): printed 20×20 Γ(∆⁸_{(6,(2,1))}),
  the equal tuple (8,8) for l=1, λ=(2,1), d=2, **including cross-head
  couplings** (√3/2, −1/2 entries). Published: C^(2,1)=(α−2)³α(α+2)(α+4),
  P₅=α⁴−7α²+3, P₆=α(α−1)(α+1)(α²−7).

Results (all exact, sympy 1.14; outputs in evidence/):

1. **gcd step (§3)**: monic gcd(det Γ_(5), det Γ_(6)) equals the published C^(λ)
   for both d=1 cases; for d=2 the gcd of det Γ_(5,5) and det Γ_(5,6) equals
   **F = C·P_N^{d−1} = C·P₅** exactly as §3 predicts (multiplicities retained;
   no coprimality of F and P_N needed — confirmed, F·P_N and F·P_{N+1} share P_N).
2. **Identification**: the quotients reproduce the published reduced series
   exactly: P̂₅=(α+1)(α²+3α−6), P̂₆=α(α³+4α²−4α−10) for (3);
   α²−2α−3, α³−2α²−4α+2 for (1³); and det Γ_(5,5)=C·P₅², det Γ_(5,6)=C·P₅P₆
   for (2,1). The polynomials are recovered **from matrix determinants alone**,
   i.e. the parent's §3 derivation is validated against the source's own
   independent route (initial conditions + Prop 3.25).
3. **Compression (§2)**: exact Krylov compression of A = −(const part) at the
   tail-attach coordinate e gives an **irreducible tridiagonal** J with
   **r = dim K = deg P_N** (3, 2, 4 respectively — a nontrivial consistency
   check the parent's argument implies). Direct charpolys of J_s (J + s-path at
   e) satisfy **q_s = P_{5+s} for all tested s** (s=0..8 for both d=1 cases,
   s=0..3 for d=2), and **q_{−1} = charpoly(J with e deleted) = P_{N−1} =
   αP_N − P_{N+1}** — the k=−1 boundary works exactly as claimed (matches
   Remark 3.33: α(α+4) for (3); α−2 for (1³); α(α²−4) for (2,1)).
   Successive q's verified disjoint and strictly interlaced.
4. **End-to-end on the largest printed matrices**: det Γ_(13) (15×15) =
   C·P₁₃ and det Γ_(8,8) (full printed 20×20) = C·P₈², both exact.
5. **Conjecture clauses on instances**: P₄..P₁₃ squarefree in all three
   instances; exterior root counts (|root|>2) monotone nondecreasing and ≤ r:
   [1,1,…] for (3), [0,1,1,…] for (1³), [0,2,2,2,2] for (2,1). Note P₄^{(2,1)}
   has roots exactly ±2 — correctly excluded by the strict-inequality count.
6. **§4 eventual stability**: re-derived. Strict interlacing ⇒ h_s^±
   nondecreasing (top-h roots of q_s above 2 force h roots of q_{s+1} above 2
   via λ_j < μ_j); T_s (the appended path) is a principal submatrix of J_s of
   codimension r with all eigenvalues 2cos(jπ/(s+1)) ∈ (−2,2), so Cauchy gives
   μ_i ≤ ν_i < 2 for i ≤ s, hence h_s^+ ≤ r (same for −2). Bounded monotone
   integer sequences stabilize. Correct. (The sharper Cauchy bound is r, not
   2r — the parent's looser bound is harmless.)
7. **§5 density**: re-derived. For nonempty open I ⊂ (−2,2), #{j :
   2cos(jπ/(s+1)) ∈ I} → ∞, and Cauchy bounds the count difference for the
   codim-r embedding by a constant, so J_s (hence P_{N+s}) has a root in I for
   all large s. Correct.

**Objections found (none fatal):**

* **O1 (must fix in writeup/formalization).** §5 asserts "its closure also
  contains both endpoints" without argument. It is true and one line: for any
  ε>0, #(T_s roots in (2−ε,2)) → ∞ while the J_s/T_s count difference is ≤ 2r,
  so P_{N+s} has a root in (2−ε,2) for all large s; likewise near −2. Spelling
  this out is required for the literal "dense in [−2,2]" endpoint.
* **O2 (cosmetic).** §2 claims Lanczos subdiagonals are "strictly positive";
  positivity is achievable by sign choices but only **nonzero** (irreducibility)
  is used anywhere. Irreducibility follows because a vanishing β_i would close
  the Krylov space early, contradicting dim K = r. Clean this up for Lean.
* **O3 (check).** The identity gcd(F·P_N, F·P_{N+1}) = F (multiplicities
  included) is the gcd-domain identity gcd(ab,ac)=a·gcd(b,c) with
  gcd(P_N,P_{N+1})=1; valid; verified symbolically.
* **O4 (scope).** The argument is uniform in λ ⊢ l+2, l ≥ −1 (no fixed
  partition, row/column/hook, or bounded-degree case), and d=1 and d=2 (the
  first case with cross-head couplings) are both machine-verified. No special
 -case shortcut is being passed off as the general theorem.

## Gate 3 — NOVELTY (serious, bounded): conditional PASS — no prior resolution found

Bounded search performed (access limits below):

* **arXiv abs 2512.24535**: v1 only, submitted 31 Dec 2025 — matches parent's
  provenance; no v2.
* **Citations**: Semantic Scholar snippet in search results reports **0
  citations** (direct API call rate-limited, HTTP 429 — see limits).
* **Author follow-ups**: Benjamin Morris's homepage (benjimorris.github.io)
  lists only the Dec 2025 KY paper (with Paul Martin) and June 2025
  Temperley–Lieb categories on non-orientable surfaces (Ibarra,
  Montoya-Vega). No KY root-distribution follow-up.
* **Original KY literature**: Kádár–Martin–Yu, *On geometrically defined
  extensions of the TL category in the Brauer category* (arXiv:1401.1774,
  Math. Z. 293 (2019) 1247–1276): algebra structure and generic semisimplicity;
  no Gram-determinant root-distribution results; the P^{(λ)}_n series and the
  conjecture first appear in the 2025 paper. Kádár–Martin 2002.05478 likewise
  does not contain it.
* **Methodologically adjacent prior art**: Christiana–Ibarra–Montoya-Vega,
  *Chebyshev polynomials and Gram determinants from the Möbius band*
  (arXiv:2504.16439) — Gram determinants of a diagrammatic algebra expressed
  via Chebyshev polynomials, but a different algebra ((Mb)₁/Mb), closed-form
  conjectures only, no cyclic-compression identification and no density/
  exterior-count theorem; does not touch KY. Chen–Przytycki type-B TL Gram
  determinant (0802.1083) is a product-formula setting with classical roots.
  Neither subsumes the parent's contribution.
* **Source itself**: contains no Jacobi/interlacing/orthogonal-polynomial
  machinery (grep: "tridiagonal" appears only to describe the tail; no
  "Jacobi", "interlacing", "Lanczos", "dense" outside the conjecture). §4
  proves real-rootedness (Cor. 4.0.1) and MVT interlacing counts **only for
  specific families** ((l+2), (1^{l+2}), (l+1,1), (l+1,1)^T, (2,2)); it does
  not prove squarefreeness, exterior-count stability, or density for general
  λ. The conjecture is genuinely open in the source and not "immediate" from
  it.
* **Mechanism novelty**: the head+path → compressed-Jacobi identification is an
  instance of classical machinery (Lanczos/Krylov compression, orthogonal
  polynomials of a spectral measure, finite-section/free-lead spectral theory).
  The parent explicitly claims no credit for it; the new contribution is the
  source-exact identification (§3) and the full arbitrary-partition resolution.
  No paper stating this identification for KY (or this form of the general
  lemma applied this way) was found.

**Access limits**: Semantic Scholar Graph API 429 (citation count taken from a
search-result snippet, consistent with "0 citations"); Exa rate limits on two
queries; no Google Scholar/INSPIRE/DBLP/MathSciNet sweep; MathDB read from the
parent lane's fresh live JSON (SHA-matched commit), not re-fetched. Within
these bounds: **not already resolved, not posted, not subsumed**.

## Gate 4 — ELIGIBILITY: PASS (prospective, one outcome)

* One complete resolution of the full source question (all l ≥ −1, all
  λ ⊢ l+2, all three clauses, k ≥ −1) — not a fixed-partition or numerical
  special case.
* Novelty does **not** rest on the MathDB record (whose companion grouping is
  demonstrably wrong) but on the source PDF + independent citation/author
  search above.
* Classical machinery uncredited by design; proposed credit is for the
  identification + resolution, consistent with the parent's own framing.
* No priority claim made; no count change; credit stays 0.

## Gate 5 — FORMAL BRIDGE: viable, conditional, NOT a formal PASS

The parent correctly flags that a generic head-tail theorem alone is not the
literal source endpoint. Recommended two-tier bridge:

**Tier 1 (self-contained; formalizable now).** Abstract theorem over hypotheses:
(H1) M_s(α) = αI − A_s with A real symmetric, A₀ = A fixed;
(H2) A_s = A with an s-vertex zero-diagonal unit-weight path appended at a
fixed unit coordinate e (path sign ±1 immaterial — diagonal similarity);
(H3) det M_s = F·P_{N+s} in ℝ[α] with F monic fixed, P reduced, monic, ramping
from N (degs +1).
Conclusions: (i) P_{N+s} = charpoly(J_s), J_s irreducible Jacobi built from the
Krylov compression of A at e (r = deg P_N), for s ≥ 0, and P_{N−1} =
charpoly(J∖e) (= 1 if r = 1); (ii) all P_{N+k}, k ≥ −1 squarefree;
(iii) #{roots of P_{N+s} outside [−2,2]} eventually constant and ≤ 2r;
(iv) ∪_{s≥0} interior roots dense in [−2,2] (with O1's endpoint argument).
Mathlib dependencies to verify before quoting: Hermitian eigenvalue interlacing
(Cauchy), bordered/blocked determinant expansion, polynomial gcd/monic/radic
machinery, and a constructive cosine-grid counting lemma for (iv). The
"eventually constant" clause is inherently non-constructive (no explicit
stabilization index is produced; only the bound ≤ 2r).

**Tier 2 (source-faithful endpoint).** Verify (H1)–(H3) for Γ^{(λ)}_{l,n} from
the KY algebra: basis (3.2.1)–(3.2.2), form computation (3.13)/(3.2.4),
Lemmas 3.20/3.23/3.24, Prop 3.25, Thm 3.19. This is a major representation-
theory formalization project. Honest interim: state the source items as
explicitly cited hypotheses (they are *proved* in the source preprint, not
conjectured — but the preprint is not peer-reviewed, and (3.1.1)'s sign typo
shows the source must be handled carefully). The reducedness input is part of
the ramping property (3.7), which Prop 3.25/Thm 3.19 supply.

**Machine-checked test vectors for the Lean bridge** (exact, in evidence/):
(l,λ) = (1,(3)) and (1,(1³)) from Eq (3.2.5) — full chain including q_{−1} and
det Γ_(13) = C·P₁₃; (1,(2,1)) from Figure 2 — d=2 chain including F = C·P₅ and
det Γ_(8,8) = C·P₈². Extend to every matrix printed in §3.3/§A as a
regression suite.

## Verdict

* SOURCE: **PASS**. MATH: **PASS** (independently re-derived; machine-verified
  on source-printed data for d=1 and d=2). NOVELTY: **conditional PASS** —
  no prior resolution found within bounded search; classical machinery
  uncredited by design. ELIGIBILITY: **PASS** as a prospective one-outcome
  resolution of an open conjecture. FORMAL: **conditional** — viable bridge
  specified; no formal claim.
* Required repairs before any promotion: (a) spell out the density-endpoint
  argument (O1); (b) replace "strictly positive" by "nonzero" in §2 (O2);
  (c) pin the recurrence sign to (3.2.7)/(3.2.9) in any formal statement.
* No priority claim, no count change, credit 0. This review adds no entries to
  shared indexes and stages/commits nothing.

— Review sub-agent, lane pi-kadar-yu-preliminary-review
