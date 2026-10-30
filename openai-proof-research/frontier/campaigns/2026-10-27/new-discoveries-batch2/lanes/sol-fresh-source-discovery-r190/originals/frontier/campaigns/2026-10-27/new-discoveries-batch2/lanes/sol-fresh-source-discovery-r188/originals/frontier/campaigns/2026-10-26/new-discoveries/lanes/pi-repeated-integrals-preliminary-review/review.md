# Preliminary source/math/novelty/eligibility review — parent-repeated-integrals @ ae8275d81f

Review lane: `pi-repeated-integrals-preliminary-review`. Solo reviewer (pi), no children,
no external posts, no git operations, no edits outside this lane. Tally unchanged (16/30,
candidate credit 0). This is a PRELIMINARY review, not a formal or manuscript gate: no
Lean development and no paper exist for this candidate.

Candidate: `NEW/lanes/parent-repeated-integrals` (PROOF.md sha256
`4d356788ec926c36ab294667fbbde3a2378912cccff6a2378cb2be336ec9f1b2`), frozen by
`review-hashes.json` binding 10 files. All 10 re-hashed byte-identical at review time.

## 0. Verdict summary

| Gate | Verdict |
|---|---|
| G1 Source fidelity & provenance | **PASS** |
| G2 Mathematics (independent rederivation) | **PASS** |
| G3 Novelty (serious bounded screen) | **PASS** (bounded; limits in §8) |
| G4 Eligibility (subsumption decision) | **PASS** — substantive previously unreported resolution of an explicit all-n open question; **not** an uncountable immediate corollary |

**Explicit subsumption decision (the MAIN ISSUE).** di Dio's Theorem 2.5 /
Corollary 2.7 (arXiv:2411.03145v2 pp. 5–6; published as Theorem 2.5 and
Corollary 3.1 in DOI 10.1007/s00013-025-02175-1) does **not** directly subsume
(P_n). Applied naively it yields, for an interior moment functional, a Cc∞
density that vanishes near both endpoints — it says nothing about W_n, nothing
about positivity of the density on all of [0,1], and nothing about the endpoint
germ rho=1 with all higher endpoint jets 0. Reaching (P_n) requires a genuine
reduction chain (§6): the atomless-Stieltjes-to-interior bridge, the kernel
identity, and the endpoint-baseline germ lemma. None of these appears in di Dio
or in the source. Conversely the parent's own proof is self-contained and does
not need di Dio at all. Exact accounting of new reasoning is in §6. The result
should be recorded as a **resolution of an explicit open conjecture
(Burke–Haris–Madhavendra Conjecture 1.2 = MathDB 371768 (P_n), all n)** whose
proof is short and uses standard truncated-moment-cone technology — not as a new
deep theorem, and with no priority claim. No formalization exists; this review
does not certify any Lean endpoint.

## 1. Scope and method

I independently rederived every step of PROOF.md, retrieved all primary sources
fresh, and re-inspected them (text and, for the conjecture page, visually).
Numerical checks (Gauss–Legendre quadrature, exact linear algebra) were run for
the kernel identity, the transformation T, the boundary/interior dichotomy, and
cross-checked against the source's own explicit descriptions of W_1, W_2 (exact
match) and W_3 (consistent). I did not read any running other lane or status file.

## 2. Provenance and frozen-byte verification

`review-hashes.json` binds PROOF.md, provenance.json, and 8 source files. All 10
recomputed sha256 values match exactly. Fresh retrieval on review date:

| Source | Frozen sha256 (prefix) | Fresh sha256 (prefix) | Match |
|---|---|---|---|
| arXiv:2512.02151v1 PDF (37 pp.) | 914981e19128… | 914981e19128… | ✔ byte-identical |
| arXiv:2411.03145v2 PDF (29 pp.) | 6b15667fda74… | 6b15667fda74… | ✔ byte-identical |
| arXiv:2512.23949v1 PDF (24 pp.) | 99f8bf6cfa78… | 99f8bf6cfa78… | ✔ byte-identical |

Fresh copies downloaded from `arxiv.org/pdf/<id>vN` on review date into a temp
directory (not written into the frozen lane). The three frozen `.txt`
extractions and `conjecture-page2.png` and `mathdb-371768-live.json` were read
directly from the frozen lane; the png was visually inspected (see §3).

Access limits: Springer `link.springer.com` serves a JS client challenge to plain
HTTP clients; the published full HTML was retrieved through an extraction service
(successfully — full theorem bodies obtained, §5). `mathdb.org` is an unrelated
WordPress site; the live MathDB record lives at `mathdb.com/problems/371768`
(retrieved; §3.3). Semantic Scholar API rate-limited (HTTP 429); OpenAlex and
arXiv.gg used instead. MathSciNet/zbMATH not accessible — not screened (limit).

## 3. Source statements verified

### 3.1 arXiv:2512.02151v1, p.2 — visually inspected (frozen `conjecture-page2.png`)

The rendered page shows verbatim:

- `W_n = {b ∈ R^{n+1} : there is an f ∈ C^n[0,1] with D^n f increasing and nonconstant
  such that D^j f(0) = 0 and D^j f(1) = b_j for all j = 0,…,n}` with footnote 1:
  "increasing in its non-strict sense".
- "(P_n) is the statement that W_n is open in R^{n+1} and that for each b ∈ W_n we may
  choose the witnessing function f to be C∞ and so that D^{n+1}f(x) > 0 for all
  x ∈ (0,1), D^{n+1}f(0) = D^{n+1}f(1) = 1 and D^j f(0) = D^j f(1) = 0 for j > n+1."
- "Conjecture 1.2. (P_n) is true for all nonnegative integers n."
- Theorem A (Theorem 8.2): (P_n) holds for n = 0,1,2,3, with explicit descriptions
  W_0 = {a>0}, W_1 = {0<a<b}, W_2 = {0<2a<b, b²<2ac},
  W_3 = {0<c<d, 2b²<3ac, 6ad+4b²+c² < 6ac+2bc+2bd}.

This matches PROOF.md's target statement literally, including the endpoint-jet clause.
Endpoint derivatives are one-sided (source §2, "the derivatives are meant in the
one-sided sense"); the parent's witnesses (smooth rho ≡ 1 near endpoints) satisfy
these regardless.

### 3.2 arXiv:2512.02151v1, p.13 — Proposition 4.4

Text verified: `W_n = {b : there is g ∈ F_0, g(0) = 0, I^j g(1) = b_{n−j}, j = 0,…,n}`
with proof "Use the correspondence g = D^n f, f = I^n g between the witnessing
functions." So the source itself already operates in the repeated-integral
formulation; the parent's kernel identity (2) is the Stieltjes-kernel form of
I^{n−j}g(1) with mu = dg. The source contains no measure-cone machinery (its only
measure mention is an incidental Lebesgue-measure error bound, Lemma 7.11); the
moment-cone route is genuinely absent from the source.

### 3.3 MathDB 371768 — full live record inspected (review date)

Live page `mathdb.com/problems/371768` ("The openness and smooth-witness conjecture
for repeated integrals"): statement identical to the frozen JSON (including the
closing sentence "The supplied text gives no resolution of (P_n), so its status
remains open"); tags approximation-theory, differentiable-functions, real-analysis;
**Solutions 0 — "No solutions have been posted yet"; Progress summary — "Nothing
recorded yet"; no comments; no replies; no model attempts; no human solves.**
All arrays of the frozen record (`comments`, `solutions`, `model_attempts`,
`formulations`, `replies`) are empty, consistent with the live page. Status open.

### 3.4 Sequel arXiv:2512.23949v1 (30 Dec 2025, single version) — conditional, verified in body

- Abstract: "The proof for n ≤ 3 establishes the theorem for all n, assuming a
  conjecture (shown in previous work with Haris and Madhavendra to hold for n ≤ 3)…"
- §2: "(Q_n) … was shown in [3] to hold for n ≤ 3. (In [3] it was called (P_n), but
  we call it (Q_n) here…"; Definition 2.4; "Conjecture 2.5 ([3]). (Q_n) is true for
  all nonnegative integers n."; "Theorem 2.6 ([3], Theorem A). (Q_n) holds for n ≤ 3."
- Main theorem: "Theorem 4.2. **Assume (Q_n).** …"; later text applies it only for
  n ≤ 3 ("Since (Q_n) holds for n ≤ 3, we can apply Theorem 4.2 for n = 2…").

So the sequel is and remains conditional on the all-n statement. PROOF.md's
characterization is accurate.

## 4. Independent mathematical rederivation

I rederived every step myself; none was accepted from PROOF.md without
independent verification. Findings, including the specific items the review was
asked to probe:

**(a) Stieltjes measure and atomlessness at the endpoints.** For b ∈ W_n with
witness f, g = D^n f is continuous on [0,1] (one-sided endpoint convention), so
mu = dg is a finite positive measure with **no atoms, including at 0 and 1**:
dg({0}) = g(0+) − g(0) = 0 and dg({1}) = g(1−) − g(1) = 0 by continuity. mu is
nonzero since g is nonconstant, and g(x) = mu([0,x]). This is the linchpin: an
atom would kill interiority (verified: for mu = δ_t*, the nonneg quadratic
(t−t*)² has ∫ q dmu = 0, so T(mu) is a boundary point; numerically confirmed
single atoms at 0.2/0.5/0.8 all fail the W_3 inequalities).

**(b) Kernel/factorial identity.** b_j = D^j f(1) = ∫₀¹ (1−t)^{n−1−j}/(n−1−j)! · g(t) dt
for j ≤ n−1 and b_n = g(1); one Stieltjes integration by parts (boundary terms
vanish: (1−t)^{n−j}g(t) = 0 at t=1 since n−j ≥ 1, and at t=0 since g(0)=0) gives
b_j = 1/(n−j)! ∫₀¹ (1−t)^{n−j} dmu(t) for all j. This equals the source's
I^{n−j}g(1) of Proposition 4.4. Verified numerically for n = 0,…,5 (max error
1.6e−15).

**(c) C closed, full-dimensional; dual cone; interior criterion.** Closedness: if
moment vectors of mu_i converge to y, then masses mu_i([0,1]) = first coordinates
converge to y_0; if y_0 > 0 the normalized mu_i are tight probability measures on
compact [0,1], a weak-* subsequential limit mu is positive with moments y (t^j
bounded continuous); if y_0 = 0 then |y_k| ≤ y_0 → 0 so y = 0 ∈ C. Full dimension
via Vandermonde at n+1 distinct points. Dual cone = coefficient vectors of q ≥ 0
on [0,1], deg ≤ n (single atoms as test measures). Interior criterion for closed
full-dimensional cones: y ∈ int C ⟺ ⟨c,y⟩ > 0 for all 0 ≠ c ∈ C* (I re-proved the
⟸ direction by separating y from int C and using that int C is itself a cone).
Atomless nonzero mu: for 0 ≠ q ≥ 0 of deg ≤ n, the zero set Z is finite, so
mu([0,1]∖Z) = mu([0,1]) > 0 and ∫ q dmu > 0. Hence y ∈ int C. **Includes n = 0**
(C = [0,∞), dual = {c ≥ 0}, y_0 = mu([0,1]) > 0). Note (my observation, no impact):
atomlessness is sufficient, not necessary — for n = 3 a measure with two distinct
interior atoms also has interior moment vector, because a nonneg cubic cannot
vanish at two interior points (even multiplicity required, degree ≥ 4). The parent
only needs sufficiency. No error.

**(d) A convex, open, dense in C; A = int C.** Convexity is immediate. Openness:
given rho, choose distinct t_0,…,t_n ∈ (0,1) and nonnegative integral-one bumps
psi_i on tiny disjoint supports; the linear map c ↦ Σ c_i m(psi_i) has moment
matrix tending to the Vandermonde matrix, hence invertible for small supports;
rho + Σ c_i psi_i stays strictly positive for small c (rho > 0 on compact [0,1]
has a positive minimum; perturbations vanish outside the support union), endpoint
germs stay 1, and the image of the admissible c-neighborhood under the invertible
moment map is an open neighborhood of m(rho). Correct. **A density in C:** finite
atomic approximation (mesh → 0 gives moment error ≤ ω_j(mesh)·mu([0,1]) → 0),
each atom — including endpoint atoms at 0 and 1 — approximated in moments by a
nonnegative bump supported strictly inside (0,1) (near 0: ∫ t^j psi ≤ m·ε^j → 0
= m·0^j; near 1: ∫ t^j psi → m; both correct), plus the baseline
eta + (1−eta)(chi_L + chi_R) ≥ eta > 0, ≡ 1 near both endpoints, total mass
≤ eta + |supp chi_L| + |supp chi_R| → 0. Correct. **A = int C:** A is nonempty
(rho ≡ 1), open, convex, with cl A = C. The step int(cl A) = A for open convex A,
which PROOF.md cites as elementary without proof, is a genuine classical fact; to
be adversarial I re-proved it: accessibility lemma (for c₀ ∈ int A, x ∈ cl A,
t ∈ (0,1), the point (1−t)c₀ + tx ∈ int A — proved via a C-point placed within
the ball around c₀, then a perturbation ball argument), which gives points
z_s ∈ A with B(z_s, 2sρ) ⊆ A for z_s → x₀ ∈ int(cl A); for large s these balls
cover a ball around x₀, so x₀ ∈ A. No gap.

**(e) Identification W_n = T(int C) and all endpoint jets.** T(y)_j =
1/(n−j)! Σ_k (−1)^k C(n−j,k) y_k is anti-triangular with nonzero antidiagonal
1/(n−j)!, det T = ±∏_j 1/(n−j)! ≠ 0; verified numerically (n = 0,…,5) including
the action on point masses: T(p(s))_j = (1−s)^{n−j}/(n−j)!. Witness construction
F(x) = 1/n! ∫₀ˣ (x−t)^n rho(t) dt: F ∈ C∞[0,1], D^j F(0) = 0 for j ≤ n
(F(x) ~ rho(0)x^{n+1}/(n+1)!), D^{n+1}F = rho > 0 on (0,1), D^j F(1) = T(y)_j by
(b), D^{n+1}F(0) = D^{n+1}F(1) = rho(0/1) = 1, and D^j F(0) = D^j F(1) = 0 for
j > n+1 because rho ≡ 1 near both endpoints. D^n F is strictly increasing (n ≥ 1)
resp. F strictly increasing (n = 0), and nonconstant. Conversely b ∈ W_n gives
b = T(y) with y ∈ int C by (a)–(b). Hence W_n = T(int C), open. Both clauses of
(P_n) follow; the second clause's jet requirements are exactly met.

**(f) Exact cross-check against the source's own Theorem A (strongest evidence).**
n = 1: int C = {m > 0, 0 < c₁ < m} (m = ∫1, c₁ = ∫t), T gives
(b_0, b_1) = (m − c₁, m); the set {0 < b_0 < b_1} is **exactly** the source's
W_1 = {(a,b): 0 < a < b}. n = 2: int conditions {m > 0, 0 < c₁ < m, c₁² < m c₂}
(Cauchy–Schwarz) map under T to exactly {0 < 2a < b, b² < 2ac} — the source's W_2,
inequality for inequality. n = 3: every sampled positive smooth density satisfies
the source's W_3 inequalities (2000/2000), single atoms violate them (3/3 fail),
and — consistently with the face structure of the truncated cone — two-point
interior atoms satisfy them (a nonneg cubic cannot vanish at two interior
points). The parent's characterization therefore reproduces the source's own
explicit all-cases description exactly. This is an independent confirmation of
the entire identification, not merely of consistency.

**Conclusion of §4:** the parent's mathematical argument is correct as stated; I
found no gaps. (P_n) holds for all n, and Conjecture 1.2 is true, by this argument.

## 5. Prior art read in full (not from abstracts)

- **di Dio, arXiv:2411.03145v2 (30 Nov 2024), pp. 5–6, read in full from frozen
  text + fresh identical PDF.** Definition 2.1 (Dirac-approximating family,
  [dD19 p.3022]); Richter's Theorem 2.4 [Ric57, Satz 4]; **Theorem 2.5
  ([dD19, Thm. 17])**: L from the interior of the moment cone on an n-dimensional
  V is represented by Σ_{i≤n} c_i δ_{σ_i, x_i} with c_i > 0; **Corollary 2.7**:
  if the family has L¹/C∞/Cc∞ densities w.r.t. mu, so does the representing
  measure. §2.2 explicitly notes Cc∞ mollifier families always exist for the
  Lebesgue cases. The central result is credited to the 2019 predecessor.
- **Predecessor verified at source:** di Dio, arXiv:1804.07058v2 (PAMS 147
  (2019) 3021–3038), **Theorem 17**: T_A full-dimensional convex cone,
  int T_A = int S_A, and (under local-compactness hypotheses) T_A = int S_A ∪ {0}.
  Matches the citation chain exactly.
- **Published truncated version DOI 10.1007/s00013-025-02175-1** (open full HTML,
  retrieved via extraction service; Springer blocks plain HTTP with a client
  challenge): same Definition 2.1 / Richter 2.4 / **Theorem 2.5** (= [dD19 Thm
  17]) / Corollary 2.6; the Cc∞ statement appears as **Corollary 3.1** (= arXiv
  Corollary 2.7), and the proof of Corollary 2.6 itself already constructs the
  Cc∞ density rho = Σ g_{ε_i, x_i}. Citation caveat for the parent: cite
  "Corollary 2.7 (arXiv) = Corollary 3.1 (published)".

## 6. Subsumption decision — exact amount of new reasoning

Relative to a **directly subsuming known theorem** (there is none — see below),
the distance from di Dio's theorem to (P_n) consists of exactly four items:

1. **Atomless-interior bridge (necessary, new in this role).** di Dio's hypothesis
   is interiority; nothing in it shows that the functional b ∈ W_n ↦ (moment
   vector of mu = dg) is interior. That requires g = D^n f continuous (mu
   atomless, §4(a)) — the single mathematical place where the source's C^n
   hypothesis enters. Without it the route collapses (single atoms are boundary
   points). ~5 lines + the standard interiority criterion.
2. **Kernel identity (2)** b_j = 1/(n−j)!∫(1−t)^{n−j} dmu (Stieltjes form of the
   source's own Prop 4.4 I^j-formulation). ~5 lines; partially in the source.
3. **Endpoint-baseline germ lemma**: baseline ≡ 1 near endpoints with arbitrarily
   small mass, so that a Cc∞ interior-supported residual can be topped up to
   rho > 0 with germ exactly 1 and trivial higher jets. ~10 lines; **not in di Dio**
   (whose densities vanish near endpoints) and not in the source. Also needed:
   int C_{(0,1)} = int C_{[0,1]} — PROOF.md justifies this vaguely ("by convex
   density and the Vandermonde span"); the clean reason is that the atomless
   measure at hand has zero endpoint mass, so int C ⊆ C_{(0,1)} ⊆ int C_{(0,1)} and
   C_{(0,1)} ⊆ C closes it (repair R1).
4. **Assembly**: T invertible (anti-triangular, det = ±∏ 1/(n−j)!), witness
   construction, jet bookkeeping. ~15 lines, routine.

Total new reasoning beyond known theorems: roughly one page of elementary
argument plus the **conceptual identification** W_n = T(int C) — which is the
actual idea, absent from the source (no measure machinery), absent from di Dio
(no W_n, no germs, no positivity), and unreported anywhere found (§7). The di Dio
route is *not* a one-line instantiation; the "uncountable immediate corollary"
dismissal does **not** apply. Equally, the parent's self-contained proof (§4(d))
makes di Dio unnecessary — the entire content is elementary once phrased in
moment-cone language. Honest framing: **a correct, short, essentially elementary
resolution of an explicit open conjecture, via standard (but correctly assembled)
truncated-moment-cone technology.** It deserves recording as a resolution of
Burke–Haris–Madhavendra Conjecture 1.2 / MathDB 371768; it does not introduce new
machinery, and no priority or depth claim should be attached.

## 7. Novelty screen (serious, bounded)

- MathDB 371768 live (review date): open, 0 solutions, no progress summary, no
  comments/replies/model attempts (§3.3).
- Citing corpus: OpenAlex — 2512.02151 cited_by 0; arXiv.gg — "0 citations in our
  index". Only known citation is the author's own conditional sequel.
- The source contains no measure-theoretic route (§3.2); its authors' method is
  constructive and explicitly proves only n ≤ 3.
- di Dio 2019/2024/2025 chain contains no W_n, no endpoint germs, no positivity;
  its Example 2.3 shows interior functionals *without* representing densities, the
  complementary concern. Nothing there states or implies (P_n).
- Targeted web searches for any resolution of (P_n)/W_n openness (2025–2026): none
  found.
- **Limits:** no MathSciNet/zbMATH access; no full sweep of 2026 preprints,
  seminars, referee reports, or the authors' private knowledge. A resolution could
  in principle exist unindexed. Screen is bounded and this is stated.

## 8. Objections and repairs

No decisive objections — the argument survives adversarial rederivation intact.
Minor repairs (presentational, none affects validity):

- **R1.** PROOF.md's justification of "int of the cone over (0,1) = int C" is
  vague. Replace by: the atomless measure representing an interior vector has zero
  endpoint mass, hence int C ⊆ C_{(0,1)}; C_{(0,1)} ⊆ C convex gives equality of
  interiors.
- **R2.** PROOF.md cites "int(closure A) = A" for open convex A as elementary. It
  is classical but should carry a one-line proof or citation (accessibility lemma;
  see §4(d)) since it is the only non-bookkeeping convexity fact used.
- **R3.** Cite the published corollary as "Corollary 2.7 (arXiv v2) = Corollary
  3.1 (DOI 10.1007/s00013-025-02175-1)"; Theorem 2.5 keeps its number in both.
- **R4.** State explicitly that atomlessness is sufficient but not necessary for
  interiority (two interior atoms suffice for n = 3), so later formalization does
  not over-assume.
- **R5.** Record the W_1/W_2 exact-match cross-check (§4(f)) as independent
  evidence in any writeup; it is the cheapest referee-proof of the identification.

## 9. Formal scope (unchanged)

No Lean endpoint exists. A faithful formalization must quantify all n, encode the
literal C^n monotonicity/initial-terminal derivative data, the Stieltjes moment
identity, the interiority of atomless measures, the bump/baseline construction,
and the endpoint jets. An abstract moment-cone theorem would not certify the
source conjecture. This review formalizes nothing and changes no tally.

## 10. Per-gate detail

- **G1 SOURCE: PASS.** All three arXiv PDFs byte-identical to frozen copies on
  fresh retrieval; p.2 visually inspected and matches PROOF.md literally; Prop 4.4
  verified in text; MathDB live record fully inspected (open, zero activity);
  sequel conditional verified in body and abstract; di Dio theorem bodies read in
  full in both arXiv and published versions; 2019 Theorem 17 verified at its own
  source. Recorded limits: MathSciNet/zbMATH inaccessible; Springer via extraction
  service (content complete); Semantic Scholar rate-limited (OpenAlex substituted).
- **G2 MATH: PASS.** Every step independently rederived (§4); numerical checks at
  1e−15 level; exact structural match to the source's own W_1, W_2 and consistent
  W_3; atomless-endpoint issue handled correctly; A-openness, A-density (including
  endpoint atoms), and the int(cl A) = A step all verified; no circularity in the
  W_n = T(int C) equivalence; n = 0 covered.
- **G3 NOVELTY: PASS (bounded).** Not present in source, sequel, MathDB, citing
  corpus (0 citations), di Dio chain, or targeted searches. Bounded screen; limits
  stated in §7 and inherited by any parent integration note.
- **G4 ELIGIBILITY: PASS.** Explicit decision: this is a **substantive,
  previously unreported (within the bounded screen) resolution of the source's
  explicit all-n question (Conjecture 1.2)**, not an uncountable immediate
  corollary of di Dio's theorem — see §6 for the exact accounting. Required
  framing for the parent: record as *resolution of an explicit open conjecture*;
  techniques are standard truncated-moment-problem tools; no new machinery; no
  worldwide priority claim; not formalized; candidate credit decision and ledger
  integration belong to the parent and are not changed by this review.

## 11. Review artifacts

Fresh retrieval copies kept outside the frozen lane (temp directory at review
time); only `review.md` and `provenance.json` written in this lane. Numerical
checks run in a scratch session (quadrature/linear algebra, results quoted in
§4); scripts not persisted in the lane by design (preliminary review, no
formalization for credit).
