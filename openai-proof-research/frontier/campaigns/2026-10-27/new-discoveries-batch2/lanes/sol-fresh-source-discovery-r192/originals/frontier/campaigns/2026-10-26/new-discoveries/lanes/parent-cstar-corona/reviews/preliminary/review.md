# Independent preliminary review — C*-Corona candidate (parent-cstar-corona @359f9ddd6f)

**Reviewer lane:** pi-cstar-corona-preliminary-review. **Mode:** solo adversarial review, no children, no git
operations, no external contact. **Verdict: mathematics CORRECT (verified); substantive eligibility FAIL —
the obstruction is a direct manifestation of old noncommutative A-analyticity rigidity and is an immediate
corollary of known theorems. Candidate credit remains 0. No formal or paper PASS is claimed or reviewed.**

Campaign tally after this review: **29/30** (Smale-infinite and Bieberbach packets separately accepted);
Corona remains uncounted with credit 0.

---

## 1. Freeze verification

All 13 relative files in `preliminary-review-hashes.json` were byte-copied to `frozen/` and re-hashed by
this lane: **13/13 SHA-256 match** the manifest exactly. Repo HEAD confirmed at `359f9ddd6f`
("Record source-faithful C-star Corona obstruction for substantive review"). `formal/Obstruction.lean` is
outside the freeze, incomplete, and was **not** reviewed; a post-freeze Lean endpoint built elsewhere is
out of my lane and was not inspected.

## 2. Source fidelity (personally inspected)

I visually read the retained author PDF (`krishna-author-zenodo-6917925.pdf`, SHA-256
2d537f04…afd59) at printed pp. 15–16 via the page renders:

- **Definition 2.6 (p. 15):** f: Ω → A (A unital C*-algebra, Ω norm-open) is *C*-algebraic holomorphic* iff
  for each a ∈ Ω there are r > 0 and coefficients {a_n} ⊆ A with
  f(z) = Σ a_n (z−a)^n converging in norm on 𝔻*(a,r) = {z : ‖z−a‖ < r}. **Left coefficients, right powers** —
  exactly as PROOF.md states.
- **Conjecture 3.2 (p. 16):** f_1,…,f_n: 𝔻*(0,1) → A bounded C*-algebraic holomorphic with
  Σ f_j f_j* ≥ δ and Σ f_j* f_j ≥ δ (all z ∈ 𝔻*(0,1), some real δ > 0) ⇒ there exist bounded C*-algebraic
  holomorphic g_1,…,g_n, h_1,…,h_n with Σ f_j g_j = 1 and Σ h_j f_j = 1. Quantifies over **every** unital
  C*-algebra; no commutativity assumption. Faithful to PROOF.md.

Zenodo API check this lane: record 6917925 has **exactly one version** (`version: "1"`, `is_last: true`);
preprints.org shows only v1 of 202208.0140. No author revision exists.

## 3. Mathematical verification — own checker, PASS (477 checks)

My independent exact checker is `checker/checker_own.py` (own code; not a re-run of the parent's
`check_exact.py`; deliberately different routes). Output `checker/checker_own-output.json`: **PASS, 477/477**.

Hypotheses of Conjecture 3.2 for the witness A = M₂(ℂ) (operator norm), f(z) = I + cz, c = diag(1/4, 0):

- **Def 2.6:** f is affine: f(z) = f(a) + c(z−a) at every center a — exact re-expansion identity verified on
  random exact rational (a,z) pairs. Trivially norm-convergent on any ball.
- **Boundedness:** ‖f(z)‖ ≤ 1 + ‖c‖‖z‖ < 5/4 (‖c‖ = 1/4 verified exactly and numerically).
- **Order bounds, δ = 1/2:** f(z)*f(z) = I + cz + z*c + (cz)*(cz) with (cz)*(cz) = z*c²z ≥ 0 (c² = c*c
  verified exactly) and cz + z*c ≥ −2‖cz‖I ≥ −I/2; likewise f(z)f(z)* = I + cz + z*c + (cz)(cz)*.
  Corroborated by 20,000-sample numeric min-eigenvalue sweep on the unit ball (min ≥ 1/2 − 1e−9).

Refutation (all exact rational arithmetic; the only infinite-series use is the **exact truncation** on the
nilpotent line z = ±tN, since (tN)^n = 0 for n ≥ 2):

- **N² = 0**, ‖N‖ = 2 (NᵀN = [[2,2],[2,2]], σ_max = 2), but **(cN)² = [[1/16,1/16],[0,0]] ≠ 0**.
- **R2 (parent's route, verified parametrically):** g(z) = Σ bₙzⁿ with f(z)g(z) = I forces
  b₁N = −cN and cNb₁N = 0. I solved b₁N = −cN with free parameters; for **every** solution,
  cNb₁N = [[−1/16,−1/16],[0,0]] ≠ 0. Unsolvable — no case analysis, no analytic manipulation.
- **R3 (my independent route):** f is invertible on the ball, so g = f⁻¹ is forced; exact 2×2 inverse
  (I + xcN)⁻¹ = I − (x/(1+x/4))cN. Truncation at ±tN forces b₁N = −(1/(1+t/4))cN **and**
  b₁N = +(1/(1+t/4))cN — sign conflict unless cN = 0. Contradiction.
- **R4:** the left-inverse half Σh_j f_j = 1 fails identically (b₁NcN = −(cN)² ≠ 0 for every solution).
- **X1 (rigidity route):** if g is affine (as known rigidity theorems force — see §4), f(z)g(z) = I on the
  ball already contradicts at ±tN; additionally the right-coefficient affine family g(z) = I + za is
  excluded because Na = −cN is unsolvable (rows of Na are negatives of each other for all a; −cN's are not).

**Conclusion of §3: the candidate's mathematical content is correct as stated.** The n = 1 instance of
Conjecture 3.2 in M₂(ℂ) fails; no bounded C*-algebraic holomorphic right (or left) inverse exists.

## 4. Prior art and subsumption (the decisive question)

**Does this merely expose an old/formulation failure of noncommutative Lorch/Scheffers-type A-analyticity?
My independent answer: YES.** Findings, strongest first:

1. **Rosenfeld 2000, theorem BODY read this lane** (EMIS/SANU full PDF,
   `sources/rosenfeld-n082p067.pdf`, 5 pp.): *B. Rosenfeld, "Differentiable functions in associative and
   alternative algebras…", Publ. Inst. Math. (Beograd) N.S. **68(82)** (2000), 67–71*, **Theorem 2**:
   "In simple noncommutative associative algebras among the functions y = f(x) only the linear functions
   y = ax + b and y = xa + b have right and left derivatives dy(dx)⁻¹ and (dx)⁻¹dy." Proved for ℍ
   (Liouville/conformal group) and for ℝⁿ, ℂⁿ, ℍⁿ, n > 1 (collineations; continuity assumed, automatic for
   differentiable maps). M₂(ℂ) = ℂ² as a real algebra is covered. Predecessors cited therein: Krylov
   (Doklady 1947) and Meylikhzon (Doklady 1948) for ℍ; Akivis (Mat. Zametki 1987).
   - Bridge (elementary, verified as §E1 of my checker): a Def-2.6 left power series satisfies
     f(z) − f(a) = (Σₙ≥₁ bₙ(z−a)ⁿ⁻¹)(z−a) by **pure associativity**, so its right quotient derivative exists
     at every point (= b₁). The 2025 paper below states the same direction ("convergent power series are
     A-differentiable"). Hence **Def 2.6 class in M₂(ℂ) ⊆ {affine functions}**.
   - Consequently the candidate's conclusion is an **immediate corollary of Rosenfeld Thm 2 + a 3-line
     nilpotent substitution**: the premise class is affine, so g would be affine, and §X1 of my checker
     derives the contradiction. The old fact directly subsumes the obstruction.
2. **The 2025 formulation repair confirms Def 2.6 is the known-bad class.** Ávila, Frías-Armenta,
   López-González, *A-Differentiability over Associative Algebras*, **Mathematics 13 (2025) 1619**
   (DOI 10.3390/math13101619). MDPI body fetch blocked (403, direct and via two fetchers); body read via
   the FreeLibrary full-text mirror (section-level excerpt). Their introduction **states the rigidity
   explicitly**: "In the quaternions case, for the left derivative, only functions f(x)=a+xb are
   differentiable, and for the right derivative, only functions f(x)=a+bx are differentiable; see [14]."
   Their own repaired class (df_x(v) = Σᵢ aᵢ(x) v bᵢ(x)) **is closed under products and quotients** and
   x⁻¹ is A-differentiable in it (their Props 1, 4, 5) — under that class the corona obstruction
   vanishes. This is precisely a **formulation correction**, which the campaign standard excludes.
3. **Strongest substantive objection (operator-supplied during this review; verified exactly in §S of my
   checker):** the **scalar-coefficient** affine f(z) = 2I + z satisfies every hypothesis of Conjecture 3.2
   with δ = 1 (‖(2I+z)v‖ > ‖v‖) and is uniformly invertible on the unit ball — yet its reciprocal
   **is** a left power series at 0 (exact geometric telescoping, verified: (2I+z)Σₙ₌₀ᵐ(−1)ⁿzⁿ/2ⁿ⁺¹ =
   I − (−1)ᵐ⁺¹zᵐ⁺¹/2ᵐ⁺¹) but **fails source analyticity at every noncentral interior center**: the true
   difference g(z) − g(a) = −(2I+z)⁻¹(z−a)(2I+a)⁻¹ has a right quotient with **no limit** at noncentral a
   (h ↦ hMh⁻¹ has a limit iff M is central), equivalently the differential h ↦ −a⁻¹ha⁻¹ is left
   multiplication bh iff a is central (verified exactly with a = diag(1/2,0) and separating h).
   So the failure is a **rigid structural property of the old noncommutative analyticity notion**, present
   already for the simplest scalar coefficient — the frozen projection-coefficient datum
   c = diag(1/4, 0) merely **relocates the failure to center 0** where a finite nilpotent truncation proof
   closes it. That is a proof-device, not a new mathematical phenomenon.
4. **Cook arXiv:1708.04135** (body in frozen sources): Thm 5.10 (product of A-differentiable maps in
   noncommutative algebras need not be A-differentiable), Example 5.11, and the explicit statement
   "Rosenfeld shows in [39] that there are only linear A-differentiable functions over simple associative
   or alternative algebras" (Cook's bibliography: *Publ. Inst. Math. 62(82), 67–71 (2000)* — issue 82 =
   vol 68, same paper). Cook–Freese arXiv:1708.04136 Prop 2.10 remark repeats the non-closure of products.
   Lorch (Trans. AMS 54 (1943) 414–425) is the abelian precursor — not itself a noncommutative subsumer.
5. **No conflict with known corona theory, and no recorded refutation found:** the classical
   operator-valued corona theorem concerns f_j: 𝔻 ⊂ ℂ → B(H) (complex variable); Krishna's variable lies
   **in the algebra** (z = ±tN), a genuinely different question — the source question is new, but its
   failure mode is 1947–2000 old. Searches (DuckDuckGo; Exa rate-limited) found no counterexample,
   no v2, no matching MathDB record, and the local trureturing Problems/Library checkout contains **no
   Corona problem entry** (only graph-theoretic "coronas"; its krishna Smale entry independently notes
   "No MathDB page was located" for this preprint family). Notably, Krishna's own later
   arXiv:2203.06916 restricts differentiation to **commutative** C*-algebras — the author moved away
   from the noncommutative notion.

## 5. Independent eligibility decision

**FAIL — not substantively eligible.** Under the standard (immediate known corollaries / formulation
corrections excluded; shortness alone never disqualifying or qualifying):

- The refutation is an **immediate corollary of Rosenfeld's 2000 rigidity theorem** (itself consolidating
  Krylov 1947 / Meylikhzon 1948) plus an elementary two-line factorization and a 3-line nilpotent
  substitution — the candidate's own self-contained proof, while correct and clean, is the same standard
  obstruction in the standard simplest setting.
- The phenomenon is a **formulation failure**: the source's Def 2.6 class is the classical
  Scheffers/Lorch-style left-power-series class, known since at least 1947/1948/2000 to collapse to affine
  maps in simple noncommutative algebras and not to be closed under products or reciprocals. The 2025
  repaired class closes the gap, confirming the diagnosis. The scalar-affine manifestation (§4.3) makes
  the rigidity reading unavoidable.
- What would have been needed for eligibility and is absent: evidence that the non-closure under
  **inversion**, or the failure of **this conjecture specifically**, carries content beyond the known
  rigidity — it does not; every new instance is ruled by the same theorem.

**Strongest objection preserved (verbatim in substance):** even scalar-coefficient affine f(z) = 2I + z is
uniformly invertible and source-holomorphic on the unit ball of M₂(ℂ) while its reciprocal fails source
analyticity at every noncentral interior center (differential −a⁻¹ha⁻¹ is not left multiplication); the
frozen projection-coefficient datum makes the obstruction occur at 0 with a finite nilpotent proof but does
not eliminate the eligibility objection. **I did not force PASS.**

## 6. Access limits (actual)

- Rosenfeld 2000: **full body read** (EMIS mirror of Mat. inst. SANU PDF).
- Mathematics 13(2025)1619: **body NOT obtained from MDPI** (403 via direct fetch, curl, and
  parallel_search; the downloaded file was an HTML error page and was deleted). Body read via the
  FreeLibrary full-text mirror excerpt — section-level, likely not every proposition statement.
- Cook / Cook–Freese: read from the parent's frozen text extractions; PDFs hash-verified against the
  parent's manifest but not independently re-downloaded.
- MathDB: no record located (search + attributed readings in adjacent lanes); this is bounded negative
  evidence, not a worldwide-priority claim. No external posting or communication of any finding.

## 7. Deliverables in this lane

- `review.md` (this file), `provenance.json`
- `frozen/` — byte-exact own copy of all 13 manifest files (13/13 hashes re-verified)
- `checker/checker_own.py`, `checker/checker_own-output.json` — own exact checker, PASS 477/477
- `sources/rosenfeld-n082p067.pdf` + `.txt` — Rosenfeld body (SHA-256 f659bda3…56a32d0f / 40520807…f4392)
- Count stands **29/30**; **Corona credit 0**; no formal or paper PASS claim made or implied.
