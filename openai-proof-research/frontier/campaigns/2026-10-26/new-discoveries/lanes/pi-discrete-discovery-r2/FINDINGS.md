# Lane: pi-discrete-discovery-r2 — findings

Research sub-agent lane for the `2026-10-26/new-discoveries` campaign.
Date: 2026-10-26. All primary PDFs are in `sources/`.

**Bottom line: no accepted (credit-bearing) result.** Four MathDB records were
eliminated as stale/mis-labeled, two of them with complete proofs recorded below
(379218, 366975/356886/353228/354966 cluster). Documentation of every screened
candidate and rejection reason is at the end.

---

## 1. MathDB 379218 — ABR Conjecture 5.3 is a corollary of Stanley (1980), Theorem 3.1. EXCLUDED.

**Record.** MathDB 379218 states (Adin–Brenti–Roichman, math/0508362, JCTA 2005,
Conjecture 5.3; record open, 0 solutions): for 0 ≤ k < n the polynomial

    P_{n,k}(q) = [n choose k]_q · ∏_{j=k+1}^n (1+q^j)

is symmetric and unimodal. ABR verified n ≤ 15 and state it as open.

**Claim.** P_{n,k} is the rank-generating function of the type-B parabolic
quotient W^J ⊆ B_n with J = S∖{s_k}; hence its symmetry and unimodality are the
content of Stanley, *"Weyl groups, the hard Lefschetz theorem, and the Sperner
property"* (1980), Theorem 3.1. Not a genuine open problem.

**Proof chain** (all steps verified; scripts inline in this file's history, see
`verify_379218.py`):

1. *(Descent-class formula; ABR's own Theorem 3.3 with M = {k}, plus σ ↔ σ⁻¹.)*
   P_{n,k}(q) = Σ_{σ∈B_n, Des_B(σ^{-1})⊆{k}} q^{ℓ_B(σ)}
             = Σ_{w∈B_n, Des_B(w)⊆{k}} q^{ℓ_B(w)}.
   (ℓ_B(σ) = ℓ_B(σ^{-1}); the map σ ↦ σ^{-1} bijects the classes.)
   Verified by direct enumeration of B_n for n ≤ 8, all k.

2. *(Parabolic identification.)* {w ∈ B_n : Des_B(w) ⊆ {k}} is exactly the set
   W^J of minimal-length right coset representatives for W/W_J with
   J = S∖{s_k}, since W^J = {w : Des_R(w) ∩ J = ∅}. Here
   W_J = ⟨s_0,…,s_{k−1}⟩ × ⟨s_{k+1},…,s_{n−1}⟩ ≅ B_k × S_{n−k}.

3. *(Rank GF = quotient of Poincaré polynomials.)* Stanley 1980, §2, points (4)
   and (5): W^J is a graded subposet of W ranked by ℓ, and
      Σ_{w∈W^J} q^{ℓ(w)} = F(W,q)/F(W_J,q).
   For W = B_n: F(B_n,q) = ∏_{i=1}^n [2i]_q, so
      F(B_n)/F(B_k)F(S_{n−k}) = ∏_{i=k+1}^n [2i]_q / ∏_{i=1}^{n−k} [i]_q.
   Algebraically,
      [n choose k]_q ∏_{j=k+1}^n (1+q^j)
        = (∏_{i=n−k+1}^n [i]_q/∏_{i=1}^k [i]_q) · ∏_{j=k+1}^n [2j]_q/[j]_q
        = ∏_{j=k+1}^n [2j]_q · (∏_{i=n−k+1}^n [i]_q ∏_{i=1}^{n−k}[i]_q) / (∏_{i=1}^k[i]_q ∏_{j=k+1}^n [j]_q)
        = ∏_{j=k+1}^n [2j]_q / ∏_{i=1}^{n−k} [i]_q        (numerator and denominator of the
          middle fraction are both [n]!_q),
   which is exactly F(B_n)/F(B_k)F(S_{n−k}). Verified numerically for n ≤ 8, all k.

4. *(Stanley's theorem.)* Theorem 3.1 of Stanley 1980 (verified verbatim from the
   primary PDF, `sources/stanley80.pdf`): *"(W,S) a Coxeter system for which W
   is a Weyl group, J ⊆ S. Then W^J is rank-symmetric, rank-unimodal, and has
   property S."* — via the Schubert-cell cellular decomposition of G/P
   (Theorem 2.4), valid for **every** parabolic J ⊆ S.

Steps 1–4 give: P_{n,k} is symmetric and unimodal for all 0 ≤ k < n. ∎

**Empirical cross-check.** Exact-integer search found zero violations of the
conjecture for n ≤ 40 (all k); the identity checks above were run for n ≤ 8.

**Remark.** ABR's conjectures 5.1/5.2 (unimodality of ℓ_B over *general* type-B
descent classes Des_B(σ^{-1}) ⊆ M) are *stronger* and not covered by Stanley's
theorem (general descent classes are not parabolic quotients); the ABR paper is
not vacuous. But the MathDB record states 5.3, which is the Stanley corollary.
Note also ABR cite [36] (Stanley's 1989 survey) for the k = 0 case, which is the
same theorem applied to J = {s_0}; the general k case is identical.

## 2. Circular fence / trace cluster: 356886, 353228, 366975, 354966 — resolved in the literature. EXCLUDED.

* **MathDB 356886 & 353228** (unimodality of circular fence rank polynomials,
  except compositions (a,1,a,1)/(1,a,1,a)): **Theorem 5.1** of
  Kantarcı Oğuz–Özel–Ravichandran, *"Chainlink polytopes and Ehrhart-equivalence"*
  (arXiv:2211.08382; published Annals of Combinatorics 2024), p. 14:
  "Rank polynomials of circular fence posets F̄(ā) are unimodal except when
  ā = (a,1,a,1) or (1,a,1,a)". Primary PDF: `sources/chainlink.pdf`.
  Both MathDB records are stale ("no resolution as of Nov 2022" — the resolution
  is Theorem 5.1 of the very paper cited).

* **MathDB 366975** (Kantarcı Oğuz's conjecture on tr M(a_1,…,a_{2m})):
  by [Kantarcı Oğuz, *Oriented posets, rank matrices and q-deformed Markov
  numbers* (arXiv:2206.05517, Discrete Math. 348 (2024)), Proposition 5.5],
  tr M_q(c_1,…,c_k) = R̄((a_1−1,a_2,…,a_{2m}), q) — a circular fence rank
  polynomial. Her own published note (v3, `sources/koguz.html`) states:
  "**Resolution of Conjecture 1.4**: After this paper was shared on arXiv, the
  author, together with Ravichandran and Özel, was able to resolve Conjecture
  1.4 about the unimodality of circular rank polynomials using characteristic
  polynomials of rank matrices. This is one of the results in the upcoming
  paper [6]" — [6] = the chainlink paper above.

* **MathDB 354966** (Leclere–Morier-Genoud trace unimodality): the same paper
  2206.05517 states in its abstract "We also resolve a conjecture of Leclere and
  Morier-Genoud" (and gives identities/characterizations of the exceptional
  cases). Resolved in the source itself.

## 3. Other candidates screened and rejected (with reasons)

| MathDB | Problem | Outcome / reason |
|---|---|---|
| 353227 | Morier-Genoud–Ovsienko q-deformed rationals unimodality | Resolved: McConville–Sagan–Smyth (Discrete Math. 2021) + 2112.00518/2201.03044 chain. |
| 355637 | (previous lane) | Already refuted in literature; no credit. |
| 354787 | q-Stirling parity log-concavity | Screened by parent-stirling lane (credit 0); no counterexample found to n=120. |
| 373707 | odd-zero-matrix | Screened by parent-graph-screen lane (credit 0). |
| 365199 | Grassmannian log-concavity | Parent-grassmannian lane, exploratory only. |
| 374706 | q-Fibonomial unimodality (Bergeron–Ceballos–Küstner) | Computed exactly: [m+n choose n]_F is polynomial, symmetric and unimodal for all m,n ≤ 12; cyclotomic factorization D_{m,n} = ∏_{d} Φ_d(q) over d with (m mod z(d))+(n mod z(d)) ≥ z(d)) gives no usable unimodal factorization. No proof or counterexample; left open. |
| 348539 | Strict unimodality of F_{n,k} (Chen–Jia Conj. 3.3) | Read primary source (2011.01467). Their semi-invariant method fails at r=2 since δ(2,n,n)=1 (their Lemma 3.1 gives exactly one semi-invariant of degree 2, weight n) — the authors state "it is not clear as to how this can be pursued". f_m − f_{m−1} = Δ_{k,n}(m) − Δ_{k−2,n}(m−n) with Δ Gaussian increments; no injection found. Left open honestly. |
| 337807 | Reiner–Stanton/Stanley–Zanello f(k,m,b) | k ≥ 6 open; single cases don't count; no new method found. |
| 358003 | Zanello strengthening of Bergeron's Gaussian inequality | Nonnegativity itself (q-Foulkes type) is the open hard core; unimodality out of reach. |
| 366993 | q-rious unimodality (Warnaar–Zudilin type) | Wide open; no traction. |
| 364289, 378964, 380137, 342617, 361318, 366993, 337098, 356218, 353228, 380718 | various | Fetched and triaged; either not matching campaign bar (single-case, stale, or already resolved) or no viable attack within this session; see sources/m*.json. |

## 4. Verification artifacts

* `verify_379218.py` — full verification of the three identities of §1
  (P_{n,k} = descent-class GF; descent-class GF = F(B_n)/F(B_k)F(S_{n−k});
  [B_n] = ∏[2i]_q), n ≤ 8, plus the SU check to n ≤ 40.
* Primary PDFs: `abr.pdf` (math/0508362v4), `stanley80.pdf` (Stanley 1980),
  `chainlink.pdf` (2211.08382), `koguz.html` (2206.05517v3),
  `2502.02974v3.pdf` (Ren–Yanagawa), `chenjia.pdf` (2011.01467).

**No PROOF.md/provenance.json/Lean artifacts were produced because no
credit-bearing new result survived; per campaign rules the lane reports honest
rejections only.**

## 5. Prior-art note on §1

A bounded web search (2026-10-26; several providers unavailable, Exa used)
found no published proof or resolution of ABR Conjecture 5.3. The exclusion
therefore rests on the primary-source chain of §1 (ABR's own Theorem 3.3 + the
classical parabolic-quotient rank-GF identity + Stanley 1980, Theorem 3.1),
not on a known publication. Per campaign rules a formal corollary of an
established theorem earns no credit even if the corollary itself is
unpublished; the observation is recorded here for the parent lane's use
(e.g., as a stale-label correction to MathDB 379218).
