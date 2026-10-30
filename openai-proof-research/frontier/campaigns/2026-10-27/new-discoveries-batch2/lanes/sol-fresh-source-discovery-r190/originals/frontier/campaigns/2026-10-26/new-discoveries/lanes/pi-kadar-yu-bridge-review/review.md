# Bridge review — parent-kadar-yu frozen at commit 60ba544d47

Reviewer lane: `NEW/lanes/pi-kadar-yu-bridge-review` (solo, no children, no commits, no shared edits).
Date: 2026-10-26. Subject: independent adversarial review of the NEW arbitrary-head Gram/gcd model
(`GRAM-PROOF.md`, `SOURCE-BRIDGE.md`, `formal/*.lean`, 190 declarations / 22 modules) and its proposed
application to MathDB 372352 / Morris–Martin arXiv:2512.24535v1, Conjecture 4.5.1 (p35).
This is **not** a final manuscript/packet acceptance. Credit remains 0; accepted tally remains 16/30.

All 33 frozen file hashes in `bridge-review-hashes.json` verified against the parent lane at the frozen
commit before review; `frozen/` holds byte-identical copies (`sha256sum` receipt in `provenance.json`).
The parent's original PROOF.md (Lanczos route) was **not** reviewed here; the earlier
`pi-kadar-yu-preliminary-review` verdict does **not** carry over automatically and was used as context only.

## Verdict summary

| Gate | Verdict |
|---|---|
| 1 SOURCE (source equations + conjecture rendering) | **PASS** |
| 2 MATH (new codim-1 multiplicity route, independent re-derivation) | **PASS** |
| 3 FORMAL (fresh strict replay, 190/22, axioms ⊆ standard 3) | **PASS** |
| 4 SOURCE-SCOPE / CERTIFICATE (SOURCE-BRIDGE Q1–Q3) | **HOLD** — precise missing endpoint identified (formal-scope, not math) |
| 5 NOVELTY (bounded, serious) | **PASS** (no prior resolution found; access limits documented) |
| 6 ELIGIBILITY (single prospective outcome) | **PASS but not yet countable** — blocked by Gate 4 |
| **Overall** | **HOLD** — the exact all-partition source theorem is not yet certified; everything else stands |

---

## Gate 1 — SOURCE: PASS

Primary independently fetched: `sources/2512.24535.pdf`, SHA-256
`2d6f180bf33021ca6ab819928dfe51c91d44bed2eba8ccf03d2e443ed6bf5c86` — identical to the parent's retained
copy and provenance. arXiv abs page: **v1 only, submitted 31 Dec 2025**; no v2.

Checked verbatim in the retained source text (and cross-checked against the PDF):

- **(3.2.3)**: `Γ(∆n(n−2,λ))(α) = αI + Γ(∆n(n−2,λ))′`, with Γ′ = Γ|_{α=0} **real symmetric**. Verbatim.
- **(3.2.4)**: tail pairings `δ_{ii'}(αδ_{jj'} + δ_{j+1,j'} + δ_{j−1,j'})` — chains with diagonal α,
  unit couplings, **no cross-tail coupling between different Specht components** through tail elements;
  head is dense. Verbatim.
- **(3.17)** mixed tuples `n = (n_1,…,n_{d_λ})`, `n_k ≥ l+4`. Verbatim.
- **(3.2.17)**: extending one tail appends exactly one row/column with a single off-diagonal **1** at that
  tail's old endpoint and diagonal α; all other entries fixed. Verbatim — this is exactly
  `headTailMatrix_succ_border` with the attaching coordinate last.
- **(3.2.9)** Proposition 3.18: `det Γ_{l,n+2e_k} = α·det Γ_{l,n+e_k} − det Γ_{l,n}` — **MINUS**. Verbatim.
- **(3.2.12)**: `P_{a,b} = c·P_{a',b'}` with `c` the **maximal monic common factor** and the reduced series
  having the ramping property — i.e. the source itself proves reducedness (consecutive coprimality) of the
  normalized quotients. Verbatim.
- **Proposition 3.25**: `det Γ_{l,n} = C^{(λ)}(α) ∏_{k=1}^{d_λ} P_{n_k}^{(λ)}(α)`, C monic, P ramping. Verbatim.
- **Conjecture 4.5.1, p35**: squarefree `P^{(λ)}_{l+4+k}` for every `k ≥ −1`; eventually fixed number of
  roots outside `[−2,2]`; `∪_{k≥0}{α ∈ [−2,2] : P^{(λ)}_{l+4+k}(α)=0}` dense in `[−2,2]`. Matches the
  parent's rendering exactly (also consistent with the independent preliminary lane's render inspection).
- The printed plus in (3.1.1) vs minus in (3.2.7)/(3.2.9): confirmed; no credit sought. Correct.

MathDB **live re-fetched by me** (`sources/372352-live.json`, `POST /api/posts/372352`): status **open**,
`lean_formalization_count: 0`, no solutions/human solves. The record's companion grouping
(1601.04382 = Tran rational-generating-functions; 1510.01758 = Kelley–Owen finite-field trinomials) is
indeed unrelated to KY — parent's warning confirmed.

## Gate 2 — MATH: PASS (independently re-derived + exact machine checks)

I re-derived every load-bearing step of the new route from scratch; none requires Lanczos, an irreducible
head, or any factorization/coprimality/cyclicity premise:

1. **Literal construction.** `headTailMatrix h A c s` keeps *every* entry of the (h+1)-square head,
   gives new vertices zero diagonal and coupling `c` between adjacent indices only; the first new vertex
   couples to head coordinate `h` (attaching coordinate **last**). Cross-head couplings are retained.
   `gramModelMatrix = αI + (that with G, c=1)` and `gramModelMatrix_eq_charmatrix` resolves the sign
   convention exactly (equals charmatrix of `headTailMatrix h (−G) (−1) s`). Both couplings ±1 covered
   (`c^2 = 1`).
2. **Codim-1 multiplicity bound.** `spectralCountAbove/Below_prefix_upper` (viewing the prefix as the
   tail of a 1⊕n block via `lastFirstEquiv`) gives `N^±(A) − N^±(prefix) ∈ {0,1}`; with
   `spectral_counts_multiplicity` this yields `|mult_t(charpoly A) − mult_t(charpoly prefix)| ≤ 1`
   (`principal_root_multiplicity_bounds`) — literal polynomial-root multiplicities.
3. **Squarefree after gcd removal.** For a root t of p_s, coprimality of p_s,p_{s+1} puts
   `mult_t(p_s) = mult_t(f_s) − mult_t(f_{s+1}) ∈ {−1,0} ⇒ ≤ 1`; splits because p_s divides a real
   symmetric charpoly (`gramModelReduced_splits`). Boundary: `headTail_boundary_factor` gives
   `charpoly(M_0-prefix) = F·(X p_0 − p_1)`, and the proof of
   `reduced_headTail_boundary_squarefree` uses the pair **(p_{−1}, p_0)** — which I verified is the
   correct pairing: coprimality propagates *backwards* only to (p_{−1}, p_0) via the recurrence step;
   `(p_{−1}, p_1)` alone need **not** be coprime (common factor possible exactly when X | p_1). The
   implementation got this subtle point right.
4. **Exterior stabilization.** `headTail_counts_succ` (monotonicity) + `headTail_counts_bounds`
   (`≤ h+1` each side, tail spectrum in (−2,2) exactly) + `exteriorRootCount_mul` (multiplicities
   retained, F ≠ 0) ⇒ eventual constancy for p_s with bound `C ≤ 2(h+1)`.
5. **Density incl. endpoints.** Exact cosine-grid (`exists_many_grid_points` via an Archimedean/floor
   argument, not a numerical mesh), count sandwich transfer (`reduced_headTail_roots_hit_interval`),
   metric closure (`closed_band_closure_of_interval_hits`) giving both endpoints.
6. **Complex bridge.** `real_complex_normalized_gcd` is proved by Bezout combination + monic uniqueness
   — a genuine coefficient-ring argument, not equal-numerical-roots. Roots transfer as **multisets**
   (`gramModelReducedComplex_roots`), every complex root real, complex exterior counts agree, closed-band
   density transfers via `gramModelReducedComplex_eval_real`. `gramModelReducedComplex_identification`
   matches **any** monic ℂ factorization with initial coprimality; no real-coefficient assumption on p.

**Exact machine checks of the new route** (`evidence/verify_new_route.py`, output `verify_new_route.out`;
sympy, all exact — Sturm counts, no numerics as substitutes): on the **printed (3.2.5) matrices**
(l=1, λ=(3) ε=+1 and λ=(1³) ε=−1), building f_s = det(αI + literal head+path) from the printed head:

- normalized gcd(f_0, f_1) equals the published `C^{(3)} = (α−2)²α²` and `C^{(1³)} = (α−2)²(α+2)³` **exactly**;
- quotients p_0, p_1, p_2 … equal the published `P_5, P_6, P_7` **exactly**;
- literal `p_{−1} = X·p_0 − p_1` equals the recursion-determined `P_4`: `α(α+4)` for (3) and `α−2`
  for (1³) (the (α−2)(α+1) printed in §3.3 is the l=0 (1²) case — an easy transcription trap, resolved);
- p_{−1}…p_8 all squarefree; exterior counts stabilize (constant 1 in both cases); root-hitting probes
  in (−1.9,−1.8), (−0.4,−0.2), (0.2,0.4), (1.5,1.6) all hit;
- c = −1 tail gives the **same** normalized gcd (my first draft of this check was wrong — it negated
  head-internal couplings; fixed to negate path couplings only, matching `headTailMatrix_neg`);
- **synthetic degenerate head** with a repeated eigenvalue of multiplicity 2 decoupled from the attach
  coordinate: g = α² (repeated gcd root retained), all p_{−1}…p_8 still squarefree, exterior counts
  stabilize at 0, density probes hit (s up to 24).

These confirm the closed model's conclusions on printed and adversarial instances, including the
multiplicity-retention claims. They are consistency checks, not proofs; the proof is the Lean replay.

## Gate 3 — FORMAL: PASS (fresh strict replay, own lane)

- Copied exact frozen bytes to `frozen/` (33/33 hashes match `bridge-review-hashes.json`; parent tree
  clean at 60ba544d47).
- Fresh strict replay via the **copied** `verification/verify_candidate.py` with
  `--lean-bin …/lean-4.34.1-linux/bin/lean` and `--packages …/2026-10-14/formal/.lake/packages`:
  **PASS, 190 declarations, 22 modules**, pins enforced (Lean 4.34.1, mathlib d13f23b7 + 8 deps
  revision- and dirtiness-checked), `warningAsError=true`, forbidden-token scan enforced by the script.
  Receipt: `frozen/build/verified/audit.json`, SHA-256
  `304181ca9d2783dff183d0f9cfaa8347a1718aebf81dc311989ac6eaf59ab74c` — **byte-identical** to the
  parent's `partial190-audit.json`; my `Checks.log` is byte-identical to the parent's retained
  `partial190-Checks.log` (deterministic replay; the retained logs are genuine, not fabricated).
- I read **all 190 declaration types and axiom reports** from **my own** successful replay log
  (`frozen/build/verified/Checks.log`): 184 declarations depend on `[propext, Classical.choice, Quot.sound]`;
  6 (`lastFirstEquiv`, `lastFirstEquiv_inr`, `headTailSplitEquiv`, `pathBorder`, `pathBorder_last_last`
  and one `hermitian_upper_band_charpoly_squarefree_any_dimension`-adjacent equiv helper family — precisely
  the equiv/`Fin`- plumbing helpers) on `[propext, Quot.sound]` only. **Axioms ⊆ standard 3**; no `sorry`,
  `admit`, custom `axiom`, `unsafe`, or `native_decide`.
- Closed endpoints verified as stated: `gramModelReduced_root_distribution` and
  `gramModelReducedComplex_root_distribution` take **only** `G.IsHermitian` — no residual
  factorization/coprimality/cyclicity/rank premises. Main theorems in `candidate.json` all present
  (script enforces `main_theorems ⊆ inventory`, no duplicates).
- Root-count definitions read: literal root **multisets** with multiplicity, strict inequalities,
  exterior = outside the **closed** band. No surrogate lists.

## Gate 4 — SOURCE-SCOPE / CERTIFICATE: HOLD

**Question 1 (universal model vs source instance).** The closed model quantifies over every finite real
symmetric head, so it is *logically* stronger than any per-partition statement: **mathematically**, if
the source's own proved equations (3.2.3), (3.2.4)/(3.2.17), Proposition 3.25 and reducedness hold —
and I verified they do — then for each (l, λ) the reordered frozen mixed Gram head is a legitimate `G`,
the factorization `det Γ_{(N',N+s)} = F·P_{N+s}` with `F = C^{(λ)}·(P_N)^{d−1}` monic and
`P_N, P_{N+1}` coprime satisfies exactly the hypotheses of
`gramModelReducedComplex_identification`, and the three conjecture clauses follow with **no additional
mathematical step** (the k=−1 boundary included, via the literal `X·p_0 − p_1`). I re-derived this
composition and machine-checked it on printed instances. There is no hidden premise and no
representation-theoretic assumption inside the closed model.

**However, as a formal certificate of the *exact* all-partition source theorem it is not yet complete.**
The Lean corpus contains no Specht-partition type, no construction of the mixed Gram matrix Γ_{l,n},
and no Lean statement of `P^{(λ)}_n`; hence `∀ l, ∀ λ ⊢ l+2, …` cannot even be *stated*, let alone
concluded, in the current formalization. Under the campaign's axiom discipline (⊆ standard 3), the
source facts cannot be imported as axioms. The missing endpoint is precisely:

> **Missing instance layer** (formal-scope, not math): for each (l, λ) — or for a formalized universe of
> partitions — a Lean construction (or faithful encoding) of (i) the frozen head matrix
> `G_{l,λ} : Matrix (Fin m) (Fin m) ℝ` (the constant part of Γ_{(N,…,N)} with the varying tail's
> attach coordinate placed last — an explicit `Equiv`-reindex, determinant-invariant), (ii) the border
> extension equation matching `headTailMatrix_succ_border` for its unit tail (from (3.2.17)), (iii) the
> factorization `(gramModelDeterminant m G_{l,λ} s).map ofRealHom = F · P_{N+s}` with `F` monic and
> `P_N, P_{N+1}` coprime (from Proposition 3.25 + (3.2.12) ramping), and (iv) the boundary identification
> `P_{N−1} = X·P_N − P_{N+1}` (from (3.2.9)/Remark 3.33). Composed with
> `gramModelReducedComplex_identification` and `gramModelReducedComplex_root_distribution`, this yields
> the literal Conjecture 4.5.1 endpoint. Items (ii)–(iv) are *source-established theorems*, not new
> hypotheses of the conjecture, and should **not** be re-proved from scratch — but under this campaign's
> standard they must be *instantiated in Lean* (or the contribution repositioned as the universal model
> theorem plus a conditional corollary), not silently assumed.

This is a **formal-scope gap, not a math gap and not an exposition gap**: no step of the mathematical
argument is missing; what is missing is the Lean object that makes the universal statement apply to the
source's actual family. I do **not** demand re-proof of upstream source results (Prop 3.25, Thm 3.19,
(3.2.12) reducedness) — they are dependencies of the conjecture, proved in the source, and re-proving
them would be an unnecessary Tier-2 representation-theory project unless the campaign wants a
self-contained packet.

**Question 2 (complex bridge).** Inspected: implemented, genuine, sufficient (see Gate 2 item 6). No
assumed real coefficients anywhere in the complex identification theorem.

**Question 3 (source dependencies).** Using Prop 3.25 / reducedness / (3.2.17) as *source dependencies*
is legitimate and I do not count them against the math. The HOLD above is solely about their absence as
Lean instances.

**Question 4 (classical tools).** Confirmed: all spectral/gcd/Chebyshev ingredients are classical; the
parent credits none of them; the generic model itself is **not** claimed or counted as a discovery. Agreed.

## Gate 5 — NOVELTY: PASS (bounded, serious)

Fresh searches (Exa-backed; my own, not inherited):

- **arXiv 2512.24535**: v1 only (31 Dec 2025). **OpenAlex: cited_by_count = 0** (my API fetch);
  Semantic Scholar Graph API rate-limited (HTTP 429) — citation cross-check from OpenAlex and search
  snippets only. MathDB 372352: still **open**, 0 solutions, 0 lean (my live API fetch).
- **Author follow-ups**: Martin's April 2026 arXiv:2604.02989 (2-tonal/even partition algebras
  semisimplicity) cites the KY algebras only as related context; it does not touch Gram determinants,
  P^{(λ)}_n, or the conjecture. No Morris/Martin KY root-distribution follow-up found.
- **Nearest classical bodies** (compared at primary level): Simon's Jost-function program for Jacobi
  matrices with finitely-perturbed parameters (math.caltech.edu/SimonPapers/302), inverse problems for
  Jacobi operators with finitely supported perturbations (arXiv:2206.06242), MFAT 2015 explicit Weyl
  representation for finitely perturbed Jacobi matrices, perturbed Jacobi-matrix-sequence asymptotics
  (J. Approx. Theory 2006). These establish mechanism-level facts about **infinite** operators and
  parameter sequences (essential spectrum [−2,2], finitely many exterior eigenvalues, simplicity) but —
  in the bodies I could access — **none states the reduced-quotient squarefree clause, the normalized-gcd
  identification, or anything about the KY series**. The application is therefore not an *explicit*
  classic corollary; whether it is "immediate" to an expert is a judgment call, but under the strict
  standard (actual primary bodies stating/subsuming it) it is not subsumed. The mechanism itself is
  classical and uncredited by design.
- No empty-citation inference is made: eligibility rests on the source PDF (open conjecture, no resolution
  reported), the live MathDB record, and the citation/author searches above.

**Access limits**: Semantic Scholar 429 (twice, including the preliminary review's attempt); no
MathSciNet/DBLP/INSPIRE/Google-Scholar sweep; MathDB read via API JSON (site 403s plain fetches);
Zentralblatt not checked. Within these limits: no prior resolution, no later resolution found.

## Gate 6 — ELIGIBILITY: PASS but not countable yet

- Exactly **one** prospective outcome: full resolution of Conjecture 4.5.1 for all l ≥ −1, all
  λ ⊢ l+2, all three clauses, k ≥ −1. Nothing is counted per-clause or per-helper. The generic model,
  classical tools, and the complex bridge earn nothing separately (agreed and enforced here).
- Because Gate 4 is HOLD, the outcome remains **prospective**: credit 0, tally 16/30 untouched, no
  ledger change, no candidate-credit.

## Decisive objections (blocking) vs non-blocking notes

**Blocking (must be addressed before any count):**

- **B1 (the HOLD)**: no Lean instance of the source family; the exact all-partition statement is not
  statable in the current formalization. Required: the instance layer of Gate 4 — or an explicit,
  campaign-sanctioned repositioning of the contribution (universal model + conditional source corollary)
  agreed with the count owner. Until then this candidate cannot be promoted to a counted discovery.

**Non-blocking notes:**

- N1: The `(p_{−1}, p_0)` coprimality pairing in the boundary squarefree proof is load-bearing and
  correct; `(p_{−1}, p_1)` would not be derivable in general. Worth one sentence in the paper.
- N2: The exterior bound `C ≤ 2(h+1)` is loose but valid; the conjecture needs only "eventually fixed".
  No explicit stabilization index is produced (inherent, matches the conjecture's phrasing).
- N3: The printed (3.1.1) plus-sign typo and the (1²)-vs-(1³) `P_4` values near Remark 3.33 are
  transcription traps; the formalization and GRAM-PROOF.md use the correct minus convention and correct
  initial conditions. Flag both in the paper.
- N4: The reordering putting the attach coordinate last is a permutation similarity; the paper should
  state it once (determinant invariance) since the model's head convention depends on it.
- N5: `candidate.json` "formal_declarations: 190" and module list match the replay exactly.
- N6: Provenance's warning on MathDB companion grouping is confirmed by my live fetch.

## Required next steps (for the parent, in order)

1. Address B1: build the source-instance layer (or obtain an explicit ruling that the conditional
   framing is the counted form), then **author the paper**.
2. Obtain **final review** (fresh reviewer, own lane) of the paper + instance layer.
3. Build the packet with fresh extraction/replay; only then may any count be proposed.
4. No edits to reviewed frozen bytes; no ledger/count changes from this review.

## Evidence inventory (this lane)

- `frozen/` — byte-identical copy of the 33 reviewed files; hash verification output in `provenance.json`.
- `frozen/build/verified/{audit.json,Checks.log}` — my fresh strict-replay receipt and full
  190-declaration type/axiom log (byte-identical to the parent's retained `partial190-*`).
- `sources/2512.24535.pdf` — my independent fetch, SHA matches; `sources/abs.html` — version history.
- `sources/372352-live.json` — my live MathDB API fetch (open, 0 solutions, 0 lean).
- `evidence/verify_new_route.py`, `evidence/verify_new_route.out` — exact symbolic checks of the new
  route on printed (3.2.5) instances (λ=(3), λ=(1³)) and a degenerate synthetic head, plus c=−1 check.

— Review sub-agent, lane pi-kadar-yu-bridge-review
