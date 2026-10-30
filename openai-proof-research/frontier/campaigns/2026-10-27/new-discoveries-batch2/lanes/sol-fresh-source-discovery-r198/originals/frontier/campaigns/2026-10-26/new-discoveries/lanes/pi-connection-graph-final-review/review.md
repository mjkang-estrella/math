# Final independent adversarial review — strict connection–Dirac spectral dominance (dimension ≤ 1)

Reviewer: pi (final review sub-agent), 2026-10-26. Work performed solo; no children; no git
staging/commits; no shared-ledger or other-lane edits; no external communications, posts, or uploads.
Scope: this lane (`pi-connection-graph-final-review`) only. Object reviewed: an exact-bytes copy of the
frozen candidate `../parent-connection-graph` at frozen-review commit `2cdef2e5fb`
(frozen-review.json byte-verified in this lane), copied to
`pi-connection-graph-final-review/candidate-copy/`. The preliminary review in
`../pi-connection-graph-preliminary-review` was read as background only; none of its conclusions
was taken on faith — every gate below was re-established independently.

Proposed result: ONE general infinite-class theorem — every nonempty finite abstract simplicial
complex whose faces have cardinality 1 or 2 (equivalently: any finite simple graph taken as its
vertex-and-edge complex, isolated vertices and disconnected graphs allowed, no clique filling) has,
for every 1 ≤ k ≤ (number of faces),

    S_k(L) − S_k(D) ≥ √2 − 1 > 0,

with L the literal simplex-intersection connection matrix and D the literal signed boundary Dirac
matrix. Explicitly NOT claimed: the full higher-dimensional MathDB 372758 / Knill 2601.18071v2
Conjecture 1; anything about g = L⁻¹ or spectral radii (the known George 2-skeleton-of-K5
counterexample territory); optimality of the constant.

## GATE VERDICTS

| Gate | Verdict | One-line basis |
|---|---|---|
| SOURCE | **PASS** | Frozen v2 PDF/TXT verified against provenance hashes; live arXiv refetch confirms v2 (29 Jul 2026) is still latest; Conjecture 1, §1.1–1.7, §5.1–5.5, §10 visually inspected on rendered pages; live MathDB 372758 matches frozen copy, still open, 0 formalizations. |
| MATHEMATICS | **PASS** | Every step of the variational proof independently re-derived (§3 below); no holes; degenerate cases (m=0, isolates, k>v, repeated eigenvalues) each handled. |
| FORMAL | **PASS** | Fresh isolated strict replay on my own copy: 211/211 declarations in 17 modules, warningsAsError, only propext/Classical.choice/Quot.sound, no forbidden tokens; all 23 frozen hashes byte-verified; all 211 types and axiom reports inspected by me; endpoint is the closed literal face-family statement. |
| NOVELTY / ELIGIBILITY (serious bounded) | **PASS (bounded)** | Independent refetches: Semantic Scholar shows 0 citations of 2601.18071; arXiv API searches for the comparison find only the source itself; Knill's homepage lists no later resolution; no known theorem states or immediately implies the graph-case all-k L-vs-D signed comparison. |
| MANUSCRIPT | **PASS** | main.tex ↔ paper.pdf textually identical, built with exit 0; all 3 rendered final pages personally inspected at 110 dpi; no clipping, overlap, unresolved references, or overclaims found. |

**Overall: ELIGIBLE** as ONE prospective general theorem (the full dimension-at-most-one case of
MathDB 372758, proved with a uniform strict gap √2−1 that the conjecture itself does not ask for).
No decisive objection found. Credit remains 0; acceptance and tally are the parent's prerogative.

## 1. SOURCE gate — PASS (evidence)

- `candidate-copy/sources/*` SHA-256 recomputed: all five match `provenance.json` exactly
  (2601.18071 pdf/txt, 1803.01464 pdf/txt, 372758-live.json).
- **Live refetch (independent of frozen copies):** arXiv abs page confirms v2, Wed 29 Jul 2026, is
  the latest version (v1: 26 Jan 2026); no v3. The v2 stamp on the frozen PDF ("2601.18071v2
  [math.CO] 29 Jul 2026") matches.
- **Visual inspection of the primary:** page 1 rendered and read — D = d + d* with
  d(x,y) = sign(x,y) when |x|,|y| differ by 1 and y ⊂ x; L(x,y) = 1 iff x ∩ y ≠ ∅ (so L has 1 on the
  diagonal); "For 1-dimensional complexes, L − L⁻¹ = |D|²" (the sign-less Hodge reading per [15]).
  Page 9 rendered and read — §5.1 defines S_k(A) = λ₁+…+λ_k for eigenvalues ordered decreasing,
  all 1 ≤ k ≤ n, multiplicities included, negative eigenvalues included; §5.3 states the conjecture
  is unproved ("we can not prove it yet"); Conjecture 1 verbatim: "If L is the connection matrix and
  D the Dirac matrix, then L − D satisfies S_k(L) ≥ S_k(D)." §5.4–5.5 contain only failed attempts
  (Fan's theorem, Schur bounds) — no graph-case proof anywhere in the paper.
- **Live MathDB** (https://mathdb.com/api/posts/372758, fetched 2026-10-27): status "open",
  post_type "conjecture", lean_formalization_count 0, no solutions/replies/progress; statement is
  exactly the S_k array form for every finite abstract simplicial complex. Byte-identical in all
  material fields to the frozen `372758-live.json`.
- **Hydrogen credit check:** 1803.01464 page 4 rendered and read — Theorem 1 (Hydrogen relation):
  "For any finite simple graph, |H| = L − L⁻¹" with |H| the sign-less Hodge Laplacian from the
  unsigned incidence matrix, L the connection matrix (L(x,y)=1 iff x∩y≠∅). This is precisely the
  identity the candidate credits; it compares L with the *sign-less* |H|, never with the *signed* D.
  The only Dirac mentions in 1803.01464 are a definitional passage and a figure caption; no
  partial-sum comparison exists there.
- **Scope fidelity:** Knill's complexes are finite sets of nonempty sets closed under nonempty
  subsets (the empty face is excluded — otherwise L would be singular, contradicting §1.4). The
  formal hypotheses (F nonempty; downward closure for nonempty subsets; all faces of size 1 or 2)
  match exactly. The formal D uses the canonical orientation (smaller endpoint −1); any orientation
  is a diagonal ±1 conjugation of it, preserving the spectrum, so the canonical instance proves the
  source statement (which is orientation-invariant). This is a scope note, not a defect.
- **Known counterexample attribution:** the 18 July 2026 v2 update attributes to Robert J. George
  the 2-skeleton of K5 refuting Question C (spectral radius of g = L⁻¹). The candidate claims no
  credit for this and the theorem does not involve g or radii. Consistent.

## 2. FORMAL gate — PASS (evidence)

- **Frozen-hash verification (exact bytes):** all 23 entries of frozen-review.json recomputed by me
  over `candidate-copy/` — 17 modules, main.tex, paper.pdf, PROOF.md, FORMAL-PROGRESS.md,
  provenance.json, verification/complete-audit.json — **23/23 OK**.
- **Fresh isolated strict replay** on my own copy via
  `NEW/verify_candidate.py candidate-copy --lean-bin …/lean-4.34.1-linux/bin/lean
  --packages …/2026-10-14/formal/.lake/packages` (warningsAsError):
  **PASS, 211 declarations, 17 modules**, dependency revisions checked against pins.json
  (mathlib d13f23b7…), forbidden tokens (sorry/admit/axiom/unsafe/native_decide) absent,
  211/211 axiom reports produced and matched to inventory, axioms exactly
  {propext, Classical.choice, Quot.sound}. Receipt: `candidate-copy/build/verified/audit.json`.
- **All 211 declarations read** (all 17 modules, 2417 lines). Spot-checks that mattered most:
  - *Literal matrices.* `connectionMatrix` is the face-intersection indicator (1 on the diagonal —
    `connection_diagonal`); `connection_eq_blocks` proves it equals [[I,U],[Uᵀ,UᵀU−I]] for simple
    edge sets: for distinct edges (UᵀU)_{ef} ∈ {0,1} so the −I only fixes the diagonal (2−1=1);
    disjoint edges get 0. `diracMatrix` = [[0,C],[Cᵀ,0]] with canonical signed incidence; the
    face-level matrices are proved reindex-equivalent (`spectralTopSum_reindex` via charpoly).
  - *Endpoint.* `source_graph_strict_gap` quantifies over the actual finite face family F
    (nonempty, downward-closed under nonempty subsets, faces of size 1–2) and all 0 < k ≤ F.card;
    matrices are `familyConnectionMatrix F` / `familyDiracMatrix F` (literal, face-indexed). No
    rank, SVD, inertia, or eigenvector-existence premise survives. `GroundSet.lean` restricts to
    `supportVertices F` and `restricted_{connection,dirac}_spectral_sum` transport the spectral
    sums — unused ambient vertices handled; actual signed boundary signs and repeated/negative
    eigenvalues carried through (negative selected D-eigenvalues only decrease the sum;
    `diracPos_orthonormal` handles repeated positive eigenvalues without counting).
  - *No weakened surrogate accepted:* the endpoint is not a block-matrix surrogate; the graph-block
    route is proved *equal* to the literal face matrices (`complex_*_spectral_sum`,
    `face_*_pullback`), and the ground-set restriction is a proved reindex, not a weakening.
  - *D-positive projection.* `DiracPositive.lean` (the implementation lane's file, byte-identical
    per provenance): `diracPos_inner_half` proves ⟨a_i,a_j⟩ = ⟨w_i,w_j⟩/2 for positive eigenvectors
    via adjointness (E1: μ_i⟨a_i,a_j⟩ = ν_j⟨b_i,b_j⟩; E2: ν_j⟨a_i,a_j⟩ = μ_i⟨b_i,b_j⟩; sum ⇒
    equality since μ_i+ν_j > 0), so √2·a_i is orthonormal with H-eigenvalues μ_i² — repeated
    eigenvalues fine, no orthonormality gap.
  - *L-side low bound.* `graph_low_connection_bound`: Ky Fan diagonal (T_k ≤ Σ_{top-k} q_i), the
    normalized lift ((φ(q)+1)u, φ(q)Uᵀu) proved an eigenvector uniformly in q ≥ 0 (uses only
    φ² = qφ+1), and q₁ ≥ 2 from a single edge term (z₁ᵀQz₁ ≥ (z_a+z_b)² = 4, ‖z‖²=2) — the Lean
    uses only ≥ 4, so the preliminary review's "always 4" slip is absent from the formal proof.
  - *L-side high bound.* `HighConnection.lean`: L+I PSD via BᴴB+JᴴJ; Σφ(q_i) = 2m+g; Cauchy
    v² ≤ (2m+g)g with mathlib's `sq_sum_div_le_sum_sq_div` (statement checked in mathlib);
    2m+1 ≤ v² from m ≤ C(v,2); g ≥ 1; growth with eigenvalues ≥ −1; diagonal S_k ≥ k;
    linarith combination gives m+v/2+1/2 ≤ S_k(L). All zero-counting premises absent — the
    variational route is genuine, so I do not demand inertia/zero-multiplicity formalization.
- **Parent receipt** `verification/complete-audit.json`: PASS, 211 declarations, module hashes match
  frozen hashes, allowed axioms only. Historical checkpoints 135/161/185 are separate receipts, as
  stated; they play no role in this gate.
- The replay is deterministic on the pinned toolchain; my run was against my own copy in my own
  lane and the parent will extract the packet replay separately (out of my scope).

## 3. MATHEMATICS gate — PASS (independent re-derivation)

I re-derived the whole argument myself before reading the Lean in detail; it is correct:

1. **L blocks.** For Qu = qu, w = Uᵀu/√q: the pair ((φ+1)u, φw) satisfies both block equations of
   [[1,U],[Uᵀ,UᵀU−I]] exactly when φ² − qφ − 1 = 0 (block 1: φ+1+φq = φ²+φ; block 2: (φ+1)+φq−φ =
   1+φq = φ²). Valid at q = 0; nonzero for u ≠ 0 since the vertex part has coefficient φ+1 > 0.
   Orthonormal Q-eigenbasis ⇒ orthogonal lifts (⟨Uᵀu_i, Uᵀu_j⟩ = q_jδ_ij) ⇒ after normalization a
   v-membered orthonormal eigenfamily ⇒ S_k(L) ≥ Σ_{i≤k} φ(q_i) for k ≤ v (Ky Fan). I also verified
   L⁻¹ = [[1−Q, U],[Uᵀ,−1]] by direct multiplication, so L − L⁻¹ = diag(Q, UᵀU) — the credited
   hydrogen identity — though the formal proof never needs it.
2. **Low k.** φ(q) = 1 + q/2 + e(q), e ≥ 0 increasing, e(2) = √2−1; an edge {a,b} gives
   zᵀQz = δ_a+δ_b+2 ≥ 4, ‖z‖² = 2, so q₁ ≥ 2 (Rayleigh); diagonal Ky Fan gives Σ_{i≤k}q_i ≥ T_k.
   Hence S_k(L) ≥ k + T_k/2 + √2−1 for k ≤ v. (Note δ_a+δ_b+2 can exceed 4 — the bound only needs ≥.)
3. **D upper bounds.** For positive eigenvectors w_i=(a_i,b_i): adjointness gives
   μ_i⟨b_i,b_j⟩ = μ_j⟨a_i,a_j⟩ and μ_j⟨b_i,b_j⟩ = μ_i⟨a_i,a_j⟩; adding, (μ_i+μ_j)⟨b_i,b_j⟩ =
   (μ_i+μ_j)⟨a_i,a_j⟩ ⇒ ⟨a_i,a_j⟩ = ⟨b_i,b_j⟩ = δ_ij/2 ⇒ √2·a_i orthonormal, H(√2a_i) = μ_i²·√2a_i.
   No rank or multiplicity count used — repeated eigenvalues fine. Then Σμ_i² ≤ 2T_r (H ≤ 2Δ on
   quadratic forms + Ky Fan diagonal), Σμ_i ≤ √(rΣμ_i²) ≤ √(2kT_k) for k ≤ v; and globally
   2μ ≤ μ²+1, Σμ² ≤ 2m (Bessel per signed-incidence column, each of norm² exactly 2), r ≤ v
   (linear independence in R^v) ⇒ S_k(D) ≤ m+v/2 for all k ≤ v+m.
4. **High k.** xᵀ(L+I)x = ‖a‖²+‖a+Ub‖² ≥ 0 ⇒ eigenvalues of L ≥ −1. g = Σ1/φ(q_i) > 0;
   Σφ(q_i) = 2m+g; Cauchy v² ≤ (2m+g)g; 2m+1 ≤ v² (m ≤ C(v,2), v ≥ 1); g < 1 would give
   (2m+g)g < 2m+1 ≤ v² — contradiction ⇒ g ≥ 1 ⇒ S_v(L) ≥ 2m+1; growth ⇒ S_k(L) ≥ 2m+v+1−k;
   with S_k(L) ≥ k (diagonal of ones): averaging yields S_k(L) ≥ m+v/2+1/2 (the two bounds sum to
   2m+v+1 ≥ 2(m+v/2+1/2) + … — precisely: both bounds cannot lie below m+v/2+1/2 since their
   deviation sum is m ≥ 0). Gap ≥ 1/2 > √2−1 for k > v.
5. **Degenerate cases.** m = 0: L = I, D = 0, gap = k ≥ 1. Isolated vertices: degree-0 entries and
   q = 0 eigenvalues flow through every inequality (φ(0) = 1). Disconnected graphs: the argument
   never uses connectivity. Nonempty complex ⇒ v ≥ 1 (formally derived in `supportVertices_nonempty`).
6. **Independent numerics (my own code, written from the literal face definitions, not the parent's
   check_graphs.py):** 3000 seeded random graphs v ≤ 9 + 1000 isolate-heavy/disconnected complexes;
   literal face-intersection L and canonical-boundary D built from faces; all k = 1..|F| checked
   against √2−1: **0 violations; minimum observed gap 1.0** (single edge, k=1: λ₁(L) = 1+√2,
   λ₁(D) = √2). Exact single-edge and triangle-boundary spectra match the paper's claims
   (L pos. spec. {φ(q_i)}, D = ±√3 pairs + zeros for the triangle boundary).

The two preliminary-review slips were re-verified as corrected and non-load-bearing: single-edge
gap is exactly 1 (not from "2 and 1"), and ‖Uᵀ(e_i+e_j)‖² = δ_i+δ_j+2 ≥ 4 with equality only when
both degrees are 1 — the Lean uses only ≥ 4.

## 4. NOVELTY / ELIGIBILITY gate — PASS (serious bounded search)

Independent searches (this reviewer; the preliminary reviewer's searches were not reused):
- **Citations of the primary:** Semantic Scholar citations endpoint for arXiv:2601.18071 — **0
  citations**. No citing follow-up can contain the endpoint.
- **arXiv API:** "weak Loewner"+"Dirac" — 1 hit, the primary itself. "connection Laplacian"+"Dirac"
  (recent first) — 8 hits, none comparing L and D spectra besides the primary. "Dirac matrix" +
  "simplicial complex" + "spectral sum" — 0 hits.
- **Author follow-ups:** Knill's Harvard homepage post list through Fall 2026 — only
  "Connection and Dirac matrices [ArXiv]" (the primary) touches the topic; the two later 2026
  preprints (2607.24322, 2608.06405) verified off-topic by abstract.
- **Live MathDB** still open with 0 formalizations (fetched 2026-10-27).
- The primary's own attempts (§5.4–5.5) provably do not reach even the graph case; its theorems are
  individual-eigenvalue bounds λ_j ≤ d_j, not partial-sum comparisons. The hydrogen identity
  compares L to the sign-less |H|, not the signed D; bridging requires exactly the candidate's
  H ≤ 2Δ + Ky Fan + scalar chain, so the result is not an immediate corollary of any single known
  theorem I could locate.

**Bounded-search caveats (honest):** no general web-search provider was available in this
environment; coverage is arXiv API, Semantic Scholar, MathDB live, and the author's homepage. I
cannot exclude unindexed venues, very recent private notes, or non-indexed blogs. No absolute
priority claim is made or needed; the campaign standard asks for a serious bounded search, which
this is. **Eligibility:** infinite class (all finite graphs/1-complexes), all k, uniform constant;
not a finite check; not a reformalization; strictly stronger than the bare conjecture (positive
gap); correctly excludes g/radius credit; correctly does not claim the higher-dimensional case.

## 5. MANUSCRIPT gate — PASS

- `paper.pdf` and `build/main.pdf` textually identical; both from frozen main.tex
  (sha ac4bb3…); build receipt exit 0, no issues.
- All 3 final rendered pages (build/final-page-{1,2,3}.png) personally inspected: title/abstract/
  Theorem 1 correct and match the formal endpoint; equation chains (1)–(7) match the Lean proof
  steps; §5 scope paragraph accurately describes the endpoint, replay, and credits; references
  correct (K26 = 2601.18071v2, K18 = 1803.01464); no clipping, overlap, or unresolved references.
- Overclaim scan: abstract and body say "dimension-at-most-one case", "no optimality is asserted",
  higher-dimensional conjecture "remains outside the result"; no credit claimed for hydrogen/
  Ky Fan/incidence ingredients; no g/radius statements. Consistent with the campaign standard.

## Decisive objections

**None.** I could not break the mathematics, the formalization, the source attribution, the
manuscript, or the bounded novelty claim.

Non-blocking notes (for the parent's integration record):
1. The constant √2−1 is provably loose: observed infimum over my numerics is 1.0 (single edge,
   k = 1). The candidate correctly asserts no optimality. A gap-≥1 strengthening would need a new
   argument and must not be claimed.
2. The formal endpoint fixes the canonical edge orientation. Orientation-independence of S_k(D) is
   argued in the paper (diagonal ±1 conjugation) but is not itself formalized; this is harmless
   because the source's conjecture is orientation-invariant and the canonical orientation is an
   instance of it. If the parent ever wants the literal "for every orientation" quantifier, that is
   an optional formal add-on, not a gap in the source claim.
3. The strict replay is toolchain-pinned (Lean 4.34.1, mathlib d13f23b7); determinism claims hold
   for that pin. The extracted-packet replay remains the parent's step.
4. Access limits: no general web-search provider in this environment (enumerated searches above);
   novelty confidence is bounded accordingly, per campaign standard.

## Verification artifacts in this lane

- `candidate-copy/` — exact-bytes copy of the frozen candidate (all 23 frozen hashes verified).
- `candidate-copy/build/verified/audit.json` — my fresh isolated strict replay receipt
  (PASS, 211 declarations, allowed axioms only).
- `/tmp/my_check.py` output recorded below (my independent numerical probe; 0 violations, min gap 1.0).

Replay command and result (my lane):
`python3 verify_candidate.py lanes/pi-connection-graph-final-review/candidate-copy --lean-bin …/lean-4.34.1-linux/bin/lean --packages …/2026-10-14/formal/.lake/packages`
→ {"status": "PASS", "declarations": 211, "axioms": ["Classical.choice", "Quot.sound", "propext"]}.

## Gate tally contribution

This review contributes FIVE gate evaluations (SOURCE, MATHEMATICS, FORMAL,
NOVELTY+ELIGIBILITY, MANUSCRIPT) — all PASS. No acceptance, count, ledger, or paper changes made;
the parent integrates and extracts the packet replay.
