# Independent adversarial review — WGM parity candidate

Reviewer lane: `lanes/pi-wgm-parity-review`. Worked SOLO, no children, no shared edits,
no git actions, no ledger changes. Reviewed frozen parent commit bytes in
`frozen/` (copied from `lanes/parent-wgm-parity`, all 34 `review-hashes.json`
entries verified against the copy before any work).

**Candidate:** positive integer weights with odd sum S force L(s) ≥ m in Wang's
simple SOC representation (Definition 3.1), answering Wang 2024, Section 7,
open problem (2), p. 1512. MathDB 349081 (bivariate cardinality) is already
resolved by Wang's Corollary 4.5 and is explicitly not counted here.

## Verdict per gate

| Gate | Verdict |
|---|---|
| SOURCE | **PASS** |
| MATH | **PASS** |
| FORMAL | **PASS** |
| NOVELTY + ELIGIBILITY | **PASS** (bounded screen, recorded limits, no EXCLUDE grounds) |
| MANUSCRIPT | **PASS** |

Overall: **no decisive finding against the candidate**; eligible, credit 0
pending parent packet assembly and extracted replay. Nonblocking findings listed
at the end.

---

## 1. SOURCE — PASS

- Independently fetched the actual published author PDF
  `https://wangjie212.github.io/jiewang/research/wgm.pdf`. SHA-256 of my fetch:
  `088c131e9b3d55a366ec3010d48dd0431700f0cf85411907fdfe2c3774357fd6` — identical
  to the frozen `sources/wang-wgm-published2024.pdf` and to the required hash.
- Visually read (my own renders, `logs/page-4/6/9/23`):
  - **Definition 3.1, p. 1493:** representation = quadratic inequalities
    `x_{i_k} x_{j_k} ≥ x_{m+k}²`, k = 1..n, inputs `i_k, j_k ∈ {1,…,m+n}`
    (arbitrary; cycles, repeats, self-references allowed), `x_{m+2..m+n}` are
    n−1 auxiliary nonnegative variables, size n, `L(s_1,…,s_m)` = optimal size,
    equivalence (3.1) with `x_{m+1}^{ŝ}`.
  - **Theorem 3.6, p. 1495:** primitive tuple ⇒ L ≥ m−1.
  - **Corollary 4.5, p. 1498:** `L(q, p−q) = ⌊log₂ p⌋` for 0<q<p coprime —
    confirms the old MathDB-349081-type bivariate conjecture is resolved by the
    same paper (correctly uncounted).
  - **Section 7 (2), p. 1512, verbatim:** "We have proved L(s₁,…,s_m) ≥ m−1 in
    Theorem 3.6. On the other hand, we observed that for the tested examples the
    lower bound m−1 is attained only if ŝ is even. Is this always true? Can we
    prove L(s₁,…,s_m) ≥ m given that ŝ is odd?" — exactly the candidate's target.
- arXiv 2206.05924 latest version rechecked: **v4, announced Wed, 31 Jan 2024**.
  Published 2024 SIAM body is the authoritative source.
- Semantic fidelity of the encoding (checked by reading all Lean files against
  Definition 3.1): `SourceRepresentation` is the standard projection semantics —
  for all nonnegative terminals x and t, the inequality holds iff **∃** internal
  values z ≥ 0 with `z root = t` and all constraints `z_i² ≤ v_{c(i,0)} v_{c(i,1)}`.
  Constraint i has RHS z_i² (paper: x_{m+k}² for constraint k) and inputs range
  over all m+n variables (`Fin m ⊕ Fin n`) exactly as in the paper. The endpoint
  assumes the full equivalence, and the proof uses only soundness, which is the
  weaker direction — no fidelity gap either way. n ≥ 1 encoded by `root : Fin n`;
  m = 0 collapses to a vacuous/non-odd case. No numerical surrogate, no hidden
  residual-flow or acyclicity hypothesis anywhere in the statement.
- Note: Definition 3.1's display (3.1) is read by the campaign as projection
  semantics; the theorem is proven under soundness alone, so it holds under
  either the projection or the universal reading of the equivalence. No gap.

## 2. MATH — PASS (independent derivation + independent computation)

I re-derived every load-bearing step myself rather than trusting PROOF.md:

1. **Terminal reachability from soundness.** If terminal j were unreachable,
   the 0/1 assignment (reachable = 1, else 0) satisfies every constraint
   (reachable internals have both children reachable ⇒ equality; unreachable
   internals have RHS 0 ≤ nonnegative product), output 1, but x_j = 0 < s_j-th
   power in the product with s_j > 0 — contradiction. ✓ (Requires L nonempty;
   m = 0 is vacuous since S = 0 is not odd.)
2. **Counting.** Every reachable vertex except the root is hit by a child slot
   of a reachable internal vertex (last edge on a shortest path). So
   m + R − 1 ≤ 2R, m − 1 ≤ R ≤ n. This is the old bound, without irredundancy. ✓
3. **Equality case n = m−1.** Then R = n = m−1, all vertices reachable; the map
   (2n child slots) ∪ {one extra slot for the root} onto the m+n = 2n+1 vertices
   is a surjection between finite sets of equal size, hence a bijection:
   child map injective, every nonroot vertex used exactly once, root never an
   input. ✓
4. **Invertibility.** M = 2I − A with column sums of A ≤ 1 (also handles
   self-loops A_{jj}=1). If M^T w = 0 then 2w_j ∈ {0} ∪ {single entries of w};
   a maximum-|·| entry gives 2max ≤ max ⇒ w = 0. ✓ (Lean proves the equivalent
   kernel statement for M directly via `inputFlow`; argument is the same.)
5. **Exact log equality.** For any u, z := M⁻¹Bu gives an exponential assignment
   satisfying all constraints with equality (Mz = Bu ⇔ 2z_i = sum of child
   values' logs). Soundness gives S z_r ≤ s·u; applying to −u gives equality for
   all u, hence `t := S e_r^T M⁻¹` satisfies t^T M = S e_r^T and t^T B = s^T,
   i.e. q_i = s_j on terminal children, q_i = 2q_j on internal children (j ≠ r),
   2q_r = S. No flow positivity used. ✓
6. **Integrality obstruction.** D = {i : q_i ∉ ℤ}. A child of i ∈ D cannot be
   terminal (would force q_i = s_j ∈ ℤ); if internal j then j ∈ D. Injectivity
   restricts to an injection D×{0,1} → D; finiteness gives 2|D| ≤ |D| ⇒ D = ∅.
   So q_r ∈ ℤ and S = 2q_r is even — contradiction. Hence n ≥ m. ✓ gcd 1 is
   indeed never used; the theorem is stronger than the asked statement.
7. **Coherence check of the flow object.** By Farkas' lemma, soundness on
   strictly positive inputs is *equivalent* to feasibility of
   `∃ q ≥ 0: 2q_j − Σ_{slots→internal j} q_i = S δ_{j,root},
   Σ_{slots→terminal j} q_i = s_j` — exactly the candidate's flow; extended
   soundness (allowing x_j = 0) adds exactly terminal reachability. The proof's
   "flow" is thus the LP-duality certificate of soundness; the parity argument
   never needs its positivity. This closes the loop between the two readings.

**Independent computational check** (`logs/independent_lp_check.py`,
`independent_lp_check.log`), deliberately different from both the parent's
unordered enumeration and the Lean proof: exact-rational feasibility of my
Farkas flow system over **all ordered** child maps, root fixed at internal 0,
plus reachability; validated in both directions (finds the paper's own Example
3.7 configuration sound; finds explicit violating assignments by randomized
search for flow-infeasible configs; sound configs survive 8k-random searches).

| m, n | weights | sound configs |
|---|---|---|
| 2, n=1=m−1 | (1,2), S=3 odd | **0** ✓ theorem |
| 2, n=1=m−1 | (1,1), S=2 even | 2 (bound attained) |
| 2, n=2=m | (1,2), S=3 | 4 ⇒ L(1,2)=2=m |
| 3, n=2=m−1 | (1,1,1) S=3 odd | **0** ✓ |
| 3, n=2=m−1 | (1,2,1) S=4 even | 4 |
| 3, n=1=m−2 | both | 0 ✓ old bound |
| 3, n=3=m | (1,1,1) S=3 | 48 ⇒ L(1,1,1)=3=m |
| 4, n=3=m−1 | (1,1,1,2) S=5 odd | **0** ✓ |
| 4, n=3=m−1 | (1,1,2,2) S=6 even | 0 (no contradiction: evenness not sufficient) |
| 4, n=4=m | (1,1,1,2) S=5 | 0 (bound not tight here; consistent) |
| 4, n=4=m | (1,1,2,2) S=6 | 288 |

Ordered reach-all counts 2/12/240 = parent's unordered 1/3/30 × 2ⁿ — exactly
consistent with the parent's independent enumeration. My check corroborates the
theorem in all small cases by an orthogonal method.

## 3. FORMAL — PASS

- Copied all frozen bytes to my lane; **all 34 hashes in review-hashes.json
  verify unchanged** (0 mismatches, 0 missing).
- Fresh strict replay from my own copy:
  `verify_candidate.py frozen --lean-bin …/lean-4.34.1-linux/bin/lean
  --packages …/2026-10-14/formal/.lake/packages` →
  **status PASS, 41 declarations, 7 modules**, warnings-as-errors enforced by
  the script, forbidden-token scan (sorry/admit/axiom/unsafe/native_decide)
  enforced and clean, pins enforced (Lean 4.34.1, mathlib d13f23b7 + 8 deps at
  pinned revs, unmodified).
- I read the **complete `Checks.log` of my own replay** (`logs/replay-checks.log`):
  all 41 declaration types printed, all axiom reports either
  `[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms".
  Zero warnings/errors. `WGMParity.source_odd_total_bound` type:
  `(m n : ℕ) → (s : Fin m → ℕ) → (∀ j, 0 < s j) → (root : Fin n) →
  (child : Fin n × Bool → Fin m ⊕ Fin n) → SourceRepresentation s root child →
  Odd (∑ j, s j) → m ≤ n` — exactly the literal source question, no extra
  hypotheses. `odd_total_sound_size_bound` is the stronger soundness-only
  version.
- **Determinism:** my receipt `build/verified/audit.json` is byte-identical to
  the parent's `verification/parent-audit.json`
  (both sha256 `90344f6a…1aa71ce53`); module declaration counts match
  provenance (5/8/6/7/3/6/6 = 41).
- Endpoint and `literalSourceRepresentation` bodies read line by line
  (see §1 fidelity paragraph).

## 4. NOVELTY + ELIGIBILITY — PASS (bounded, honest)

- **Citers.** Independently re-read stored OpenAlex and Semantic Scholar records:
  both list exactly the same 3 citers (Blanco–Martínez-Antón 2024 power cones
  DOI 10.1137/23M1617205; Blanco–Martínez-Antón 2026 extremal mediated graphs
  DOI 10.1007/s10957-026-03048-5, JOTA 210, article 24; Alzalg 2026
  DOI 10.1515/spma-2025-0055).
- **Full-text checks by me:** Blanco 2024 (`power-cones.txt`): zero hits for
  odd/parity/L-bound context. Published JOTA 2026 (`extremal-mediated.txt`):
  zero odd/parity hits; Wang cited only for the mediated-set background and the
  brute-force algorithm (its [30]). **New artifact I retrieved:** the arXiv
  preprint of the same work, arXiv:2502.03288v1 (5 Feb 2025, "Optimal mediated
  graphs", 29 pp., `logs/opt-mediated-graphs.pdf`): zero odd/parity hits; cites
  "Wang, 2024, Corollary 28" only for a nonemptiness sufficient condition. It
  is the same citation corpus, not a fourth paper.
- **Alzalg 2026:** my own attempts to fetch the full text all failed
  (DeGruyter PDF empty/202, AIMS 404, ResearchGate 403). The parent's RG
  transcript read of intro/conclusion/sole-Wang-citation stands; the technical
  algebra body remains unread — **recorded limit**, nonblocking (abstract and
  title indicate algebraic/metric structure of the cone, not representation
  size bounds; no parity claim surfaced in any indexed snippet).
- **Classical subsumption check:** Powers–Reznick "A note on mediated
  simplices" (arXiv 1909.11008 / JPAA 2020) fetched and queried: **no**
  cardinality lower bound, no parity condition — only existence/k≥max{2,n−2}
  dilation results. MMS classification literature: no such bound. A classical
  parity theorem would not have left Wang's 2024 question open.
- **Author follow-ups:** Jie Wang's homepage (papers under review/2026 list)
  contains no mediated-set/SOC-size item; MiniSOC repo unchanged in scope.
- **MathDB:** 349081 live record re-fetched (open, 0 replies/solutions/
  human_solves); my own probes confirm the listing API ignores `q`/`search`
  parameters (identical payloads with a bogus query) — the parent's "failed
  search ≠ successful search" note is accurate. No post on Wang Section 7(2)
  identified.
- **Eligibility under the strict source-question standard:** the source question
  (Section 7(2)) is informal in wording but explicit, precise, and unambiguous;
  it is a *different, later* question than MathDB 349081 (which Wang's own
  Corollary 4.5 resolves). The candidate answers it rigorously and proves a
  strictly stronger statement (all positive integer weights with odd sum, no
  primitivity). No post/citation inference was needed. **No EXCLUDE grounds.**
- No MathSciNet/zbMATH sweep (no access); no absolute priority claim made or
  needed.

## 5. MANUSCRIPT — PASS

- Frozen `paper.pdf` sha256 `3ed2fef7…89d95a0a7c` matches the required hash;
  2 pages.
- Clean rebuild from frozen `main.tex` with the pinned Tectonic
  (`…/t088p133-manuscript-r1/tools/tectonic`): exit 0, 2 pages, same byte size
  (52.0478515625 KiB). My PDF hash `fa681a25…c15f4262` differs from the frozen
  one **only** in the embedded random `/ID` (verified: no CreationDate/Producer
  deltas); extracted text byte-identical; rendered pages at 105 dpi
  **pixel-identical** to the frozen paper (both pages).
- Visual inspection of both my rendered pages: no clipping, overlap, or
  unresolved references; bibliography [1–3] correct (Wang SIAM J. Optim. 34
  (2024) 1490–1514 DOI 10.1137/22M1531257; Blanco–Martínez-Antón SIAM J. Optim.
  34 (2024) 3088–3111 DOI 10.1137/23M1617205; JOTA 210 (2026) article 24).
- Every display recomputed by hand against the frozen Lean statements:
  (1) gm inequality with exponent S ✓; (2) `y_i² ≤ v_{c(i,0)}v_{c(i,1)}` ✓;
  counting `m+R−1 ≤ 2R`, `m−1 ≤ R ≤ n` ✓; `n=R=m−1` step ✓; M=2I−A, column
  sums ≤ 1, max-norm invertibility ✓; `Mz=Bu` equality assignment ✓;
  `S z_r ≤ Σ s_j u_j` and two-sided equality ✓; `M^T q = S e_r`, `q^T B = s^T`
  (checked via `q^T B u = (M^T q)^T M⁻¹Bu… = S z_r = s^T u`) ✓;
  equations (3)(4)(5) ✓ with `j ≠ r` in (4) ✓; doubling injection D×{0,1}→D ✓.
  The paper's "soundness and strict monotonicity of the exponential" phrasing
  is fine (the Lean proof uses soundness at exponential assignments directly).
- Scope statements correct: 41 declarations/7 modules, Lean 4.34.1, mathlib
  d13f23b7, standard-3 axioms, endpoint name correct; 22,183 unordered
  configurations figure matches the parent's enumeration and my orthogonal
  ordered check is consistent with it; draft correctly says independent review
  and packet acceptance pending; **credit 0**, no claim of acceptance, no
  MathDB-349081 credit, no priority claim.

## Findings

**Decisive:** none.

**Nonblocking:**
1. Alzalg 2026 full technical body unread (publisher 202/404, RG 403 —
   reconfirmed by my own attempts). Retain as recorded limit in the packet.
2. arXiv:2502.03288 (preprint of Blanco–Martínez-Antón 2026) was not in the
   frozen source set; I retrieved and checked it (no parity content). Parent may
   add it to the packet for completeness; hash in my provenance.
3. Paper.pdf byte-reproducibility is limited to the Tectonic-embedded `/ID`;
   content is bit-stable by text extraction and pixel rendering. No action.
4. My independent ordered enumeration also shows L(1,1,1,2) > 4 (no sound size-4
   config) — the bound is not always tight for odd S; irrelevant to correctness,
   optionally worth a phrase in a future revision, not in the frozen draft.
5. The paper's phrase "Soundness and strict monotonicity of the exponential"
   slightly overstates the mechanism (soundness at exponential assignments
   suffices; monotonicity is not invoked); harmless, matches PROOF.md logic.

## Procedural compliance

Solo, no subagents; all writes confined to `lanes/pi-wgm-parity-review/`
(`frozen/` byte copy, `logs/` evidence, this review, `provenance.json`);
no git staging/commits; no shared or other-lane edits; parent untouched during
review; ledger/counts unchanged. The parent must read this review, assemble the
deterministic packet, and perform a fresh extracted replay before any credit.
