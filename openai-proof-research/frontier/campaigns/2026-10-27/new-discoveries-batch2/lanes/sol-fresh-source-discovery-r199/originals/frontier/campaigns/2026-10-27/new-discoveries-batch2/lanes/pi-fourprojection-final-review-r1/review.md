# Independent final review: four-projection complete candidate

Reviewer lane: `pi-fourprojection-final-review-r1` (Pi GLM 5.3 Flash, thinking high, standard speed). Solo, no children. Review date: 2026-10-28 UTC.

Subject: frozen lane `root-fourprojection-complete-r1` at commit `a81ca96d98`. I made my own byte copy of the entire lane **from git commit `a81ca96d98`** (not from the live directory, where root's fresh replay 62780 was running) and verified all **35 core hashes** in `final-review-hashes.json` against it: **35/35 match before and after** my review (re-verified at close; zero drift). I did not modify any frozen byte, the root lane, shared files, or other lanes. No acceptance, count change, or commit is made here.

Verification performed (all inside my lane, fresh isolated code paths):

1. `own_checker.py` — my own implementation, not the candidate's script: pinned Lean 4.34.1 binary + mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` + 8 dependency HEADs re-checked at pinned commits with clean tracked trees; all 17 modules **recompiled fresh** in a temp directory with `-DwarningAsError=true` (17/17 PASS); per-declaration `#check` + `#print axioms` for all **126 public declarations** (105 theorems, 5 lemmas, 14 defs, 1 abbrev, 1 instance); observed axioms exactly {propext, Classical.choice, Quot.sound}; forbidden-token scan clean. A metaprogram environment enumeration found **158** `FourProjection` constants including private/generated names (worker's 157 was on a 16-module subset — consistent). Results: `own-replay-result.json`, `replay-environment-names.json`, `own-checks.log`.
2. `candidate/verification/verify_candidate.py candidate` — the candidate's own verifier rerun on **my byte copy** (fresh rebuild, no object reuse): **PASS**, 126 declarations, standard-3 axioms only. Receipt copied to `receipts/own-copy-replay-audit.json`.
3. `numeric_probes.py` — independent numpy codepath: scalar estimate exact on a 199×199 grid; **200/200** randomized full-hypothesis instances satisfy the inequality and P′ is a projection; **50/50 unbalanced-rank** instances (ranks 1,2,1,1) satisfy it (supports that dropping the balances is sound); disjointness-free search found no violation (hypotheses safe, not vacuous-creating).
4. Primary source **visually read**: rendered p.20 of the actual arXiv v3 PDF (sha `82ea37c2…50fd1`) and read Conjecture 6.6 in the page image; text layer cross-checked.
5. All **three rendered paper pages** visually read; every displayed formula independently recomputed (details below).

## Per-gate verdicts

| Gate | Verdict | Scope |
|---|---|---|
| G1 Source: exact primary arXiv scope | **PASS (arXiv v3) / HOLD (journal body)** | Conjecture 6.6 visually read on printed p.20 of the actual v3 PDF. Formal hypotheses match 1:1. Journal-body comparison remains an explicit unresolved gap; it MUST NOT silently clear on formal success. |
| G2 Full ordinary mathematics | **PASS** | Every step re-derived independently (§A); 250 randomized numerical probes agree; no counterexample or missing hypothesis found. |
| G3 Literal formal endpoint, actual types & axioms | **PASS** | Both endpoints literal with **no residual frame/spectral/injectivity premise** (frames constructed internally); arbitrary finite types incl. empty and zero ranks; `ordinary Matrix.rank` balances in the source wrapper only; standard-3 axioms only; all 126 public types printed and inspected. |
| G4 Bounded novelty / substantive eligibility | **HOLD** | Substantively eligible (genuine open source conjecture, non-routine proof core: two-sided CFC normalization + entrywise two-basis estimate + rectangular contraction bookkeeping — not a polar-optimality corollary). But no bounded search can certify absence of a prior resolution; inherited coverage limits (inaccessible thesis, partial long-work readings) stand. No prior subsuming theorem was found in my own checks. |
| G5 Manuscript scope & layout | **PASS** | 3 pages, clean render, no clipping/overfull damage; all displayed formulas recomputed correct; claims honestly bounded; endpoints, pins, axiom statement, and unresolved-hold disclosures match the certificate. |

## Source-scope comparison (G1)

Printed p.20 (visually read): P,Q,R,S ∈ M_K(ℂ) orthogonal projections with (1) P⊥Q, (2) R⊥S, (3) Im(P)∩Im(R)={0}, (4) Im(Q)∩Im(S)={0}, (5)+(6) two rank balances; conclusion Tr(PR)+Tr(QS) ≥ Tr(P′Q′)+Tr(R′S′) with P′=(P+R)^{−1/2}P(P+R)^{−1/2} etc., "with all the inverses taken in the sense of Moore–Penrose"; the source itself asserts the primes are orthogonal projections; Prop 6.7 proves only S=0.

Formal endpoints (verbatim types in `own-checks.log`):
- `four_projection_inequality`: hypotheses exactly Hermitian idempotents + P*Q=0 + R*S=0 + both range infimums = ⊥; conclusion `(P'Q'+R'S').trace.re ≤ (PR+QS).trace.re` with `X = cfc (fun t => (√t)⁻¹) (P+R)`. `P*Q=0` is equivalent to P⊥Q for self-adjoint idempotents; `cfc (t↦(√t)⁻¹)` is exactly the Moore–Penrose inverse square root (0⁻¹=0 on the kernel). Rank balances **absent** — the stronger statement. No frames, spectral arrays, injectivity or inverse-existence premises remain.
- `banica_nechita_conjecture_6_6`: adds exactly `_hRankPQRS`, `_hRankPRQS` as ordinary `Matrix.rank` balances (unused, wrapper).
- `normalized_source_projection`: P′ Hermitian and idempotent under disjointness — the source's own assertion about the primes.
- Empty ambient dimension and zero ranks instantiated in `SourceBoundaryChecks`/`FrameBoundaryChecks`/`BoundaryChecks` and compile.

Scope notes (no defect): M_K(ℂ) with K finite-dimensional is modeled by arbitrary `Fintype N` (strictly more general, incl. empty); traces are unnormalized with `.re` taken (each displayed trace is real: products of psd matrices have real nonnegative trace). The paper's Theorem 1 bundles the projection claim for all four primes; the certificate proves the P′-form (`normalized_source_projection`), with Q′,R′,S′ following by the same theorem applied symmetrically — not separately instantiated. Cosmetic only.

## A. Independent mathematical re-derivation (G2)

- Scalar core: from `uk+vl=0`, |k+l|²/(|k|²+|l|²) = (u−v)²/(u²+v²) = (1+ab−√((1−a²)(1−b²)))/(1+ab), since u²+v²=2(1+ab). The needed bound w ≥ (1−t)(1+ab) was re-proved by cases (t≥1 trivial; ab<0: w²=1−t+a²b²≥1−t≥(1−t)²; ab≥0: identity (1−a²)(1−b²)−(1−t+ab)²=(a−b)²(1−t), and 1−t+ab>0 for ab≥0 with a,b∈(−1,1)) — matches `ScalarCore.sqrt_lower`/`scalar_coefficient` and paper Lemma 2. Grid probe: zero excess.
- Weighted sum: Σ_ij(a_i²+b_j²)(|k_ij|²+|l_ij|²) ≤ 2(Σa_i²+Σb_j²) from row/column squared-norm ≤1 of both contractions in any orthonormal bases; matches `SpectralCore.weighted_bound`.
- Grading/roots: J(X*Y)L = −X*Y from p*q=r*s=0; X*Y = G^{1/2}KH^{1/2}; JG^{1/2}J=(I−A)^{1/2} gives (I+A)^{1/2}K(I+B)^{1/2} + (I−A)^{1/2}K′(I−B)^{1/2} = 0 — matches eq. (5) and `GradingConsequences.sqrt_relation_of_odd_cross`.
- Pinching & traces: (K+JKL)/2 keeps exactly the diagonal blocks; ¼‖K+K′‖² = ‖K11‖²+‖K22‖²; Tr(P′Q′)=‖u_p* v_q‖²_HS via Tr(aa*bb*)=‖a*b‖²; ½Tr A² = ‖p*r‖²_HS = Tr(PR) — matches `FrameBlocks`, `HSBridge.trace_frame_products`. All recomputed by hand and confirmed.
- mpInvSqrt bridge: (EE*)^{†/2}E = E(E*E)^{−1/2} via the rectangular intertwiner lemma (`hermitian_cfc_intertwine`) — genuine CFC, no rank premise; `normalized_congruence_is_projection` uses only injectivity of E. Verified sound.
- Numerics: 200/200 balanced + 50/50 unbalanced instances pass; scalar grid exact; no disjointness-free violation found in 20 000 probes (hypotheses are safe, and disjointness is genuinely needed for the projection claim).

## B. Strongest objections (remaining, honest)

1. **Journal body never read (unresolved HOLD).** The published Adv. Appl. Math. 83 (2017) 24–46 conjecture page could renumber, restate, or annotate the conjecture. Every legitimate route tried by prior reviewers returned 403/401/429 or metadata only. My formal and paper verdicts do not and cannot clear this. It must be resolved by an authorized acquisition before acceptance, independent of formal success.
2. **Novelty is not certifiable (unresolved HOLD).** The result has been open since 2016 with a sizable citing literature; bounded screens (Semantic Scholar corpus, registries, formal-conjectures trees, Ideosphere catalogue) found no prior full resolution, but a thesis and parts of long works remain unread. I add no positive evidence either way. Absolute priority cannot be claimed.
3. **Paper/manifest packaging nit.** Paper Theorem 1 asserts the projection property for all four primes; the certificate instantiates it only in the P′-form (others by symmetry, unexercised). Also `paper-qa.json` "visual_inspection" credits root, while my independent page inspection confirms it — no discrepancy in substance.
4. **Strength asymmetry risk (checked, not a defect).** The stronger rank-free statement is genuinely proved by the certificate, so no gap; but its novelty relative to possible folklore strengthening must fold into objection 2.
5. **Source peculiarity (inherited from preliminary review, confirmed by me):** the two rank balances force rank P = rank S and rank Q = rank R, making the source's S=0 special case degenerate under all six hypotheses. The candidate proves the universal inequality, not a correction of this peculiarity — substantive, not a mere endpoint correction.

## Remaining gaps

- Journal-body acquisition and comparison (root/source follow-up).
- Novelty clearance against unread literature; any claimed prior subsumption needs an actual theorem plus a coefficient-1 bridge to the canonical normalization.
- Root's own deterministic packet / extracted paper+proof replay (running elsewhere; not polled by me).

## Artifacts (this lane)

`own_checker.py`, `own-replay-result.json`, `replay-environment-names.json`, `own-checks.log`, `numeric_probes.py`, `receipts/own-copy-replay-audit.json`, `receipts/own-copy-replay-stdout.txt`, `candidate/` (byte copy from `a81ca96d98`, 35/35 hashes verified before and after), `provenance.json`.
