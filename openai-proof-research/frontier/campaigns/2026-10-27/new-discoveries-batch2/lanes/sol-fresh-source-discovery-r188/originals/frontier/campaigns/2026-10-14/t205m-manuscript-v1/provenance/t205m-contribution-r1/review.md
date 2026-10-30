# T205M contribution and eligibility gate, round 1

Independent contribution reviewer. This is not a proof gate. Correctness of
the full T205M proof is assumed for this classification and is not certified
here. No acceptance, count, upload or priority verdict is made.

## Verdict: SUBSTANTIAL (narrow), with one required credit correction

Assuming the proof is correct, the unchanged full T205M package adds a
substantial deduction beyond the paid source, project and primary operations:
a sharp, uniform, all-label multiplicity floor for the staircase tensor
square, obtained by a new quantitative evaluation of the project's cyclic
lower-bound recursion. The classification is narrow because the recursion
itself, the module-level multiplicity inputs and every individual tool are
inherited. The residual is the uniform estimate, not a new mechanism.

Required before any acceptance record (record-level, not mathematical):

1. **Credit I19 §4.** `frontier/iterations/i19-fresh-structural-discovery.md`
   §4 (local lines 143–157) already states, over the same source band
   quotients, the multiplicity lower bounds (L1)/(L2)
   `a_m^ε(λ) ≥ Σ_ν c_{ν,(m)}^λ a_{m−1}^ε(ν)` and the four-row two-band
   analogue, says "These are multiplicity lower bounds, not only support
   rules", and says separate quotient bounds "must not be added … Taking
   their maximum is valid." Recursion (5) of `candidate205m.md` is the
   unsigned form of (L1)/(L2) plus the I21 Kostka term. Neither
   `candidate205m.md` nor `source-and-credit.md` names I19 (checked by
   search; I21, I17, R026, Kirillov, Vallejo, BBS, BB are named). This
   verdict already deducts I19 as paid; the record must say so.
2. **Claim language.** Any record must call this new to the project with
   no demonstrated new-to-literature priority (see "Literature" below), and
   must keep the high-capacity lemma credited to parent author assistance.

Neither item changes the frozen theorem, proof or scope.

## Exact object classified

From `candidate205m.md` (SHA-256 17b2b35c…, lines 13–19) and
`scope205m.md` (3eb9d790…): for every m≥2, N=m(m+1)/2, ρ_m=(m,…,1) and
every λ⊢N other than (N) and (1^N),

    g(ρ_m,ρ_m,λ) = dim Hom_{S_N}(S^λ, S^{ρ_m}⊗S^{ρ_m}) ≥ m−1,

with equality at λ=(N−1,1). Ordinary complex coefficients only. No signed
(Sym²/Λ²) refinement, no integral or modular statement, no claim about the
minimum inside the cyclic module W_m.

## Paid operations (credited, not part of the residual)

| Operation | Paid by | Where checked |
|---|---|---|
| Every S^λ occurs in W_m | Pinned cyclic source `dominance.tex`, `thm:cyclic-saxl` | Source read; blobs match pin |
| Full induced quotients W_m ↠ Ind(W_h⊠U_{m,s}), s=1,2 | `band-quotient.tex`, `prop:band-quotient` (read in full) | Source |
| Four-row support of U_{m,2}; multiplicity-free two-row square | `path-band.tex` `prop:two-band`; BB Thm 7.11 (arXiv v3 line 1379; author version line 1410); I21 identification | Source, primary, I21 |
| [W_m:S^λ] ≥ K_{λᵗ,ρ_m}, Z≅M^ρ | Source `dominance.tex` signed average/Q map; I21 §2.1 | Source, I21 |
| Multiplicity recursions over the band quotients; max, not sum | **I19 §4 (L1)/(L2)** (signed); I21 | I19 lines 120–194 |
| Ambient sign invariance g(ρ,ρ,λ)=g(ρ,ρ,λᵗ) | Classical (S^ρ self-conjugate) | — |
| Pieri, LR, rectangle-complement LR, Jacobi–Trudi, Young's rule | Classical | — |
| g(ρ_m,ρ_m,(N−1,1)) = m−1 (sharpness) | Classical corner formula; BBS intro "well known" (line 180); PPV Saxl18 Thm 4.8 | Primaries |
| Rigged-configuration Kostka formula, maximal configuration, one-cell perturbation with vacancy changes −2/+1 | Kirillov hep-th/9304099v2, Thm 1.1, Cor 1.3, (2.1), proof of Thm 2.1 | Primary read lines 20–419 |
| Capacity split (λ_1 vs first-four capacity) as a support template | Cyclic `completion.tex`; companion `capacity.tex`/`balance.tex` | Source |
| Exact character/LR finite computation | Companion `finite.tex` principle; Murnaghan–Nakayama | — |

## Residual after deducting the paid operations

1. **The invariant.** A fixed four-element exception set
   E_h={(N_h),(1^{N_h}),H_h,J_h} and the statement R_h(ν)≥h−1 off E_h for the
   *cyclic* lower bound R_h (not for g), so that the induction never feeds
   ambient multiplicities into W_h. The exception set is closed under the
   induction step without growing, and sign transposition recovers H_m, J_m
   at the end.
2. **Wide case (λ_1>m).** The interior-coefficient count giving at least two
   horizontal m-strip predecessors, the escape predecessor
   (h+1,1^{N_h−h−1}) when H_h and J_h both occur, and the rectangle case via
   two distinct (ν_i,η_i) with LR coefficient one.
3. **High capacity.** Two distinct nonexceptional four-strip predecessors via
   counting rank-k ideals of λ/(λ_5,λ_6,…). Authored by the parent (copied
   bytes fc155c9a… equal the committed 91f3c509 file); part of the package,
   credited as parent assistance.
4. **Low capacity.** A uniform Kostka inequality K_{Lᵗ,ρ_d}≥d for L_1≤d−1 and
   top-four sum ≤2d, with an explicit four-family exception list, proved by
   choosing and estimating explicit rigged configurations; plus the
   full-column deletion (9) and the critical family (m,m−2,1^{…}) with
   two-band coefficient two.
5. **Finite starts** m≤8 (exact computation; not counted as contribution).

## Why this is SUBSTANTIAL and not TECHNICAL

* **Strictly stronger, not an equivalent formulation.** The source theorem
  is support (≥1). Both pinned families say so explicitly: the cyclic
  introduction ("objective is support, or positivity, rather than a formula
  for Kronecker multiplicities") and companion `balance.tex` ("All support
  statements … without any assertion about multiplicities"). A grep of both
  families found no multiplicity lower bound. Raising the floor to the
  exact minimum m−1 for every nonlinear label is new quantitative content.
* **The inherited recursion gives no floor by itself.** I19 and I21 supply
  (5) and finite diagnostics only. I19's own computations (m=3,4,5, local
  line 159) show its seeded signed recursion does not even reach
  support for all labels. Evaluating
  the maximum of (5) uniformly to m−1 needed items 1–4, in particular a
  stable exception set and a new uniform Kostka estimate. The candidate's
  observation that Kirillov's maximal product alone fails on thin rectangles
  (source-and-credit lines 40–43) is consistent with my reading of
  Kirillov (2.1): the low-capacity bound requires chosen configurations and
  a case split, not one formula.
* **Tight constant.** Sharpness at (N−1,1) is classical, but because the
  floor is exact, every label must be shown to reach m−1 with no slack.
  This is not a routine transfer of support to "some" multiplicity.
* **Distinct from prior project results.** R026 concerns an integral
  regular summand in the staircase *cube*; I17/I19/I21 target the signed
  BB Conjecture 10.2 and leave it open; T205M resolves neither and claims
  neither. No project file states or conjectures the m−1 floor (searched
  `frontier/` outside the T205M directories).

What keeps it narrow: every mechanism is inherited, the parent authored a
key lemma, and the number m−1 is small against the known growth of typical
coefficients. A reviewer weighting "new operation" over "new uniform
theorem" could call it TECHNICAL. I do not, because the residual is a
quantified all-label statement that none of the paid operations or read
primaries yields, and its proof requires new uniform estimates rather than
re-instantiation.

## Literature (bounded; absence is not proof of novelty)

* Vallejo arXiv:1310.8362, §8 (local lines 1752–1911): fixed tail ν⊢d only;
  piecewise polynomial growth (Thm 8.10), positivity except finitely many k
  (Thm 8.14). Quantifier differs: T205M lets the label vary with m.
* Pak–Panova–Vallejo Saxl18 and arXiv:1304.0738: positivity (Main Lemma 1.3,
  Thm 1.4), depth ≤3 formulas (Thm 4.8 incl. corner formula), labels with
  vanishing characters (Prop 4.14/4.16). Positivity and fixed families only.
* Pak–Panova QBC23 / arXiv:1406.2988: g(λ,μ,μ)≥|χ^λ[μ̂]| for self-conjugate μ,
  "the only general lower bound that we know" (QBC23 line 58). It vanishes on
  exponentially many labels, so it is not a uniform floor.
* Bessenrodt–Bowman–Sutton arXiv:1903.07717: corner case k−1 "well known"
  (line 180), unbounded coefficients, special-family floors (Thm 5.10, 5.11,
  Cor 5.12 g≥k−1 for one framed family, lines 1222–1230). Not all labels.
* Bessenrodt–Bowman (arXiv 2202.03066v3 and author version): depth ≤2
  splitting, Thm 7.11, signed conjectures §10. No all-label floor.
* Ikenmeyer arXiv:1410.6549v2: dominance-comparable positivity (abstract,
  Thm 2.1). Support only.
* Lee arXiv:2512.15035v1 (2025-12, unrefereed, not validated): concluding
  open question (2) "What is min_λ g(λ,ρ_k,ρ_k)?" (local line 309). Literally
  this minimum is 1 at the trivial label; the natural nontrivial reading is
  exactly T205M's question. This is a pointer that the question is open in
  the 2025 literature, not evidence of priority.
* Bounded web searches found no prior uniform all-label floor.

New to the project: yes. New to the literature: not demonstrated.

## Eligibility and chronology

* Identity: all eight anchored files match the brief, including manifest
  29ab2fdb…41db9. Author `verify.py` passes with that anchor and fails with a
  wrong anchor. The packet's 21 selected source blobs match the anchored
  `sources/preprints-tree.json` (eeecc1da…) at pin fd4aeeb2…; I compared
  every family entry independently.
* Scope freeze: `scope205m.md` 3eb9d790… is bound by the parent receipt
  `t205m-parent-combinatorics-r1/receipt.json`, committed in 91f3c509
  (2026-10-18T02:55:53−07:00) together with the high-capacity proof, before
  the packet commit 953d9bfb (03:10:15−07:00). This supports that the scope
  existed before completion of the uniform proof. The 09:35:45 UTC freeze
  time itself rests on file mtime and author statement only.
* Historical files: `inherited-recursion-work.md` has a 4-line added status
  marker; removing it reproduces the parent-read hash 45f509e1… exactly.
  `exploratory-screen-205.md` also has an added "historical" marker with no
  earlier external anchor for its original bytes (minor, disclosed limit).
* Acceptance-rule fit (NEW-TEN-2026-10-14.md): not a routine transfer,
  rediscovery or equivalent formulation as assessed above; distinct from
  R026; the campaign count is untouched by this review.

## Controls and replay run in this review

All on copies under `/var/tmp/t205m-contrib-buTy/`, never in the canonical
packet. Author `control-tests.py` with the external anchor: PASS, all 13
cases (canonical, unchanged copy pass; payload, missing, extra file, extra
directory, root and ancestor symlink, hardlink, FIFO, nested manifest,
self-reseal and wrong anchor all rejected). With a wrong anchor the script
aborts at baseline. `verify-finite-proof.py` (default recompute mode):
PASS_FINITE_BASES, certificate hash 5ffb1880… equal to the anchor; this is a
reproduction of computation, not a proof review. The canonical packet still
verifies and `git status` shows it clean afterwards. See `control-replay.json`.

## Not done

No proof review. The parallel proof reviewer's draft was not read. No
staging, commit, upload, shared edit or nested agent. Reading limits are in
`reading-limits.md`.
