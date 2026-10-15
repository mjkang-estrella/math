# Independent GLM implementation check: staircase tensor projection (m = 1, 2, 3)

Owner: `frontier/campaigns/2026-10-14/staircase-glm-check-r1/` (this directory only).
Date: 2026-10-14. Status: **finite implementation check complete; no mismatch found.**
No standalone mathematical verdict is issued; parent review is required.

## 0. Scope and limits

- This checks the *implementation-level* identity of candidate Sections 1–4 at
  m = 1, 2, 3 only: the expansion of `z = v_R ⊗ v_R ⊗ v_C`, the local map
  `q(a,b,c) = (a+b-1, a)` when `a = c` (else killed), the content projection onto
  `D = {(r,a): 1 <= a <= r <= m}`, the predicted single word
  `w(i,j) = (m+1-i, m+2-i-j)` with coefficient +1, position equivariance, and the
  group-orbit left inverse.
- It is **not** the all-m theorem, an integral-lattice identification, a novelty
  or contribution verdict, or a proof review. m >= 4 is untouched. No
  randomized evidence was used (none needed).
- The author's `projection_controls.py` and `tensor_controls.py` were **not read
  or imported**; everything below is implemented from the candidate's stated
  conventions. The author's complex character tests are unrelated and unused.

## 1. Bound input

| item | value |
|---|---|
| Candidate | `fresh-algebra-discovery-r1/candidate.md` |
| SHA256 | `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179` |
| Length | 17969 bytes, 151 lines |
| Read extent | full file, end to end (Sections 1–4 used; §5–7 noted) |
| Local copy | `inputs/candidate.md` (hash-identical to the original, verified) |

## 2. Method

Independent checker `glm_staircase_check.py` (pure Python 3, assertions on,
deterministic, run `python3 -B glm_staircase_check.py`, exit 0, ~0.4 s):

- `B = {(i,j): i,j>=1, i+j<=m+1}` in lexicographic order; rows `R_i` and columns
  `C_j` ordered as in §1; `alt` over each ordered block = sum over all
  permutations of `1..r` with inversion-count signs.
- `v_R`, `v_C` built as explicit integer word→coefficient dictionaries
  (support sizes `Π_r r!`: 1, 2, 12 per layer for m = 1, 2, 3).
- Full triple expansion enumerated with multiplicities; no prefiltering by the
  uniqueness conclusion; the nested-palette lemma is NOT assumed — survival is
  decided only by the literal local equality and content filters.
- Orbit test: **direct full-orbit expansion** (explicitly identified as such).
  For every `g ∈ Sym(B)` the layer supports are permuted by
  `g e_a = e_{a∘g⁻¹}` and re-expanded from scratch through the pipeline. No
  word-permutation shortcut was used; no expensive case was replaced.

## 3. Base identity results (g = id)

| m | raw triples | local-equality survivors | content survivors | aggregated output |
|---|---|---|---|---|
| 1 | 1   | 1  | 1  | `(1,1)->(1,1)`, coeff **+1** |
| 2 | 8   | 2  | 1  | `(1,1)->(2,2), (1,2)->(2,1), (2,1)->(1,1)`, coeff **+1** |
| 3 | 1728| 12 | 1  | `(1,1)->(3,3), (1,2)->(3,2), (1,3)->(3,1), (2,1)->(2,2), (2,2)->(2,1), (3,1)->(1,1)`, coeff **+1** |

Each aggregated output is exactly the single predicted word `w` with
coefficient exactly +1 over ℤ; asserted, not observed loosely. Reductions
modulo 2, 3, 5 of the same integer coefficients leave the same single word with
coefficient ≡ 1 (recorded in `results/glm_staircase_check_results.json`).

## 4. Orbit test: P(g z) = δ_g for all g ∈ Sym(B)

| m | orbit elements tested | expected N! | result |
|---|---|---|---|
| 1 | 1   | 1   | all pass |
| 2 | 6   | 6   | all pass |
| 3 | 720 | 720 | all pass |

For every g the pipeline returned exactly `{w∘g⁻¹: 1}` (equivariance reading)
and the independently re-derived group element `σ = d⁻¹∘w` read off the
retained word d equaled g (left-inverse reading). Both readings come from the
same direct expansions and both were asserted for all 727 orbit elements.

## 5. Negative controls (base vector z, m = 1..3; concrete observed outputs)

Verdicts are per-m and honest. **"Ineffective" means the mutation did not change
the observed base output; it is not labeled rejected.**

| control | m=1 | m=2 | m=3 | observed difference (concrete) |
|---|---|---|---|---|
| C1 delete equality filter | ineffective (vacuous: 1 triple) | FAILS | FAILS | m=2: two content-surviving words, each net coeff 0 (third layer cancels). m=3: 12 content-surviving words, each net coeff 0; 144 content-surviving terms in total. Matches the candidate's own description of this mutation. |
| C2 drop second pair coordinate (letters `a+b-1`, `a=c` kept, content = each r exactly r times) | FAILS | FAILS | FAILS | m=1: output letter `(1)` instead of `(1,1)`. m=2: `(1,1)->[2],(1,2)->[2],(2,1)->[1]` coeff 1. m=3: `(1,1)->[3],(1,2)->[3],(1,3)->[3],(2,1)->[2],(2,2)->[2],(3,1)->[1]` coeff 1 — different output lattice, not the target identity. |
| C3 sum shift `a+b` (letter `(a+b,a)`) | FAILS | FAILS | FAILS | zero content-surviving terms at every m: aggregated output empty vs. target `{w: 1}`. |
| C4 filter `a=b` instead of `a=c` | ineffective (vacuous) | FAILS | FAILS | m=2: 4 local survivors, 0 content survivors (empty output). m=3: 144 local survivors, 0 content survivors (empty output). |
| C5 column-layer signs negated | FAILS | FAILS | FAILS | same word w, coefficient **−1** instead of +1 at every m. |
| C6 second row layer unsigned (all signs +1) | ineffective | ineffective | ineffective | output unchanged: `{w: 1}` at all m. The forced b-word is the reversal whose coefficient is +1 under either sign convention, so this mutation cannot detect a defect in the base identity at m ≤ 3. Reported as ineffective, **not** rejected. Note C6 is not an instance of the candidate's construction (the second layer is no longer alternating). |

Genuinely failing controls at every m: **C2, C3, C5**. C1 and C4 fail for
m ≥ 2 and are vacuous at m = 1 (only one triple exists there, so every
mutation is forced to the same output). This per-m granularity is reported so
that no ineffective mutation is claimed as rejected.

## 6. Incident log (transparency)

An earlier version of the checker applied a sign-negation multiplier inside the
per-block recursion, so a global negation compounded as `(-1)^{#blocks}` and
cancelled itself at m = 2. This was caught by hand-checking the m = 2 C5
coefficient against the expansion (expected −1, observed +1), fixed by
negating the finished layer vector, and re-run. Only the C5 control was
affected; the base, mod-p, and orbit computations never used the multiplier.
No mismatch with the candidate was ever observed at any point; the bug was
internal to a control.

## 7. Receipts

| artifact | SHA256 |
|---|---|
| bound candidate (original and copy, identical) | `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179` |
| checker `glm_staircase_check.py` | `d4ef57e71ba88eec0f011955b7528ca1a3097ef6771ad254eb8e223945f06362` |
| results `results/glm_staircase_check_results.json` | `555164acb3b71336fd3d1072ef888e9e5d7b9923c2f9edd1cac1af85c236a10d` |
| this report `report.md` | see `receipts.json` |

Environment: CPython 3.14, Linux, assertions enabled (`python3 -B`, no `-O`).
Command: `python3 -B glm_staircase_check.py`; exit code 0; all assertions passed.
Machine-readable counts, aggregated outputs, mod-p reductions, orbit records,
control outputs, and hashes are in `results/glm_staircase_check_results.json`;
final hashes in `receipts.json`.

## 8. Summary for parent

Sections 1–4's construction, as literally specified, reproduces exactly at
m = 1, 2, 3: single surviving term, word `w`, coefficient exactly +1 over ℤ
(and ≡ 1 mod 2, 3, 5); position equivariance and the orbit left inverse hold on
all 1 + 6 + 720 = 727 group elements by direct full-orbit expansion. No
counterexample was found, so none needed preserving. This is an implementation
check at m ≤ 3 only and carries no all-m, base-change-beyond-recorded-reductions,
or contribution verdict. Parent review of the implementation is authorized and
expected; no standalone mathematical verdict is claimed.
