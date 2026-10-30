# Independent adversarial review — Keith multicolor counterexample (MathDB 345259)

Reviewer: independent Pi/GLM review sub-agent, lane `pi-keith-multicolor-review/`.
Reviewed commit/frozen bytes of `candidates/keith-multicolor/` (commit bba46b3ef1 context). I authored none of the candidate's code, proof, or manuscript. No children started; no candidate, lane, index, git, or dependency files modified. All hashes below re-measured by me, not copied.

**Verdict: PASS on all gates. One combined source-question outcome (refutation of Keith's three-color Conjecture 1). Credit decision returned to parent; no acceptance performed here.**

## Frozen-byte verification

| File | Expected (frozen) | Measured | Match |
|---|---|---|---|
| main.tex | e3d6eb25…127fa7000 | e3d6eb25881b4d954ab353826527ef25dfb4c21e801a36b34375268127fa7000 | ✓ |
| paper.pdf | a865bc1a…958dcfde7 | a865bc1a047dc8d61c66d4577c96def55c052b16319c82ce61cd322958dcfde7 | ✓ |
| PartitionTopCounts.lean | 310b0ee2…f42b18e4 | ✓ | ✓ |
| PartitionSource.lean | 7233e5b8…16c2d9b7d | ✓ | ✓ |
| PartitionWitnesses.lean | e426f926…dc29e1c3520 | ✓ | ✓ |
| PartitionConclusion.lean | 241e4cb6…ddfce92899840 | ✓ | ✓ |
| PartitionPolynomial.lean | fc219897…988bffa6c3 | ✓ | ✓ |
| PartitionFinal.lean | d086491b…07038d1dcc | ✓ | ✓ |

## Gate 1 — Source fidelity and claim scope: PASS

- **arXiv 2001.08351**: live abstract page fetched; submission history shows **only v1** (2020-01-23). The v1 PDF in `parent-partitions/sources/` hashes to b1c1855f…79dfe8 (matches provenance). No newer version exists to check against.
- **Printed p. 2 (viewed myself)**: Theorem 3 states Σ_{n,t⃗} p_{M×N}(t⃗;n) x₁^{t₁}…x_k^{t_k} q^n = Σ_{r=0}^{min(M,N)} (x₁+⋯+x_k)^r f_{(M×N;r)}(q), f_r the generating function for box partitions with exactly r different part sizes; Conjecture 1: fix n, set any one x_i = 1, any linear cut through the remaining coefficient array is unimodal. The candidate's F(x,y)=Σ a_r(1+x+y)^r with a_r = #box partitions of 325 with r distinct sizes is exactly the q^325 slice of Theorem 3 with x₃=1: for each partition with r distinct sizes, (x+y+1)^r generates its color assignments, coefficient of x^i y^j being C(r,i)C(r−i,j). Faithful.
- **Printed p. 8 (viewed myself)**: "if x_k is set to 1, the array of the remaining coefficients appears to be unimodal in any linear cut. … Even slant cuts through the array – here, the sequence (300, 387, 19) is the (2,1) cut starting from position (3,1) …". I located the example entries in the printed 5×5 matrix: (3,1)→(2,3)→(1,5) = 300→387→19, direction (−1,2), the same line family as the candidate's step (1,−2); and Conjecture 1's "any linear cut" covers it independently. Slant cuts are in the author's intended scope; step (1,−2) is not a loophole.
- **Box conventions**: parts ≤ M, #parts ≤ N, one color per distinct size ("only one color is chosen per size of part") — matches `IsSquareBox` and `distinctCount` usage. M=N=25 makes the M/N orientation immaterial.
- **Live MathDB** `https://mathdb.com/api/posts/345259` (fetched 2026-10-26): byte-equivalent to the frozen snapshot `sources/345259.json` (snapshot sha 55803919…8ce45 verified). `status:"open"`, `progress:null`, `lean_formalization_count:0`, and `solutions`, `human_solves`, `model_attempts`, `comments`, `replies`, `formulations`, `attachments` all empty. The post's statement body is the k-color generalization ("This generalizes the unimodality conjecture of Dousse and Kim"), so 345259 is the correct target despite the Dousse–Kim title.
- **Predecessor scope**: Dousse–Kim 1701.07915v2 §7 read: Conjecture 7.1(ii) is "for every fixed n, the coefficient of q^n in the over-(q,t)-binomial is unimodal in t" — the two-color/overpartition one-variable statement. This candidate does **not** touch it (k=3, two-variable cut). The manuscript's non-refutation disclaimer is accurate and correctly cites Conjecture 7.1(ii).

## Gate 2 — Mathematics: PASS

Independently re-derived every step before looking at the Lean code:

1. a₂₅ = 1 (staircase 1+⋯+25 = 325 is the unique 25-distinct-size partition; 25 parts forces all multiplicities 1).
2. a₂₄ = 0: 24 distinct sizes sum to 325−b; ≤25 parts leaves ≤1 extra part, which would need size b, contradicting omission.
3. Injection: d = u+w−v ∈ (u,w) strictly; case v≤d removes {u,w}, adds {v,d} (both already present → support 23, extras {v,d}, missing {u,w}); case d<v removes {d,v}, adds {u,w} (extras {u,w}, missing {d,v}). Sum and part count preserved; all parts in 1..25. Decode (compare smaller missing vs smaller extra; case 1 always u<v, case 2 always d>u) is a total left inverse on both cases, including v=d (extras {v,v}). Hence ≥ C(25,3)=2300 partitions with exactly 23 distinct sizes.
4. Weights: at (20,5) only r=25 (r<25 ⇒ r<20+5) → C(25,20)C(5,5)=53130. At (21,3) r=24 absent, r=25 → C(25,21)C(4,3)=50600. At (22,1) each r=23 witness gives C(23,22)C(1,1)=23 → ≥52900. (The staircase additionally contributes C(25,22)·3=6900 there; subsumed by "all other contributions nonnegative".)
5. Cut: (20,5),(21,3),(22,1) are consecutive lattice points on y=45−2x, whose full nonnegative-lattice segment is exactly x=0,…,22 (y≥1). A strict valley at consecutive points defeats weak unimodality regardless of all other entries.
6. **My own independent enumeration** (`reviewer_dp_check.py`, exhaustive size-by-size DP over all box partitions — a different algorithm from the parent's missing/repeated classification): a₂₃=2444, exact cut 53130 / 50600 / **63112**, valley true. This also independently confirms the research-lane exact third coefficient 63112 (not a formal dependency). Result in `reviewer-dp-check.json`.

## Gate 3 — Lean semantic coverage and strict replay: PASS

- **Fresh replay in this lane** from copied `candidate.json`, `formal/`, `verification/{verify_candidate.py,pins.json}`; pinned Lean 4.34.1 (commit 5045d005…), mathlib d13f23b7… + all 7 pinned dependencies verified unmodified. Wall time ≈3 min; Witness-certificate compile peaked ≈30% host RAM (consistent with the 40–50 GB parent report).
- Result: **PASS, 37/37 declarations, warningsAsError=true, axioms exactly {propext, Classical.choice, Quot.sound}**. My receipt `build/verified/audit.json` hashes to **b5e185f0bdadd3b310b2f145195ddcb3c6f713a79dba2eb255c9c055f5591b62 — identical to the parent's recorded audit SHA**, i.e. byte-deterministic replay. Full logs preserved under `build/verified/`.
- **Verifier reviewed adversarially**: checks compiler version, every dependency revision + cleanliness, rejects source tokens `sorry|admit|axiom|unsafe|native_decide`, builds every module with `-DwarningAsError=true`, and `#print axioms` on all 37 names with a strict allowlist. Sound.
- **Modules read line-by-line**. Semantic coverage confirmed: `sourceArray` is the literal sum over mathlib `Nat.Partition 325` objects filtered by the literal box predicates (not a coefficient model); `sourcePolynomial` is the literal Σ_p (X+C(X+1))^{r_p}; `sourcePolynomial_coefficient` is *proved* from mathlib binomial identities (`coeff_X_add_C_pow`, `coeff_X_add_one_pow`), bridging polynomial and count with no assumption; `sourceArray_first/middle` reduce the finite sums with kernel-computed binomials; the 2300-witness certificate `witnessParts_certificate` is `decide +kernel` over all triples checking card/sum/box/support-23 **and** `decodeParts` left inverse, from which injectivity, `witnessPartitionSet_card=2300` and the ≥52900 bound are derived; `source_full_counterexample_345259` states ¬Unimodal of the literal polynomial cut with no residual premises. `Unimodal` is standard weak unimodality; the strict-valley negation is a complete two-case argument. `kernelSort` is structurally recursive (Quot.liftOn with a genuine perm-invariance proof); no `native_decide` anywhere. No forbidden escape hatches; 36 declarations cite the three standard axioms and `Unimodal` depends on none.
- Nothing in the certificate depends on the q-Gaussian search, the variable-N family, or the exact 63112 value; those are correctly quarantined as research notes.

## Gate 4 — Novelty / prior credit: PASS (bounded, honestly limited)

- Live MathDB full record: no solutions/progress/comments of any kind (verified above).
- Searches (recorded in provenance.json): source title/author; "colored partitions box linear cut unimodal false counterexample"; Dousse–Kim follow-ups; citation bodies of 2001.08351. **No earlier or independent resolution found.** The citing corpus (~6 citations) is unrelated (Andrews–Keith Schmidt-type theorems; a 2024 book reprint).
- **Tim Wagner 2021 thesis (MTU etdr 1175) assessed, not assumed**: chapters cover flawlessness of G_λ via the Multicolor Theorem, unimodality of G_λ for infinite families of 5- and 6-part λ, and a poset of generating functions P_n. Different problems; no colored linear-cut content. (Keith sat on the committee — context, not overlap.)
- Noise noted: an AI-generated topic page (emergentmind) claims box-restricted colored partitions are "provably unimodal along linear cuts (Keith, 2020)" — this misstates the source (Keith only conjectures). Rejected as prior art.
- **Access limits**: WorldScientific DOI PDF and institutional route returned 403 (parent); I checked the MTU DigitalCommons article page — metadata only, no downloadable full text. The final typeset body therefore remains unread by this review. arXiv v1 is the only version and was read in full text plus pages 2 and 8 visually. The gap is bounded and recorded; it cannot silently hide a typeset-body-only resolution, but this is the residual limit of the novelty gate.
- No citation-count or empty-search priority inference is made; search recency limited to pre-2026 literature reachable online.

## Gate 5 — Manuscript: PASS

- All three rendered pages inspected (`build/final-page-{1,2,3}.png`): legible throughout; no clipping, overlap, missing glyphs, or unresolved references; cached Tectonic build exit 0, issues empty, 3 pages.
- Theorem/lemma statements match the formal endpoint exactly (53130, 50600, ≥52900, cut y=45−2x). Bibliography verified against sources: Keith IJT 17(3) (2021) 591–601, DOI 10.1142/S1793042120400151, arXiv:2001.08351v1; Dousse–Kim JCTA 158 (2018) 228–253, Conjecture 7.1. Attribution section credits Keith (definition, polynomial, conjecture) and Dousse–Kim (predecessor) correctly.
- Cosmetic notes (non-blocking, no action required by me): (a) p.1 "explicitly includes slant cuts with step (1,−2)" is loose — the author's printed example is a (−1,2)-type cut; the general "any linear cut"/"even slant cuts" statements cover (1,−2). (b) The manuscript does not spell out the staircase's own 6900 contribution at (22,1); harmless since only the lower bound is claimed and nonnegativity of the remainder is stated.

## Decisive objections

None. Two cosmetic notes above and one recorded access limit (typeset body unread); none affects correctness, scope, or novelty.

## Outcome

One combined source-question outcome: **Keith's Conjecture 1 (three-color linear-cut unimodality) is false**, witnessed by M=N=25, n=325, x₃=1, cut y=45−2x, coefficients 53130 / 50600 / ≥52900 at (20,5),(21,3),(22,1). Not per-coefficient, per-helper, per-witness, or per-box credit; the original Dousse–Kim two-color conjecture is not refuted. Gates 1–5 PASS; formal replay receipt and logs in this lane; novelty bounded by the recorded access limits.
