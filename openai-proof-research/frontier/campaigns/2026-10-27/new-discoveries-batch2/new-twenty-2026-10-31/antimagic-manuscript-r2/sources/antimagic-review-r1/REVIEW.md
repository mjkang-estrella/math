# antimagic-review-r1: independent adversarial review of the MathDB 354228 candidate

Reviewer: Claude Opus 5.5, lane `antimagic-review-r1`, 2026-11-04 (UTC). This is a review, not an acceptance. No credit is claimed and nothing is self-accepted; root decides.

Candidate: expanded-corpus-r142, `outputs/antimagic/proof.md` (sha256 `90752e8e…6ddd`). The claim is that χ_la(T(t, n)) = t^n + 1 = l + 1 for every even t ≥ 2 and every depth n ≥ 1. This resolves Conjecture 6.1 of Bača, Semaničová-Feňovčíková, Lai and Wang, Fundamenta Informaticae 185(2) (2022) 99–113 (arXiv:2204.04479v2).

## Verdicts

| Gate | Verdict | One-line reason |
|---|---|---|
| A. Statement fidelity | **PASS** | The theorem is exactly published Conjecture 6.1 and MathDB 354228, with all even t ≥ 2 and every depth n ≥ 1. It contradicts no source theorem. There are two citation-hygiene fixes (below). |
| B. Independent mathematics | **PASS** | I re-derived every step by hand and found no gap. My own code (326 grid cases plus cross-checks) verifies the construction for every even t ≤ 200 and every depth with m ≤ 3 million. |
| C. Lean route | **QUALIFIED_PASS** | The endpoint shape is right, but the draft has data-carrying `sorry` instances and missing `DecidableEq` binders. A validated piecewise-affine closed form gives a much cheaper route. Estimate: 1,500 to 3,000 lines. |
| D. Prior art | **QUALIFIED_PASS** | Bounded search, no resolution found. Two paywalled tree papers are unread; at most they could cover the n = 2 sub-case. |
| E. Significance | **QUALIFIED_PASS** | A genuine full resolution of an explicitly open published conjecture. The n ≥ 3 core is a new arrangement, not a source-lemma bridge. Significance is modest, and n = 2 leans on source ingredients. |

**Overall recommendation: PROCEED to Lean formalisation**, with the conditions listed at the end.

## Inputs and hashes

- All 151 files of `expanded-corpus-r142/` were hashed before and after the review: `hashes/inputs-before.sha256` and `hashes/inputs-after.sha256`. Both lists have sha256 `0c31137f68caebfeee86174510f4297b7b6a0e83fb9bc3cf9950e4688edf10f4`, so the inputs are unchanged.
- Key input files:
  - `proof.md`: `90752e8e6360359bb685f340645333d21cc208258d2b1e25a05caa38b63b6ddd`
  - `sources/354228.body.txt` (arXiv v2 HTML text): `586c79a9…5f99`
  - `formal-draft/LocalAntimagicEvenTree.lean`: `c4f16b23…64da6`
  - `formal-draft/STATEMENT-CORRESPONDENCE.md`: `c764b188…b6d`
- I did not import, execute or copy the discovery lane's scripts.
- Downloads went into fresh directories under `dl/`; their hashes are in `hashes/downloads.sha256`.

## Gate A: statement fidelity (PASS)

**Source definitions.** Line numbers below are in the published PDF text, `dl/episciences/fi9349.txt` (fetched from fi.episciences.org/9349/pdf, which is the FI 185(2) version, identical in content to arXiv v2).

- Definition 1.1 (lines 55–60): a bijection f : E → {1, …, |E|} with w(u) ≠ w(v) for adjacent u and v, where w(u) = Σ_{e ∋ u} f(e).
- χ_la is the minimum number of colours over all local antimagic labellings.
- Definition 1.3 (line 84): a complete full t-ary tree is a rooted tree in which every non-leaf has exactly t children and every leaf has the same depth.
- Definition 1.4 (line 87): the n edge levels, with level h containing t^h edges.

**The conjecture.**

- Published Conjecture 6.1 (line 638) reads: "For any complete full t-ary tree T, t ≥ 2 even, χ_la(T) = l + 1."
- In the arXiv HTML it is numbered "Conjecture 6.0" (`354228.body.txt` line 289–290), and the text calls it "Conjecture 6".
- The MathDB record (`sources/354228.raw.jsonl`; live page `dl/mathdb/p354228.html`, which shows 0 solutions on 2026-11-04) states the same thing for every even t ≥ 2.
- The quantifiers are all even t ≥ 2 and every complete full t-ary tree, which means every depth n.
- The depth-0 tree K_1 has no edges and is excluded by the source's standing hypothesis (Definition 1.1 requires no isolated vertices). So `proof.md` line 19's restriction to n ≥ 1 is faithful.

**No contradiction with the source.**

- Theorem 5.1 (PDF line 449) says χ_la ∈ {l + 1, l + 2} for even t, which is consistent.
- Theorem 4.1 (line 380) covers odd t and is disjoint from this claim.
- Figures 3, 4 and 6 show l + 2 labellings, but they are examples, not lower bounds.
- Figure 5 (line 612, t = 2, n = 2) already gives an l + 1 labelling, and the source remarks on this (line 601).

**Citation-hygiene fixes required in proof.md** (they do not affect correctness):

1. The lemma numbers in `proof.md` follow the LaTeXML HTML numbering, not the published one:
   - "Lemma 2.13" (lines 75 and 179) is published Lemma 2.9 (PDF line 214).
   - "Lemma 2.15" (line 178) is published Lemma 2.10 (line 229).
   - "Conjecture 6" is published Conjecture 6.1.
   - Lemma 2.2 has the same number in both versions.
2. Case 2.2 (n = 2, t = 2; `proof.md` lines 50–56) is exactly the source's Figure 5: root edges 1 and 4, colours 5, 6 and 15, leaves 3, 2, 5 and 6. It must be attributed to the source, not presented as new.

## Gate B: independent mathematics (PASS)

### By-hand re-derivation

I checked every step against the proof text. Line numbers refer to `proof.md`.

**Lower bound (lines 27–35).**

- Leaf colours are the leaf-edge labels: l distinct values, each at most m.
- The edge labelled m has a parent endpoint u with at least t ≥ 2 incident edges, so w(u) > m.
- This gives at least l + 1 colours. Correct. It is the source's Theorem 1.2, citing [3].

**n = 1 (line 48).** The root colour is t(t + 1)/2 > t. Correct.

**n = 2, t = 2 (lines 50–56).** Correct; this is the source's Figure 5.

**n = 2, t ≥ 4 (lines 58–98).** Every claim checks out.

- The label sets partition [1, M]:
  - R′ = [s + 3, 3s + 1] has 2s − 1 elements;
  - S* = {1} ∪ [3, s + 2] ∪ [3s + 2, 4s] has 2s elements;
  - B = [2t + 1, M] has t(t − 1) elements.
- Σ({2} ∪ R′) = 4s² + 2s = M, so ΣS* = t².
- The middle-run pairs are Lemma 2.2 translated by β with κ = s − 1 ≥ 1. I checked both endpoints of each family. The sums are [2β + 3κ + 3, 2β + 5κ + 3], which are 2κ + 1 = t − 1 consecutive values.
- Each tuple has 2(s − 1) + 2 = t elements.
- w(x_i) = ρ_i + Γ + i = Γ + 3s + 2 = c for every i.
- w(x*) = t² + 2 and w(root) = M both lie in B.
- c > t(2t + 1) > M, so c is a new colour.
- Properness: M ≠ t² + 2 because t ≠ 2; t² + 2 > 2t ≥ max S*; and c exceeds every label.
- The colour set is S* ∪ B ∪ {c}, which has t² + 1 elements.

**n ≥ 3, the shell construction (lines 100–160).**

- (a)–(b), the label partition:
  - R = (N − t)/2 is an integer;
  - the shells π_d for d ≤ R cover [1, N − t + 1] \ {Z};
  - the ranges D_{n−1} = [1, k], D_{n−2}, …, D_2 have total size Σ_{h=2}^{n−1} t^h/2 = R;
  - A_1 = {Z} ∪ [N − t + 2, N];
  - so A_1, …, A_{n−1} partition [1, N].
- (c), children sums: the children of u ∈ V_h, for 1 ≤ h ≤ n − 2, receive t/2 shells, so their labels sum to tZ.
- (d), the leaf tuples:
  - Each outer pair sums to 2N + tq + 1, since (b − 1) + (t − b) + 1 = t.
  - The middle pair sums to 2N + tq + 1 + a − σ(a).
  - δ(a) = −a for a ≤ k, and δ(k + j) = k + 1 − j. So δ is a bijection from [1, q] onto {±1, …, ±k}.
  - The T_a partition Λ, because a ↦ q + 1 − a and σ are bijections block by block.
  - w(u) = Z + ε + Γ − ε = Γ + Z = c > m.
- (e), the range checks:
  - tZ − N = (t/2 − 1)(N − t) ≥ 0.
  - Z ≤ q is equivalent to N − t ≤ 2q − 2. This holds because Σ_{j=2}^{n−2} t^j = (t^{n−1} − t²)/(t − 1) ≤ t^{n−1} − t². For n = 3 the sum is empty and the bound is 0 ≤ 0.
  - The root colour is Z + (t − 1)N − (t − 1)(t − 2)/2, which lies in [N + 1, m].
- (f), properness:
  - The leaf-parent and V_{n−1}/V_{n−2} pairs are separated by c > m.
  - For a vertex in row h with 1 ≤ h ≤ n − 3 and its child, the colour difference is f(e(u)) − f(e(v)) ≠ 0. This holds by bijectivity alone, which is even simpler than the "disjoint A_h" argument in the text.
  - Root against row 1: w(root) − tZ = (t − 1)(N − Z − (t − 2)/2) = (t − 1)N/2, since N − Z = (N + t)/2 − 1. For t ≥ 4 this exceeds N ≥ max A_1. Correct.
  - For t = 2 it equals Z ∈ A_1, a genuine conflict. That is why (g) is needed. My negative control confirms the conflict: without the swap, the root and x_Z share colour 9 at n = 3 and 45 at n = 5.

**t = 2 swap (lines 162–172).**

- Here Z = 2^{n−1} − 1, D_2 = {R − 1, R}, Λ = [2Z + 1, 4Z + 2], and the swapped label set {1, 2, 2Z − 2, 2Z − 1} is the same set as before.
- The colours are 3Z, 3Z + 1 and 4Z − 1.
- The row-2 colours are 2Z + 2, 4Z − 1, 2Z + 1 and 4Z − 2. The only possible coincidences need Z ∈ {1, 2}, but Z ≥ 7 for n ≥ 4.
- For n = 3, row 2 has colour c.
- The rows below are unaffected, because every row-2 vertex keeps its own children sum 2Z.

**Generality.** Every case split is n = 1; n = 2 with t = 2; n = 2 with t ≥ 4; and n ≥ 3 for all even t, with a t = 2 patch. Every inequality is proved symbolically for all parameters. The proof is general, not computational.

### Own computation

Script: `scripts/verify.py` (sha256 `44ad614e…59ac`). I wrote it from the definitions and the proof text alone. It was run through `scripts/run-capped.sh` with CPU 120 s, wall 140 s, address space 1.5 GiB, MALLOC_ARENA_MAX=2, two CPUs, and one process at a time. The largest peak RSS was 497 MB. All 18 runs returned rc = 0 (logs in `logs/`), and no background job remains.

| Run | Result |
|---|---|
| `grid 200 3000000` | 326 cases: every even t ≤ 200 and every n with m ≤ 3,000,000. This includes t = 2 with n = 1 to 20, t = 4 with n ≤ 10, t = 6 with n ≤ 8, and t up to 200 at n = 1 and 2. All pass: bijective onto [1, m], proper on every edge, and exactly t^n + 1 colours. The largest case has m = 2,883,594. |
| `cross 60 300000` | 124 cases re-checked by a second, edge-list checker (explicit vertex ids, degrees counted, leaves counted as t^n). Both checkers agree. |
| `one …` | Boundary cases (t, n) = (2,1), (2,2), (2,3), (2,4), (4,1), (4,2), (4,3) and (6,2) all pass. |
| `ident 400 25` | The proof's integer identities and inequalities, without building trees, hold in 4,600 cases (t ≤ 400, 3 ≤ n ≤ 25). |
| `brute` | Exhaustive minimum over all labellings of T(2,1), T(4,1) and T(2,2): 3, 5 and 5 colours, equal to l + 1. |
| `neg` | Negative controls show the checker is sensitive (details below). |
| `closed 40 200000` | The piecewise-affine closed form proposed for Lean (gate C) reproduces the construction exactly in 50 cases with n ≥ 3, and all of them pass. |

The negative controls behave as expected:

- Dropping the t = 2 swap is detected as improper.
- A duplicated label is detected as non-bijective.
- Swapping two leaf labels between different second-last-row parents is detected (colour count l + 3).
- Swapping one leaf label with one internal label is detected for t = 2 but happens to remain valid for t ≥ 4. Both checkers agree on this, so it is a property of the swap, not a checker defect.

## Gate C: Lean route (QUALIFIED_PASS; nothing was run)

### Review of the draft (`formal-draft/LocalAntimagicEvenTree.lean`)

**Right:**

- The literal definitions are faithful:
  - `IsLocalAntimagic` uses labels `f e + 1` over `edgeSet ≃ Fin |E|`;
  - `chiLA` is the `sInf` of image cardinalities;
  - `numLeaves` counts degree-one vertices.
- The endpoint `chiLA (tree t n) = numLeaves (tree t n) + 1` under `2 ≤ t`, `Even t`, `1 ≤ n` is the right literal target.
- The `le_antisymm` / `Nat.sInf_le` / `le_csInf` skeleton (lines 89–97) is sound.

**Wrong or risky:**

1. Lines 29–30 make the `Fintype (TVert t n)` and `DecidableRel` instances `sorry`. These are data, not proofs. `Fintype.card`, `edgeSet` finiteness and `numLeaves` all depend on them, so the endpoint statement itself would mention `sorryAx`. They must be real instances, for example via an equivalence with Σ h : Fin (n + 1), (Fin h → Fin t).
2. `wsum` and `IsLocalAntimagic` (lines 33–40) lack `[DecidableEq V]`. That instance is needed for `Fintype G.edgeSet` and for decidable membership in `Sym2`. As written, this will very likely not elaborate.
3. `lab` (line 65) is a noncomputable `sorry`, and `pos` (line 58) is unused.
4. The theorem is stated for one canonical model. The source quantifies over every complete full t-ary tree, so either an isomorphism-invariance bridge for `chiLA` plus a uniqueness lemma is needed, or root must accept the canonical model. That choice is root's.
5. `STATEMENT-CORRESPONDENCE.md` does not mention the published-versus-HTML numbering (gate A).

### Cheaper route (validated by my `closed` run)

Use the vertex model (h, i) with 0 ≤ i < t^h, where the parent of (h + 1, i) is (h, i / t). Its cardinality, decidability and degrees are elementary. On this model the n ≥ 3 labelling is piecewise affine with parity cases:

- **Row 1:** [Z, N − t + 2, …, N].
- **Rows 2 to n − 1:**
  - Put r = off(h) + i, where off(h) = t^{h+1} + … + t^{n−1}.
  - Put d = 1 + r / 2. The label is Z − d if r is even, and Z + d if r is odd.
  - The map r ↦ label is a bijection from [0, 2R) onto [1, N − t + 1] \ {Z}, with an explicit inverse.
  - Children sums: the slots 2u and 2u + 1 share the same d, so each pair sums to 2Z and each vertex's children sum to tZ.
  - For t = 2, transpose the row-2 indices 1 and 3.
- **Leaves:**
  - Let the parent label be Z + ε. Put a = ε if ε > 0, and a = q + 1 + ε if ε < 0.
  - Slot j takes λ_b(a) or λ_{t+1−b}(q + 1 − a) when j < t − 2. Slot t − 2 takes λ_{t/2}(a), and slot t − 1 takes λ_{t/2+1}(q + 1 − σ(a)).
  - On parity classes of the parent index p: if p is odd, then a = (p + 1)/2 and q + 1 − σ(a) = q − p; if p is even, then a = q − p/2 and q + 1 − σ(a) = p + 2.
  - Leaf bijectivity therefore reduces to (slot, parent) ↦ N + slot·q + x being injective, with x a permutation of [1, q] in each slot.

With this description, bijectivity, row sums and properness reduce to `omega` and parity case splits, plus `Finset.sum` over pairs of slots.

### Estimate

| Part | Lines |
|---|---|
| Model, degrees and numLeaves = t^n | 300–500 |
| Lower bound | 150–300 |
| n = 1 | about 50 |
| n = 2, t = 2 (fixed instance; `decide` is acceptable here) | about 50 |
| n = 2, t ≥ 4 (Lemma 2.2 pairs and reversed blocks) | 400–700 |
| n ≥ 3: bijectivity | 300–600 |
| n ≥ 3: sums | 200–400 |
| n ≥ 3: range and properness | 200–400 |
| n ≥ 3: t = 2 patch | 100–250 |
| Optional isomorphism bridge | 300–600 |

The total is roughly 1,500 to 3,000 lines without the bridge. This is high but well-structured, and below the lane's "several thousand". Fixed-instance `decide` checks do not prove the theorem.

## Gate D: prior art (QUALIFIED_PASS; bounded, not exhaustive)

**Searched on 2026-11-04.** Receipts are in `dl/` and `hashes/downloads.sha256`.

- **OpenAlex.**
  - The work for DOI 10.3233/FI-222105 (W4223652911) has 3 citing works:
    - Hadiputra–Maryati 2024, on the local *edge* antimagic number;
    - Uma–Rajasekaran 2024, Heliyon, on graph operations;
    - Sarath–Prajeesh 2023, ICEEICT, on diameter-3 trees, certain diameter-4 trees and K_{m,n}.
  - The arXiv record (W7214805693) has 0 citing works.
  - Keyword searches covered "local antimagic" from 2022 on (174 works, all titles screened), "antimagic t-ary" and "antimagic binary tree". None treats even full trees except the source.
- **Gallian's Dynamic Survey DS6**, 28th edition (30 October 2025), lines 11225–11232 of `dl/gallian/ds6.txt`, reports only the odd-t result for complete full t-ary trees.
- **arXiv:2610.22783** (Brondani–França, 16 October 2026), lines 56–58 of the lane copy, says that Bača et al. "verified the conjectured upper bound … and in particular proved that the lower bound is attained when t is odd". It disproves the general ≤ l + 2 tree conjecture with caterpillars and says nothing about even full trees. This is weak evidence that the even case was still open in October 2026.
- **Lau–Shiu–Ng, arXiv:2001.05138** (JDMSC 2022).
  - Theorem 2.1 and Corollary 2.3 add s pendants to every vertex of ONE colour class. T(t, n) is T(t, n − 1) with t pendants on each of t^{n−1} leaves, and each of those leaves is its own colour class, so the theorem does not apply.
  - Their Conjecture 3.1 (on general trees) is a conjecture.
  - Lau–Shiu–Soo (spiders) is not relevant.
- **Registries and the live problem page.**
  - MathDB 354228 shows 0 solutions.
  - openai/math HEAD is still 4eaee875, and the truncated tree listing has no antimagic paths.
  - The Omega registry advanced from 3bb89bf7 to 8a81f0a4 (8 commits, 170 files, none antimagic or labelling related).
- **Theses.** Web searches found no Lai or Tunghai thesis and no Shodhganga thesis on this topic.

**Gaps:**

- **Sarath–Prajeesh (ICEEICT 2023, IEEE, paywalled).** Its abstract mentions "certain classes of diameter 4 trees". T(t, 2) has diameter 4, so this paper could cover n = 2. It cannot cover n ≥ 3, where the diameter is at least 6.
- **Premalatha–Arumugam–Lee–Wang, "Local antimagic chromatic number of trees – I"** (JDMSC 25(6), 2022; online 2020, paywalled). Unread, but it was available before the source was accepted, and the source does not cite it for full trees.
- **NDLTD** (the Taiwanese thesis database) was not searched.

None of these can affect the n ≥ 3 core.

## Gate E: significance and exclusion screen (QUALIFIED_PASS)

**For the candidate:**

- It resolves the full stated scope of an explicitly open conjecture in a refereed paper: all even t and all depths, not a parameter instance.
- The conjecture is about 4.5 years old.
- No public resolution was found by Gallian (October 2025) or the October 2026 citing preprint.

**The n ≥ 3 core is not a source-ingredient bridge** (unlike 347138, 371637 and 374241). The source's own method provably cannot give l + 1:

- its level ordering places a consecutive block of q = t^{n−1} (even) labels on level n − 1;
- its Lemma 2.10 (the parity obstruction) then forces two colours on the second-last row.

The candidate replaces this with three ideas that do not appear in the source:

1. the level n − 1 labels form a symmetric set {Z ± d} with a hole at Z;
2. the permutation σ, whose displacements are exactly ±1, …, ±k, so the needed tuple sums form a symmetric set and the parity obstruction disappears;
3. nested shells that make every internal row a translate of a disjoint label set by tZ inside the leaf range. This replaces the source's six-case comparison.

Two parts are inherited from the source: the reversed-block outer pairs (the method of Lemmas 2.8 and 2.9) and the top-block leaf range.

**Against the candidate:**

- The proof is short and elementary, about two pages.
- The subject is a niche labelling conjecture in Fundamenta Informaticae, so significance is modest.
- The n = 2, t ≥ 4 case is assembled from source Lemma 2.2 and Lemma 2.9 with a new choice of root labels; that sub-case alone would look like a bridge.
- n = 2, t = 2 is the source's Figure 5.
- These weaknesses affect only the n = 2 slice. The general n ≥ 3 argument is new.
- Shortness is not, by the campaign rules, evidence of routineness.

**Family screen.** This is not a parameter variant of the credited 381805. That result concerns a different invariant (super edge-magic total strength) and is a refutation of Deepthi's formula. 354228 is a local antimagic chromatic number result with a different source and different methods.

**Recommendation for E:** count it if root accepts modest significance for a complete resolution. This is a closer call than gates A and B, and the deciding factor is root's significance threshold. It is not a known result, a routine bridge or a family variant.

## Conditions on PROCEED

1. Fix `proof.md` attribution:
   - credit source Figure 5 for case 2.2;
   - map the lemma citations to the published numbers (Lemma 2.9, Lemma 2.10, Conjecture 6.1);
   - say that the n = 2, t ≥ 4 case uses source ingredients.
2. Optionally simplify the step in (f) for rows 1 ≤ h ≤ n − 3 (properness follows from bijectivity alone).
3. Root decides whether the canonical-model endpoint is acceptable, or whether an isomorphism bridge is required.
4. Root may want a focused check of the two paywalled tree papers. Even a positive hit there would remove only the n = 2 slice.
5. In Lean (on Sol), replace the `sorry`'d instances, add the `DecidableEq` binders, and use the closed form above.

## Files

- `REVIEW.md` and `review.json`
- `scripts/verify.py` and `scripts/run-capped.sh`
- `logs/` (18 runs: `.jsonl` stdout and `.stderr` with `/usr/bin/time -v` and rc)
- `hashes/` (inputs before and after, downloads)
- `dl/` (receipts)
