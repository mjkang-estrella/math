# Independent adversarial review: MathDB 362785 (induced paths in G_{q,p})

Reviewer lane: `inducedpath-review-r1` (Claude Opus 5.5, high effort). Date: 2026-11-04.
Reviewed candidate: `expanded-corpus-r175/CANDIDATE-362785.md`, sha256 `c39935f26ab25955b41421ce96f359e6489dc90962a9699bab816309f47e4e54`. This matches the hash in the brief, and the file was unchanged before and after the review.
This is a review, not an acceptance. Root decides.

## Overall recommendation: EXCLUDE

| Gate | Verdict | One-line reason |
|---|---|---|
| A. Statement fidelity | PASS | Definition, quantifiers and conjecture are identical in v1 (2024-04-17) and v2 (2026-03-20). The MathDB literal is hash-bound and faithful. The problem is still open in v2, and live MathDB shows 0 solutions. |
| B. Correctness for all odd q | PASS | I checked every step by hand for all q ≥ 3 (oddness is never used) and all p ≥ 1. My own code agrees, with no counterexample found. Only wording slips. |
| C. Source-ingredient analysis | FAIL | The candidate's one-page new part can be replaced by a 12-line argument (Proposition R below). That argument uses only the source's own Claims `cla:one-edge` and `clm:ordering`, the source's every-third-edge embedding trick, and the q = 3 template of Chudnovsky–Goedgebeur–Schaudt–Zhong. |
| D. Prior art | QUALIFIED_PASS | My bounded screen found no prior resolution: arXiv v1/v2, OpenAlex (0 citing works), MathOverflow, 7 GitHub searches, Lean Pool HEAD and live MathDB. OpenAlex search was paused and dblp served a bot challenge (not retried). |
| E. Significance, exclusion and Lean route | FAIL | It falls squarely in the zero-credit precedent band of short new observations on available source machinery (337352, 336565, 349146). The Lean route is cheap and the draft is a faithful skeleton, but formalising a short bridge does not earn credit. |

**Why EXCLUDE rather than HOLD.** The mathematics is correct in full scope. The issue is credit, and no missing evidence could fix that. Proposition R below proves a strictly stronger statement: G_{q,p} contains no induced (q−1)K₂+K₁. The proof is about 12 lines on the source's own machinery, and the conjecture follows from it in one line, because P_{3q−2} contains an induced (q−1)K₂+K₁. That is exactly how the source got P_{3q−1}-freeness from qK₂-freeness (main.tex lines 1701-1703). It is also exactly how the q = 3 case was proved: G_{3,p} = Pokrovskiy's G_{p−1}, which is (2P₂+P₁)-free by a 10-line ordering argument in arXiv:1703.05684, main.tex lines 2688-2711. The genuinely new content is therefore about 10 to 15 lines and contains no idea beyond the source's machinery. This is the profile the precedents exclude.

---

## Inputs and hash binding

- `hashes/before.sha256` and `hashes/after.sha256` cover 29 read-only inputs. They include the candidate, SUMMARY, results.json, the raw MathDB line, the v2 e-print, the Lean draft, the lane's scripts and logs (read only, never imported or executed), the three AGENTS.md files and the brief. All 29 are identical before and after.
- The MathDB chunk `lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0010.jsonl` has sha256 `404b7005…e949e`, equal to the `chunk_sha256` recorded in results.json. Its line 2017 hashes to `bae6c90c…6dc5`, equal to `raw/362785.jsonl`. Its statement hashes to `d2fe8069…17e3`, equal to the recorded `statement_utf8_sha256`.
- My fresh download of the v2 e-print (`https://arxiv.org/src/2404.11704v2`) is byte-identical to the lane's copy: sha256 `8b748e95…2c4`. My fresh v1 e-print has sha256 `15ce39b8…ab77`.
- Hashes of all downloads and extracted files are in `hashes/downloads.sha256` and `hashes/extracted.sha256`.

## Gate A: statement fidelity (PASS)

**Source.** J. Goedgebeur, J. Jooken, K. Okrasa, P. Rzążewski, O. Schaudt, *Minimal obstructions to C₅-coloring in hereditary graph classes*, arXiv:2404.11704. The versions are v1 (2024-04-17) and v2 (2026-03-20), and v2 is the latest. An extended abstract appeared at MFCS 2024 (LIPIcs, DOI 10.4230/LIPIcs.MFCS.2024.55). Authors and dates were read from the live abs page, `sources/net-arxiv/`.

**Definition** (v2 main.tex lines 1522-1524; v1 line 1533, identical). For odd q ≥ 3 and p ≥ 1, G_{q,p} has vertex set [qp−3]₀ = {0,…,qp−3}, arithmetic modulo n = qp−2, and N(i) = {i−1, i+1} ∪ {i+qj−1 : j ∈ [p−1]}. The parameter p only scales the circulant: n = qp−2, with connection set {±1} ∪ {qk−1 : 1 ≤ k ≤ p−1}. The printed N(i) is symmetric, because (qk−1)+(q(p−k)−1) = n. My code (`scripts/gqp_check.py defs`) confirms that it is symmetric and loopless for q ∈ {3,5,7,9} and every p tested (`logs/gqp_defs.log`).

**Conjecture** `con:path` (v2 lines 1757-1759; v1 line 1768, identical): "Let q ≥ 3 be odd. For every p ≥ 1, the graph G_{q,p} is P_{3q−2}-free." Here P_t-free means no induced P_t. The quantifiers are: for all odd q ≥ 3 and all p ≥ 1. A diff of the whole section between v1 and v2 (`logs/v1-v2-section-diff.txt`) shows only typographical changes: a_{i mod q} subscripts, "induce" changed to "induces", and the acknowledgements moved. The definition, the claims, the conjecture and `lem:lowerpath` are unchanged.

**Sharpness.** `lem:lowerpath` (v2 lines 1764-1794) shows that G_{q,p} contains an induced P_{3q−3} when p ≥ 2q+1, so the bound 3q−3 is attained. My searches attain 3q−3 for q = 3 (from p = 7) and q = 5 (from p = 11).

**Known before the candidate.**
- q = 3: G_{3,p} is P₇-free. The source cites Chudnovsky–Goedgebeur–Schaudt–Zhong, JCTB 140 (2020), at line 1754. I located the actual proof in the companion paper by the same authors, arXiv:1703.05684 ("Obstructions for three-coloring and list three-coloring H-free graphs"), §Necessity, main.tex lines 2674-2711. Pokrovskiy's G_r (3r+1 vertices, v_i ~ v_{i±1}, v_{i+3j+2} for 0 ≤ j ≤ r−1) is literally G_{3,r+1}. Its proof that G_r is (2P₂+P₁)-free, and hence P₇-free, is about 10 lines using the colour order.
- q = 5: proved by computer in the source (lines 1739-1747). The source even shows (P₁₀+P₂)-freeness.
- General q: the source proves only P_{3q−1}-freeness (`lem:infinite-easybounds`, lines 1696-1704), through qK₂-freeness (`lem:qk2-free`, lines 1640-1690).
- So the conjecture was open for odd q ≥ 7.

**MathDB literal** (`raw/362785.jsonl`): "Let q≥3 be odd, let p≥1 … For every p≥1, the graph G_{q,p} is P_{3q−2}-free." It is faithful to con:path. It has two harmless flaws: a broken "Theorem~" reference, and the wording "open for the other cases", which ignores the source's computer proof for q = 5. Live MathDB page fetched 2026-11-05 UTC (`sources/net-mathdb/page.html`): 0 solutions, progress summary "Nothing recorded yet".

## Gate B: correctness for all q (PASS)

I rebuilt the whole argument myself. Throughout, L = 3q−2, n = qp−2 and ρ(v) = v mod q.

1. **Small p (CANDIDATE lines 35-38).**
   - If p ≤ 2, then n ≤ 2q−2 < L.
   - If p = 3, then n = L, so U = V. But G_{q,3} contains the Hamiltonian cycle 0,1,…,n−1 with n ≥ 7, so it has at least n > n−1 edges. Hence U does not induce a path.
   - If p ≥ 4, then n > L. Pick c ∉ U and translate by −(c+1). Translations are automorphisms of a circulant, so we may assume n−1 ∉ U. ✔
2. **Linear rule (lines 40-44).** Take 0 ≤ i < j ≤ n−2 and d = j−i ∈ [1, n−2].
   - d is adjacent iff d ∈ {1, n−1} ∪ {qk−1} ∪ {n−(qk−1) = q(p−k)−1}. Since d ≤ n−2, d ≠ n−1.
   - The values d ≡ −1 (mod q) with d ≤ qp−4 are exactly qk−1 with k ≤ p−1.
   - So i ~ j iff j−i = 1 or j−i ≡ −1 (mod q). ✔ This is the source's `obs:neighbors` after the wrap-around edge 0–(qp−3) is removed.
   - Brute force confirms this rule on [0, n−2] for every pair, every q ∈ {3,5,7,9} and every p tested.
3. **(★) (lines 46-52).** Suppose ρ(u) = ρ(w)+1 and u ≁ w. If u < w, then w−u ≡ −1, so u ~ w, a contradiction. Hence u > w, and u−w ≡ 1 with u−w ≠ 1 gives u ≥ w+q+1. Two vertices of the same residue, or of residues differing by something other than ±1, are never adjacent. This needs q ≥ 3, so that 1 ≢ −1. ✔
4. **Lemma A (lines 54-57).** By (★), v_{s+1} > v_s for every s, and going round the cycle gives v₀ < v₀. ✔ Brute force over all choices confirms Lemma A for q·p ≤ 40.
5. **Lemma B (lines 61-68).** I re-derived both cases.
   - Case a < b: then d < a < b < c, so the edge cd would need c = d+1. Impossible.
   - Case a = b+1: then d ≤ b−q and c ≥ b+q+1 > d, so c = d+1 ≤ b−q+1 < b. Contradiction.
   - The four vertices are distinct and every cross pair is non-consecutive, because j ≥ i+3. ✔
   - Brute force over all pairs of edges in [0, n−2] confirms it for n ≤ 40.
6. **Lemma C (lines 70-79).**
   - (i) If κ_i = κ_{i+2}, then r_i and r_{i+1} both lie in the 2-set κ_i and are distinct, so κ_{i+1} = κ_i. Hence each class occupies one interval of at most 3 edges. ✔
   - (ii) The two classes containing r_β are {r_β−1, r_β} and {r_β, r_β+1}. These are distinct sets even for q = 3. A reversal would make K_{m+2} = K_m, which contradicts (i). So the shifts are monotone and t ≤ q. ✔
   - (iii) K_m ∩ K_{m+1} = {s₀+m}, including for q = 3. Interior runs alternate between two residues and go from s₀+m−1 to s₀+m, so they have odd length. ✔
   - t = 1 is impossible because 3q−3 > 3. The candidate leaves this implicit: its "t ≤ q−1" case gives t = q−1 ≥ 2.
7. **Deficit cases (lines 81-101).** The deficits sum to 3. Interior deficits are in {0, 2}, which forces the four patterns (I.a), (I.b), (II.a) and (II.b), plus the case t = q−1. For each pattern I recomputed β_m and the residue of every chosen vertex symbolically:
   - (I.a) β_m = 3m for m < k and 3m−2 for m ≥ k, giving indices 0, 3, …, 3q−3.
   - (I.b) β_m = 3m−1 for m < k and 3m−3 for m ≥ k. F_m sits at 3m−3, B_m at 3m−3, and x_{L−1} at 3q−3.
   - (II.a) and (II.b) work similarly.
   
   Every chosen set is spaced exactly 3 apart and covers all q residues. ✔ Wording slips only: F₁ when |R₁| = 2, and G_{q−1} when |R_q| = 2, are endpoints of the path, not "interior" vertices. The indices and residues are still correct.

**Adversarial probes.**
- The wrap-around edge is removed by the rotation in step 1.
- The vertex n−1 never lies on the path after rotation.
- At q = 3, every use of ±1 being distinct holds.
- At p = 1, 2 or 3 the case is vacuous or handled by the edge count.
- Paths through former vertex 0 are irrelevant after rotation.
- Boundary runs of length 1 and 2 are covered by the case list.
- The proof never uses that q is odd, so it also proves the statement for even q ≥ 4. This is harmless.

**Machine checks (my own code, `python3 -I`, `ulimit -v` 2 GB, each run in the foreground and under 2 minutes):**
- `scripts/walk_lemma.py` (`logs/walk_lemma_q3-13.log`, `logs/walk_lemma_q14-15.log`). For every q from 3 to 15, odd and even, it enumerates every ±1 residue walk on 3q−2 vertices that satisfies Lemma B, starting at residue 0.
  - There are exactly 4q−2 such walks. Every one has an independent transversal, i.e. pairwise non-consecutive indices covering ℤ_q, found by an exact DP rather than the candidate's construction.
  - Every walk has runs of length ≤ 3, distinct classes, and t ≤ q.
  - On 3q−3 vertices, every Lemma-B walk lacks an independent transversal. So the reduction is tight.
- `scripts/gqp_check.py lip`: exhaustive longest induced path in the literal source graph, with the first endpoint fixed by vertex-transitivity, and every witness re-verified.
  - q = 3, p ≤ 8: maximum 6. By the source's `cor:reducetofinite` this settles all p (`logs/lip_q3.log`).
  - q = 5, p ≤ 14: maximum 12. This also settles all p (`logs/lip_q5.log`).
  - q = 7, p ≤ 10: maximum 16. This is complete for those p but is not a proof for all p (`logs/lip_q7_a.log`, `lip_q7_p9.log`, `lip_q7_p10.log`). No path on 19 or more vertices was found.
- `scripts/matching_plus_vertex.py` checks the stronger statement of Proposition R.
  - It finds no induced (q−1)K₂+K₁ in G_{5,p} for p ≤ 14. Since |V(F)| + 1 = 10, `cor:reducetofinite` makes this all p.
  - It finds none in G_{7,p} for p ≤ 14 or in G_{9,p} for p ≤ 8. The runs at q = 7, p = 15 and q = 9, p = 9 hit their caps (`logs/matching_plus_vertex_q5.log`, `logs/matching_plus_vertex_q7_q9.log`).
- `scripts/short_route_check.py` checks the intermediate ordering claim of Proposition R on every induced (q−1)K₂ in the rotated model, with 0 violations (`logs/short_route_check.log`): q = 3, p = 8 (45 matchings); q = 5, p = 11 (45); q = 5, p = 12 (225).

## Gate C: source-ingredient analysis (FAIL)

**Ingredients the source already contains.**

| Candidate step | Source | Comment |
|---|---|---|
| Step 1 linear rule | `obs:neighbors` and its corollary, main.tex lines 1531-1540 | The only addition is the rotation that deletes the wrap-around edge, one line. The source's `lem:reducetofinite` (lines 1587-1622) already exploits the same linear model. |
| (★) | Implicit in every case of `cla:one-edge` and `clm:ordering` ("(j,i′) is of type (s+1,s), so ji′ is an edge") | One line. |
| Lemma A | The final paragraph of `lem:qk2-free` (lines 1685-1690): the same cyclic-order contradiction, applied to matching edges instead of vertices | Three lines. |
| Lemma B | Exactly `cla:one-edge` (lines 1646-1664), applied to the induced 2K₂ formed by path edges three apart | The candidate's own credit-risk section says so. |
| Every-third-edge embedding | `lem:infinite-easybounds`, line 1701 | |

**The candidate's new part** is Lemma C plus the deficit case analysis: CANDIDATE lines 70-101, about 32 lines or one page.

**My finding: that page is not needed.** The following argument proves a stronger statement in about 12 lines from the same ingredients.

> **Proposition R.** For every q ≥ 3 and p ≥ 1, G_{q,p} contains no induced (q−1)K₂+K₁.
>
> *Proof.* (q−1)K₂+K₁ has 2q−1 < n vertices when p ≥ 3; when p ≤ 2 it does not fit, since n ≤ 2q−2. So rotate as in step 1 and work in the linear model on [0, n−2]. Let the edges be M and the isolated vertex v.
>
> By `cla:one-edge`, the q−1 edges have distinct classes, so exactly one class {c, c+1} is missing. Write the edge of class {c+j, c+j+1} (1 ≤ j ≤ q−1) as A_jB_j, with ρ(A_j) = c+j+1 and ρ(B_j) = c+j. All cross pairs are non-adjacent, so (★) gives:
> - A_{j+1} > A_j and B_{j+1} > B_j;
> - B₁ > A_{q−1}, since ρ(B₁) = c+1 = ρ(A_{q−1})+1.
>
> Hence A₁ < … < A_{q−1} < B₁ < … < B_{q−1}. This is the source's `clm:ordering`, read along the chain.
>
> Let ρ(v) = c+j. Since v is anticomplete to M, (★) gives:
> - if 2 ≤ j ≤ q−1, then A_j > v > B_{j−1} ≥ B₁ > A_{q−1} ≥ A_j;
> - if j = 1, then A₁ > v > A_{q−1} ≥ A₁;
> - if j = 0, then B₁ > v > B_{q−1} ≥ B₁.
>
> Each case is a contradiction. ∎
>
> **Corollary (Conjecture con:path, all q ≥ 3, all p ≥ 1).** The induced path x₀…x_{3q−3} contains the induced (q−1)K₂+K₁ formed by {x_{3i}x_{3i+1} : 0 ≤ i ≤ q−2} together with x_{3q−3}. The index gaps are all ≥ 2. ∎

The checks above confirm both the ordering claim and (q−1)K₂+K₁-freeness wherever they were run. This route also needs no p = 3 special case and no run or deficit analysis.

**Measure of genuinely new content.** The new content is the observation "test (q−1)K₂+K₁ instead of qK₂", plus the 4-line vertex step. That is about 10 to 15 lines, a combination of:
- the source's `cla:one-edge` and `clm:ordering`;
- the source's own embedding trick;
- the q = 3 proof of Chudnovsky et al., which is exactly this (2K₂+K₁) argument for q = 3.

There is no new idea beyond that available machinery. The candidate's one-page run analysis is a longer route to the same conclusion. It does not add an idea that the short route lacks.

## Gate D: prior art (QUALIFIED_PASS)

All requests were made on 2026-11-05 UTC with TLS verification on. Receipts are in `logs/net-*.log`, with hashes in `hashes/downloads.sha256`.
- **arXiv:** abs pages for v2 and v1, and e-prints for v1 and v2. Two `/e-print/` 301 responses redirected to `/src/` on the same host, which had not denied anything; I followed them explicitly. v2 is the latest version and still states con:path as open. I fetched the q = 3 companion arXiv:1703.05684 (abs and e-print) and read its proof.
- **Authors' later work:** the `arxiv.org/a/` atom listing for Rzążewski (91 entries, read through 2026-10-30) shows no follow-up on G_{q,p} or minimal C₅-obstructions. Its 2024-onward abstracts were screened for obstruction, C₅, odd girth, Pokrovskiy and G_{q. The listings for Goedgebeur, Jooken and Okrasa returned 404 (ID guesses), which is a limitation.
- **OpenAlex:** the arXiv DOI resolves to the merged MFCS record W7111069160, with `cited_by_count` 0, and the `cites:` filter returned 0 works. Title search returned 503 "anonymous search paused". I did not retry it, which is a limitation.
- **dblp:** the search API served a bot challenge (Anubis). I stopped and did not retry.
- **MathOverflow** (Stack Exchange API, 3 queries): 0 hits.
- **GitHub repository search:** 7 queries spaced 12 s apart, all HTTP 200 with 0 results: G_{q,p} induced path, Pokrovskiy graph, C5-coloring obstructions, 2404.11704, minimal obstructions coloring graphs, induced path circulant graph, mathdb lean graph conjecture.
- **Lean Pool:** HEAD `01db1d7049cf9668bda1e9e106875ee1278b43e6` (2026-10-07), the same HEAD the lane saw. `projects.yml` is 404 at HEAD, because the file no longer exists at the root. I grepped `candidates/` (discovered.yml, shortlist.md, decisions.jsonl and both queues) for the authors, 2404.11704, 362785, obstruction, Pokrovskiy, induced path and C5: there are no relevant hits, only unrelated "obstruction" repositories.
- **Live MathDB:** 0 solutions.
- **Not used, as the brief directed:** Crossref, Semantic Scholar, the arXiv search API and ScienceDirect.

No public resolution was found. The screen is bounded and does not include Google Scholar, so absence of evidence is not proof of novelty. This does not change the outcome, because Gate C fails on its own terms.

## Gate E: significance, exclusion screen and Lean route (FAIL)

**Exclusion screen.**
- The result settles a stated open conjecture in full scope, and the source's five authors left it open across two versions (2024 and 2026). Those are the points in its favour.
- Against it: the decisive content is a short argument on the source's own machinery. It is a direct analogue of the source's own P_{3q−1} derivation and of the published q = 3 proof.
- That matches the zero-credit precedents: 337352 ("a four-line lemma on source-family machinery"), 336565 ("a three-line identity plus a source lemma"), and 349146 ("a page of elementary counting on a source reduction").
- It does not match the qualifying precedents (354228, 342364, 338887, 343536, 356756). Each of those needed a genuinely new mechanism.
- Significance is moderate at best. The result sharpens the path bound of one construction by a single vertex, and the bound itself was the authors' explicit guess.

**Lean endpoint.** The literal target is:

`∀ q p, Odd q → 3 ≤ q → 1 ≤ p → IsEmpty (pathGraph (3*q-2) ↪g Gqp q p)`

with `Gqp q p : SimpleGraph (ZMod (q*p-2))`, adjacency `i ≠ j ∧ (conn (j-i) ∨ conn (i-j))`, and `conn d := d = 1 ∨ d = -1 ∨ ∃ k ∈ Icc 1 (p-1), d = ↑(q*k-1)`. Mathlib's `↪g` is an induced embedding. I find this faithful to the printed N(i). n ≥ 1 always holds, so ZMod 0 never arises.

**Draft** `lean/InducedPathGqp.lean` (82 lines, uncompiled, 4 `sorry`s):
- The definitions and the main statement (lines 18-44) are a faithful skeleton.
- `walk_has_transversal` (lines 72-80) has the right conclusion (non-consecutive indices). Its binder-level `by omega` proofs may need restructuring.
- No proof is present, so the draft has no certificate value.

**Cost estimate.** The candidate's route needs about 1.5 to 3 thousand lines. Proposition R needs roughly 400 to 900 lines: the rotation and ZMod-to-ℕ linear rule, (★), `cla:one-edge`, the chain order, the vertex step, and extracting (q−1)K₂+K₁ from `pathGraph`. Feasibility is not the blocker. Credit is.

## Process notes (candid)

- Two of my commands overran the 2-minute foreground limit and were moved to the background automatically. The first was the initial `walk_lemma.py 25` run before I added pruning; its partial output is `logs/walk_lemma.log`, superseded by the chunked logs. The second chained two capped runs. I stopped both with TaskStop. Both had already printed or finished their work, and I confirmed that no process was left. The harness wrote their transient output files under its own `/tmp/claude-1000/…/tasks/` directory. I did not write anything there.
- I did not run Lean, lake, leanchecker or any SAT/ILP solver, and I did not start any child agent. I never imported or executed the lane's scripts. All downloads went into fresh lane-local directories and were extracted with `tarfile` `filter="data"` under `python3 -I`.

## Files

- `REVIEW.md`, `review.json`
- `scripts/`: `walk_lemma.py`, `gqp_check.py`, `matching_plus_vertex.py`, `short_route_check.py`, `untar_safe.py`
- `logs/`: computation logs, network receipts (`net-*.log`), and `v1-v2-section-diff.txt`
- `hashes/`: `before.sha256`, `after.sha256`, `downloads.sha256`, `extracted.sha256`
- `sources/`: arXiv pages and e-prints (v1, v2, 1703.05684), OpenAlex, MathOverflow, GitHub, Lean Pool and MathDB responses
