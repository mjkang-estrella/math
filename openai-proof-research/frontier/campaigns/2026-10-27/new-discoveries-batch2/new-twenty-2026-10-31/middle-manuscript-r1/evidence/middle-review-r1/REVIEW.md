# middle-review-r1: independent adversarial review of MathDB 355217

Reviewer: Claude Opus 5.5, Claude lane, 2026-11-03 (UTC 23:19 to 23:45). This is a review, not an acceptance. Root decides.

Candidate under review: the connected 8-vertex graph G8 (edges 01 06 16 23 27 37 46 47 56 57 67) from lane expanded-corpus-r139, claimed to refute Conjecture 7.1 of Kazemnejad, Pahlavsay, Palezzato and Torielli, arXiv:2206.15439v1: "Let G be a graph of order n ≥ 2. Then γ̃c(G) < γ̃c(M(G))."

## Verdicts

| Gate | Verdict | One-line reason |
|---|---|---|
| A. Statement fidelity | PASS | Definitions and conjecture read from the primary text. G8 lies in every reasonable domain (connected, has edges). It contradicts no proved source theorem. |
| B. Independent mathematics | PASS | Own proofs and own code give γ̃c(G8) = 4 = γ̃c(M(G8)). The exhaustive search over all 12346 graphs of order 8 (and all smaller orders) reproduces the lane's result. The family and the matching lemma are correct. |
| C. Lean route | QUALIFIED_PASS | The cheapest route is literal and small. The draft's design is right, but two of its three endpoints are trivially provable from the edgeless 2-vertex graph, and one decide step is a real performance risk. |
| D. Prior art | QUALIFIED_PASS | Bounded check (arXiv and OpenAlex only). There are zero citing works, no follow-up discusses Conjecture 7.1 or 7.6, and G8 or its family appears nowhere that was searched. |
| E. Significance and exclusion | QUALIFIED_PASS | This is a genuine refutation and not a routine consequence or a source-ingredient bridge: the hard inequality, γ̃c(G8) ≥ 4, has no source ingredient. Significance is limited by an unrefereed, uncited source whose own evidence for the conjecture contains errors. |

**Overall recommendation: PROCEED** to Lean formalisation. Two conditions apply:
- The counted endpoint must be the connected (or at least non-edgeless) negation, with explicit values. The bare literal negation is not enough (see C).
- Root should weigh the venue and near-tightness points in E. A HOLD on significance alone would be defensible; EXCLUDE as a bridge would not, in my view.

## 0. Inputs, hashes and discipline

- Read-only inputs were hash-bound before and after the review: `input-hashes-before.txt` and `input-hashes-after.txt`. All 19 files are byte-identical (the diff is empty).
  - Files covered: SUMMARY.md, results.json, raw/355217.jsonl, work355217/{PROOF.md, ocd.py, family.py, verify_witness.py, lean/MiddleOCD.lean}, the 2206.15439 and 2308.02127 pdf, txt and abs files, pdf-receipts.txt, abs-receipts.json, root-integration.json, launch.json and TASK.txt.
  - Example: the source PDF has sha256 `446c68bb…f9d7` and the text has `1416b32c…7e`.
- The discovery lane's scripts were read only. They were not imported or executed. All code here is my own (`scripts/`), written from Definitions 1.2 and 1.3.
- Every computation ran through `scripts/run.sh`, one process at a time. That wrapper applies `python3 -I`, `prlimit` CPU 120 s and AS 2 GiB, `timeout 140`, `taskset` 2 CPUs and `MALLOC_ARENA_MAX=2`. The largest peak RSS was 33.8 MB (gen8) and the longest run took 5.6 s CPU (conj76_n8). Receipts are in `logs/*.receipt.json`. No background job remains.
- No Lean, lake, leanchecker or solver binary was run. No git. Nothing was written outside this lane. No child agents were used.
- Network: 16 GETs to arxiv.org and api.openalex.org, with no retries (`downloads/receipts.jsonl`). One guessed arXiv author-page URL returned 404 and was not pursued. Crossref, Semantic Scholar, the arXiv search API and ScienceDirect were not contacted.

## A. Statement fidelity: PASS

Primary text is `expanded-corpus-r139/sources/txt-2206.15439.txt` (line numbers below), checked against the PDF hash above. The live abs page re-fetched today has the identical sha256 `9ff794c1…` and shows v1 only.

- **Standing assumption** (lines 31–33): "we assume that every graph is non-empty, finite, undirected and simple." Connectivity is not assumed globally.
- **Definition 1.2** (lines 55–58): a dominating set S is outer-connected if G − S is connected, and γ̃c(G) is the minimum cardinality. The text gives **no convention** for an empty or one-vertex complement.
  - With a one-vertex complement, G − S = K1 is connected under any convention.
  - With an empty complement, only S = V is affected. For connected G with n ≥ 2, S = V − {v} is always OCD, so the convention never changes γ̃c of a connected graph or of M(G).
  - I computed both conventions throughout: A (the empty graph counts as connected) and B (the complement must be non-empty). They agree on G8 and M(G8).
- **Definition 1.3** (lines 63–75): M(G) has vertex set V(G) ∪ E(G). Edge nodes are adjacent when the edges share an endpoint, a vertex node and an edge node are adjacent when incident, and two vertex nodes are never adjacent. My `middle()` implements exactly this.
- **Conjecture 7.1** (lines 460–461, page 11): "Let G be a graph of order n ≥ 2. Then γ̃c(G) < γ̃c(M(G))." The MathDB record (`raw/355217.jsonl`) matches it word for word.

**Intended domain.**
- Every Section 3–6 theorem that is not about a specific family assumes connectivity: Theorem 3.1 (line 113), Theorem 4.1 (line 135), Theorem 4.7 (line 194), Theorems 5.2, 5.4, 5.6 and 5.7, and Corollary 6.2.
- The Section 7 evidence (lines 451–458) consists only of connected families.
- Conjecture 7.1 itself says only "graph of order n ≥ 2". So the literal domain is all non-empty finite simple graphs, and the intended domain is very likely connected graphs.

**G8 is in both domains.** G8 is connected (own check), has 11 edges, and n = 8.

**Literal-domain artefact.** My exhaustive run over all graphs, disconnected ones included, gives `logs/search2to7.log` and `logs/search8.log`. For 2 ≤ n ≤ 8, the only failures of 7.1 are:
- the edgeless graphs nK1, where M(G) = G and γ̃c = n on both sides under convention A (under convention B, γ̃c is undefined on both sides); and
- G8, up to isomorphism.

No disconnected graph with at least one edge fails for n ≤ 8. If "non-empty" in the standing assumption is read in the Bondy–Murty sense (empty = edgeless; reference [2], line 514), the edgeless graphs are outside the source's domain, and G8 is then the smallest literal counterexample too. Caveat: I recall this Bondy–Murty usage from memory; it was not verified against the book in this lane.

Either way, the MathDB problem as literally worded ("a graph of order n ≥ 2") is trivially falsified by 2K1 under convention A. So **root must not count the bare literal negation**. The creditable statement is the connected (equivalently, non-edgeless) negation, which G8 supplies. This matches lane PROOF.md line 15, which correctly disclaims the 2K1 case.

**No conflict with proved source results.**
- Theorem 4.1 (lines 135–145, connected G): ⌈8/2⌉ = 4 ≤ γ̃c(M(G8)) = 4 ≤ 8. Equality holds at the lower end.
- Corollary 4.2 (line 147): ρ(G8) = 4 ≤ 4.
- Theorem 2.1 (Cyman, line 96): γ̃c(G8) = 4 ≤ n − δ = 6.
- Theorem 4.3 and Corollary 4.5 (trees) and Theorem 4.7 (γ̃c(M(G)) = n iff G is a tree, for n ≥ 4): G8 is not a tree and 4 ≠ 8, so they are consistent.
- Theorems 4.8 (K_n), 4.10 (C_n), 4.11 (W_n), 4.12 (K_{n1,n2}) and 4.13 (F_n): G8 belongs to none of these families. It is also not a corona, 2-corona or join with K_p (it has no leaves and no universal vertex), so Theorems 5.2–5.7 do not apply.

I also re-checked Theorems 2.1, 4.1, 4.2, 4.3 and 4.7 on all 995 connected graphs with 2 ≤ n ≤ 7 and found no violation (`logs/source_thms.log`).

**Source-internal errors** (these do not involve G8, but they are relevant to E):
1. **Theorem 4.12 is false at K_{2,2}** (lines 276–287), and it contradicts the source's own Theorem 4.10 there, because K_{2,2} = C4.
   - Theorem 4.12 gives γ̃c(M(K_{2,2})) = 2. Theorem 4.10 gives γ̃c(M(C4)) = 3, and 3 is correct.
   - Proof: any 2-element dominating set of M(C4) is the edge-node set of a perfect matching F (by the counting argument). C4 − F = 2K2 is disconnected, so by the matching lemma it is not OCD.
   - The source's construction {m11, m22} leaves M − D with two components, v1–m12–u2 and v2–m21–u1.
   - My code agrees with Theorem 4.12 at K_{2,3}, K_{2,4}, K_{2,5}, K_{3,3}, K_{3,4} and K_{3,5} (`logs/source_thms.log`).
   - The conjecture still holds at K_{2,2}: 2 < 3.
2. **The Section 7 evidence line "1 = γ̃c(Fn)" (line 455) is wrong.**
   - Removing the hub leaves n disjoint edges. If the hub is not in S, each blade pair must meet S (each blade vertex v has N[v] = {v, its partner, hub}). If the hub is in S, at most one blade pair survives outside S.
   - Hence γ̃c(F_n) = n, which my code confirms at n = 2 and 3 (`logs/witness.log`), while γ̃c(M(F_n)) = n + 1.
   - So the source's own friendship family is tight up to 1, not separated by n. See E.

## B. Independent mathematics: PASS

### B.1 Own proof that γ̃c(G8) = 4

Name the blocks X = {0,1}, Y = {2,3}, T = {4,5} and hubs 6 and 7. Then N[0] = N[1] = {0,1,6}, N[2] = N[3] = {2,3,7}, N[4] = {4,6,7} and N[5] = {5,6,7}.

Let S be OCD with |S| ≤ 3. Then R = V − S has at least 5 vertices, so the convention is irrelevant.

- **If 6 ∉ S:** domination of 0 forces S ∩ X ≠ ∅.
- **If 6 ∈ S:** a vertex of X lying in R has all its R-neighbours inside X, so either X ⊆ S or R ⊆ X. R ⊆ X would give |S| ≥ 6. Hence S ⊇ X ∪ {6}.
- The same two facts hold for Y and hub 7.
- **If 6, 7 ∉ S:** domination of 4 and 5 forces T ⊆ S.

Cases:
- Neither hub in S: |S| ≥ 1 + 1 + 2 = 4.
- Exactly one hub in S: |S| ≥ 3 + 1 = 4.
- Both hubs in S: |S| ≥ 6.

Each case is a contradiction.

The upper bound is S = {0,2,4,5}: the complement {1,3,6,7} contains the path 1–6–7–3, and the domination checks pass. My code finds exactly 8 minimum OCD sets, the same under both conventions:
- {0,2,4,5}, {1,2,4,5}, {0,3,4,5}, {1,3,4,5}
- {0,1,2,6}, {0,1,3,6}, {0,2,3,7}, {1,2,3,7}

This matches PROOF.md line 65 and root's set {0,1,2,6}. The lane's argument (PROOF.md lines 25–34) is correct.

### B.2 Own proof that γ̃c(M(G8)) = 4

M(G8) has 19 nodes and 48 edges.

- **Lower bound.** Vertex nodes are pairwise non-adjacent. A vertex node's closed neighbourhood contains one vertex node, and an edge node's contains two. So every dominating set has at least 8 / 2 = 4 elements. This uses only domination; the convention is irrelevant.
- **Upper bound.** Take D = {m01, m23, m46, m57}.
  - Every vertex is covered by its matching edge.
  - Every other edge shares an endpoint with a matching edge.
  - M − D contains all 8 vertex nodes and the 7 edge nodes of G8 − F = {06, 16, 56, 67, 27, 37, 47}. That edge set is a spanning tree, so M − D is connected.

Brute force over all 5036 subsets of size ≤ 4 of the 19 nodes finds no OCD set of size ≤ 3 (no dominating set of size ≤ 3 exists) and exactly two of size 4: {m01, m23, m46, m57} and {m01, m23, m47, m56}. These are the two perfect matchings of G8, and both have connected remainder (`logs/witness.log`). This agrees with PROOF.md line 65.

### B.3 Own exhaustive search

`scripts/gen.py` is isomorphism-filtered augmentation:
- Every graph on n vertices is obtained from some class representative on n − 1 vertices by adding one vertex with an arbitrary neighbourhood.
- Duplicates are removed by colour-refinement buckets followed by an exact backtracking isomorphism test.

The counts are 1, 2, 4, 11, 34, 156, 1044 and 12346 graphs (OEIS A000088) and 1, 1, 2, 6, 21, 112, 853 and 11117 connected graphs (A001349) for n = 1…8 (`logs/gen7.log`, `logs/gen8.log`).

`scripts/search.py` then takes **every** graph, connected or not, under both conventions:
- It computes γ̃c(G) by enumerating all 2^n subsets.
- It decides whether M(G) has an OCD set of size ≤ γ̃c(G) by an exact branching search. The search branches on the undominated node with the smallest closed neighbourhood. At each dominating partial set it tries every superset of the target size, which is needed because outer-connectivity is not monotone.

The branching search was cross-validated against plain brute force on M(G) for all 189 graphs with 2 ≤ n ≤ 6 and |V(M)| ≤ 16, under both conventions: 378 comparisons with 0 mismatches (`logs/xval.log`).

Results:
- **Connected graphs with n ≤ 7:** no failure.
- **n = 8:** exactly one connected failure, with edges 04 06 15 17 26 27 36 37 46 57 67. My isomorphism test confirms it is isomorphic to G8. It is an equality (4 = 4), not a reversal.
- **Disconnected graphs:** only the edgeless graphs fail (see A).

This confirms PROOF.md lines 63–65: none for n ≤ 7, and G8 is unique at n = 8. It also shows there is no reversal γ̃c(G) > γ̃c(M(G)) for n ≤ 8.

Of the 676 connected 8-vertex graphs with γ̃c(G) ≥ 4, 389 have gap γ̃c(M) − γ̃c(G) ≥ 2, 286 have gap exactly 1, and only G8 has gap 0.

### B.4 Matching lemma and family

**The lemma (PROOF.md lines 51–53) is correct.**
- (⇒): a dominating set of size n/2 must consist of edge nodes covering each vertex exactly once, that is, a perfect matching F. A path in M − D between vertex nodes projects to a walk in G − F.
- (⇐): as in B.2.

Computationally, for every connected graph of even order n ≤ 8, I compared "M(G) has an OCD set of size n/2" (decided by exact search, not by the lemma) with "G has a perfect matching F with G − F connected". The tallies were 1, 6, 112 and 11117 graphs with 0 disagreements, and no OCD set below n/2 was ever found (`logs/lemma.log`).

**The family G_{a,b} (PROOF.md lines 55–59) is correct for a, b ≥ 1.** I re-derived the four-case proof:
- Neither hub in S: |S| ≥ 2 + a + b.
- Only x in S: |S| ≥ 2a + 1 + b ≥ a + b + 2, which uses a ≥ 1.
- Both hubs in S: |S| ≥ n − 2.

The upper-bound set {t, u, α_i, γ_j} works. Computationally, for all 1 ≤ a ≤ b ≤ 3 (n = 8 to 16):
- γ̃c(G_{a,b}) = n/2 by full enumeration;
- the matching set is OCD in M;
- F is perfect and G − F is connected;
- the exact γ̃c(M) is n/2 for (1,1) and (1,2);
- G_{1,1} is isomorphic to G8 (`logs/family.log`).

The condition a, b ≥ 1 is necessary: with a = 0, the case "only x in S" gives 1 + b < b + 2.

A compact description: G8 is the diamond K4 − e on {4,5,6,7} with a triangle glued at each of its two degree-3 vertices. G_{a,b} glues the friendship graphs F_a and F_b at the two ends of a diamond.

## C. Lean route: QUALIFIED_PASS (design only; nothing compiled here)

### C.1 Cheapest literal endpoint (recommended to Sol)

- Keep the literal vertex type of the middle graph, `W ⊕ G.edgeSet` (as the draft does). Do not use `Fin 19`, which would need an extra isomorphism bridge back to Definition 1.3.
- Define `IsDominating`, `IsOCD` (`Preconnected` complement, convention A) and `IsOCD'` (`Connected` complement, convention B) exactly as the draft does at lines 28–38.
- State minima as `IsLeast {k | ∃ S, IsOCD G S ∧ S.card = k} 4` rather than only through `sInf`. That makes the endpoint independent of the `sInf ∅ = 0` default, which matters for convention B on degenerate graphs. Then derive the `ocd`/`ocd'` equalities from it.
- Final theorems, each for both conventions **separately**:
  1. `G8.Connected`, and `G8.edgeSet.Nonempty` (or the explicit 11-edge list).
  2. `IsLeast {k | ∃ S, IsOCD G8 S ∧ S.card = k} 4` and `IsLeast {k | ∃ S, IsOCD (middle G8) S ∧ S.card = k} 4`, plus the primed versions.
  3. `¬ ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.Connected → 2 ≤ Fintype.card W → ocd G < ocd (middle G)`, and the same with `ocd'`.
  4. Optionally, a separately labelled control lemma for the edgeless 2-vertex graph, so the reader sees that the unrestricted literal negation is trivial.

### C.2 Kernel cost

| Item | Size | Estimated cost |
|---|---|---|
| G8 lower bound, by enumeration | 1 + 8 + 28 + 56 = 93 subsets of size ≤ 3 of 8 vertices | Each needs a domination test (≤ 8 vertices × 3) or a separation certificate, so the raw work is about 10^4 elementary steps. Real cost depends on the encoding (see C.3). Via the hand proof (B.1, a case split on 6 ∈ S and 7 ∈ S, plus `not_preconnected_of_closed` with explicit closed sets {0,1}, {2,3}, …), the kernel cost is negligible. |
| M(G8) lower bound | — | No enumeration is needed: the generic counting lemma, `two_mul_card_ge_of_dominating_middle`, gives \|D\| ≥ 4. |
| Brute-force alternative for M(G8) | C(19, ≤ 3) = 1 + 19 + 171 + 969 = 1160 subsets | Feasible only with an explicit combination list. It is infeasible through `Fintype (Finset (Fin 8 ⊕ edgeSet))`, which has 2^19 = 524288 elements. Not recommended. |
| Witnesses | One OCD set per side | One parent-map connectivity certificate each, with depth ≤ 4. Negligible. |

### C.3 Audit of the uncompiled draft `work355217/lean/MiddleOCD.lean` (sha256 `994678e2…`)

Correct:
- The definitions (lines 28–67) match Definitions 1.2 and 1.3. In particular, edge–edge adjacency is `e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f` and vertex–vertex adjacency is `False`.
- `reach_of_parent` and `connected_of_parent` (lines 91–113) are sound parent-map certificates.
- `not_preconnected_of_closed` (lines 116–129) is sound. The `badCert` design (lines 234–237) checks closure rather than trusting the iteration count, so it is sound.
- The vertex-node counting lemma (lines 133–172) and `dominating_middle_of_mate` (lines 175–186) are mathematically right.
- The data checks out: S0 = {0,2,4,5}, the parent map p0/d0 on {1,3,6,7}, the matching `mate`, D8, the tree parent `tp` (2, 3, 4 → 7, others → 6, avoiding F), `dv`, `lowEnd` and `depM`. The depth arithmetic 2·dv(tp w) + 1 < 2·dv(w) holds because dv(tp w) = dv(w) − 1.

Wrong or weak:
1. **Endpoint strength (fidelity).** `conjecture71_false` (line 391) and `conjecture71'_false` (line 398) are true, but each is also provable from the edgeless graph on `Fin 2`:
   - convention A: `ocd = 2` on both sides;
   - convention B: no OCD' set exists, so `sInf ∅ = 0` on both sides and `0 < 0` fails.

   So these two endpoints do not certify G8's content and must not be the counted endpoints.
2. **`Conjecture71Connected` (lines 79–81)** conjoins both conventions. Refuting `∀ G, conn → (A ∧ B)` only shows one convention fails, and the proof (line 407) uses `.1`. Split it into two connected statements, as in C.1.
3. **Performance risk: `all_small_bad` (lines 242–243)**, a kernel `decide` over `∀ S : Finset (Fin 8), S.card ≤ 3 → badCert S`.
   - This enumerates `Finset.univ : Finset (Finset (Fin 8))` (256 elements via `powerset`/`sublists` on quotients).
   - For each S it evaluates `cl S u` (8 iterations of `filter`/`∪` on Finsets) inside `∃ u v` and `∀ a b` (64 × 64 pairs), and the term is recomputed without sharing.
   - I estimate 10^7 to 10^8 kernel reductions, with a real risk of timeout or `maxRecDepth`. The comment's "93 subsets" undercounts the work, because `decide` still walks all 256.
   - Recommended replacements, in order: (a) the hand case proof (B.1); (b) per-subset explicit certificates (dominator failure, or a separating pair together with an explicit closed list), generated offline and checked one at a time; (c) a `Nat`-bitmask checker with a proved bridge lemma.
4. **Fragility to expect** (not errors):
   - `rfl` proofs of `adjB a b = true` inside `mate` and `D8` (lines 279–288); `by decide` is safer.
   - `simp [S0]` proving Fin-literal non-membership (line 221).
   - `tree_ok` (lines 339–343) relies on `Decidable (∃ h : p, q h)`, `lowEnd` and `Sym2.lift` reducing in the kernel. Its `fin_cases` fallback is reasonable.
   - `induction e using Sym2.ind` with the dependent hypothesis `he` (lines 157 and 182) may need explicit `revert`.
   - The name `Finset.card_le_two` (line 167) should be checked against the pinned Mathlib.

## D. Prior art: QUALIFIED_PASS (bounded)

Searches on 2026-11-03 used arXiv abs pages and the OpenAlex API only; receipts are in `downloads/receipts.jsonl`.

- **Source status.** arXiv:2206.15439 has v1 only (20 June 2022) and no journal reference. OpenAlex lists it as W4283778727 with `cited_by_count` 0, and the explicit `filter=cites:W4283778727` query returns **0** works. Across all four authors' OpenAlex records since 2022 (author IDs A5079488761, A5022980613, A5084024396 and A5085209235), I found **no journal version**.
- **Follow-up.** arXiv:2308.02127v1 ("Total outer-connected domination number of middle graphs", W4385644199, also 0 citing works) cites 2206.15439 as an arXiv preprint (its reference [12], txt lines 574–575). The word "conjecture" does not occur anywhere in its text. So it neither resolves nor restates 7.1 or 7.6.
- **Wider sweeps.** I ran two OpenAlex searches and read the top 100 titles of each:
  - "outer-connected domination", 2022 onward: 6820 hits;
  - "middle graph domination", July 2022 onward: 5490 hits.

  No work other than the two above treats outer-connected domination of middle graphs. Two candidates were opened and are unrelated:
  - Kim, "Domination-related parameters in middle graphs", DMAA 2023, W4384382946: it does not cite the source, and its abstract covers Italian, rainbow, Roman, secure and total parameters.
  - Zhang, Li and Dong, "Partial domination of middle graphs", arXiv:2501.02879: isolation number.
- **Conjecture 7.6 (MathDB 355218).** I found no resolution. Diagnostic only: γ̃c(L(G8)) = 2 ≤ 4, so G8 does not touch 7.6. My exhaustive probe over all connected graphs with n ≤ 8 found no counterexample to 7.6 except the degenerate K2 under convention B, where L(K2) = K1 has no OCD' set (`logs/conj76*.log`).
- **G8 or G_{a,b}** appears in nothing found.
- **Limits.** No Google Scholar, MathSciNet, zbMATH or publisher search was made; Crossref, Semantic Scholar and the arXiv search API are denied routes. OpenAlex author disambiguation may split records. Registry checks (Omega and openai/math HEADs) were done by the discovery lane and were not repeated here.

## E. Significance and exclusion screen: QUALIFIED_PASS

**Is it a routine consequence of Theorem 4.1 plus an obvious construction? No.**
- Refuting 7.1 needs two inequalities: γ̃c(M(G8)) ≤ 4 and γ̃c(G8) ≥ 4.
- Theorem 4.1's ⌈n/2⌉ bound is a lower bound on M(G). It is only used to pin equality and plays no role in the failing direction.
- The M-side upper bound is the source's own matching pattern (the D sets of Theorems 4.8 and 4.11). That part is a source ingredient, and the matching lemma is a light restatement of the Theorem 4.1 counting.
- The decisive inequality is γ̃c(G8) ≥ 4, a lower bound on the outer-connected domination number of G itself. The source never proves a lower bound on γ̃c(G); it only quotes Cyman for family values, and some of those are wrong (A, error 2).

**Is it a source-ingredient bridge like 347138, 374241 or 371637? No.**
- In those cases a source lemma or obstruction already carried the failing inequality: Theorem 19(b) and Proposition 12, Corollary 4.19, and Lemma 4.2 respectively.
- Here no source result implies γ̃c(G8) ≥ 4. None of the source's operations (corona, 2-corona, join with K_p) or families yields a counterexample; I checked their stated values and found only strict inequalities.
- The graph is the unique smallest connected counterexample (n ≤ 8) and is not a classical extremal graph.
- It is not a wording or domain artefact: it is connected and refutes the intended statement.

**What weighs against it (root should see this plainly):**
1. **Near-tightness inside the source's own families.**
   - The source's cycles already have a gap of exactly 1: γ̃c(C_n) = n − 2 versus n − 1.
   - With the correct value γ̃c(F_n) = n, which the source misreports as 1 (line 455), the friendship graphs also have gap 1, and their M side already meets ⌈n/2⌉.
   - G8 is, structurally, two friendship blades (F_1 at each hub) joined by a diamond whose twins repair parity and give a perfect matching with connected remainder.
   - Once one knows the friendship gap is 1, the counterexample is a small design step. The source's text, however, hides this: it claims a gap of n.
2. **Weak source standing.** The conjecture comes from an unrefereed arXiv-only preprint with zero recorded citations and no journal version found. Its supporting evidence contains two errors (F_n, and Theorem 4.12 at K_{2,2}). Refuting a conjecture with this little support and visibility has low external impact.
3. **Search fact, not argument.** Uniqueness at n = 8 and the absence of smaller examples are exhaustive-search facts. Per the 347138 ruling, such facts do not by themselves add mathematical substance.

**Precedent comparison.** 355140 (Staller) was accepted: a 7-vertex graph attaining equality in a known bound and falsifying a proposed improvement from a published (DAM) conjecture, with a short exact argument. 355217 has the same shape: equality in Theorem 4.1's bound plus a short exact lower-bound argument. The differences are the weaker venue and the near-tightness noted above.

**Recommendation.** It passes the bridge and routine screen, so E is QUALIFIED_PASS and the overall recommendation is **PROCEED**. If root judges that an uncited arXiv-only conjecture with erroneous supporting evidence falls below the significance bar, HOLD is the defensible alternative. I do not think EXCLUDE as a "routine consequence or source-ingredient bridge" is supported by the source's text.

Not claimed: a reversal γ̃c(G) > γ̃c(M(G)) (none exists for n ≤ 8), anything about 7.6, or worldwide priority.

## Files in this lane

- `scripts/`:
  - `mocd.py`: core definitions and searches.
  - `check_witness.py`: G8, M(G8) and source-family values.
  - `gen.py`: isomorphism-filtered enumeration.
  - `search.py`: exhaustive Conjecture 7.1 test.
  - `crosscheck.py`: cross-validation, lemma and family.
  - `source_thms.py`: checks of the source theorems.
  - `conj76_probe.py`: diagnostic for 7.6.
  - `run.sh`: capped runner. `fetch.sh`: single-shot fetch with receipt.
- `data/all{1..8}.txt`: class representatives as upper-triangle bit codes.
- `logs/`: full stdout and stderr, GNU time output and a JSON receipt for every run.
- `downloads/`: all fetched pages and API responses, plus `receipts.jsonl`.
- `input-hashes-before.txt` and `input-hashes-after.txt`: the read-only input binding. `own-artifact-hashes.txt`: hashes of my scripts and data.
- `review.json`: machine-readable verdicts.
