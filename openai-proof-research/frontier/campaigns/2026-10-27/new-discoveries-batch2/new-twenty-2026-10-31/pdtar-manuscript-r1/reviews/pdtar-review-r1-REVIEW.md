# Independent adversarial review: MathDB 353203 (PD-TAR uniqueness of K_{s,t})

Lane pdtar-review-r1, 2026-11-03 UTC. Reviewer: Claude Opus 5.5, high effort, with no child agents. This review does not accept the result; root decides.

**Target.** The ordinary proof in `pdtar-proof-r1/PROOF.md` (sha256 `32e3d044…f5b6`), together with SUMMARY.md, results.json and LEAN-PLAN.md.

## Verdicts

| Gate | Verdict | One-line reason |
|---|---|---|
| A. Statement fidelity | **PASS** | The claimed theorem is exactly the source's iff for all positive s and t, with the source's PD rounds, TAR graph and uniqueness definition. s = 0 is correctly out of scope. Only editorial fixes are needed. |
| B. Reduction | **PASS** | Theorem t:main applies: PD is an original, hence robust, parameter, and both graphs have no isolated vertices. The conclusion gives equal order and a bijection with exactly the same PD sets. Different-order or disconnected H, and the X(K₁) = 0 branch, cause no gap. |
| C. Core proof | **PASS** | No error was found in Lemmas 0–7. Every use of s ≥ 3, t ≥ 3, t ≥ 4 and (s,t) ≠ (3,3) is justified. My own exhaustive checker confirms every lemma, with zero failures, over all graphs at (3,3), (3,4) and (4,3), and over **all 2^28 graphs at (4,4) and (3,5)**. |
| D. Small cases | **PASS** | The source results cover exactly the complement of the Core range. An independent computation reproduces every small-case verdict for graphs H on up to 6 vertices. |
| E. Prior art and significance | **QUALIFIED_PASS** | A bounded search (arXiv, OpenAlex, author listings, web) found no resolution. The text of the La Matematica (2026) version could not be read through any permitted route. My significance recommendation is modest but genuine, and the proof is not a routine bridge. |

No blocking defect was found. The required fixes (§8) are editorial or concern the Lean statement.

## 1. Input binding

- **Before review.** 308 input files were hashed into `receipts/inputs-before.sha256` (file sha256 `273c85db…4d24`). They are:
  - all of pdtar-proof-r1's PROOF/SUMMARY/results/LEAN-PLAN/TASK/manifest, `scripts/`, `logs/`, `sources/`, `r119-copy/` and `lean-draft/`;
  - expanded-corpus-r119's `results.json`, `outputs/notes.md` and `logs/pdsat-*.log`;
  - the MathDB chunk.
- **After review.** The same files were hashed again into `receipts/inputs-after.sha256`. The two files are **byte-identical** (same sha256 `273c85db…4d24`).
- **MathDB raw line.** Chunk-0008, one-based line 2515, has sha256 `fb3b4a73e92d8196e75e36cb9ee60ad6ad119a70c59be6cb44744734c24f3935`, re-verified. Its statement is: "PD^TAR(K_{s,t}) is unique if and only if s ≠ 2 and t ≠ 2."
- **Key file hashes:**
  - PROOF.md `32e3d044b6f068bfb9f637ab1be219d9bba06807b5cae6bb5809ee6e5785f5b6`
  - source TeX `2d66e9c4961a5b30a51dd041812c44bc56efe7d419bea3724b31530f7f937202`
  - survey TeX `610fb8c011fbecc899d638927e687a73df547fc891846f69f13ec6b4c0b45508`

## 2. Gate A: statement fidelity (PASS)

I checked PROOF.md §0 against the source TeX (`2201.01798-PD-recon.tex`):

- **Power domination.** Source lines 205–214 define P⁰[S] = S, P¹[S] = N[S], and P^i[S] = P^{i−1}[S] ∪ {u : N(v) \ P^{i−1}[S] = {u} for some v ∈ P^{i−1}[S]}, applied in simultaneous rounds. PROOF.md lines 15–19 match.
  - The source defines P^i only for non-empty S. PROOF.md allows S = ∅, but ∅ is never PD on a non-empty vertex set, so nothing changes.
  - Graphs have non-empty vertex sets (source line 177).
- **TAR graph.** Source lines 247–248 define PD^TAR_k on PD sets of size at most k with adjacency |S₁ ⊖ S₂| = 1, and PD^TAR = PD^TAR_n (lines 424–426). PROOF.md line 21 matches.
- **Unique.** Source line 568 reads: "For a graph G with no isolated vertices, we say PD^TAR(G) is unique if for any graph H with no isolated vertices, PD^TAR(G) ≅ PD^TAR(H) implies H ≅ G." PROOF.md line 23 quotes this verbatim.
- **Conjecture.** Source line 738, `\begin{conj}` directly after `p:K33`, states it with no further qualifiers. The MathDB statement is identical.
- **Range.** Uniqueness is only defined for graphs without isolated vertices. So K_{0,t}, the edgeless graph on t vertices, lies outside the definition, and K_{0,0} is not a graph in the source's sense.
  - The only coherent reading is s, t ≥ 1. PROOF.md line 25 and the Lean endpoint (`1 ≤ s`, `1 ≤ t`) adopt this.
  - Reading the conjecture literally at s = 0, t ≠ 2 would assert uniqueness of a graph for which uniqueness is undefined, so excluding s = 0 is correct and not a weakening.
- **Coverage.** The claimed theorem (§7, line 194) is the full iff for all positive s and t. The case split (lines 196–203) partitions all pairs with s ≤ t, and symmetry covers s > t. See §5 for the case-by-case check.

**Non-blocking issues.**

- (A1) Line 36 attributes "|V(G)| = Δ(PD^TAR(G))" to `c:pd-iso-props`. That fact is Corollary `pd-deg-dist`(1) (source lines 453–456; survey `x-deg`). `c:pd-iso-props` (source lines 443–449) gives |V(G)| = |V(H)|. Line 200 has the same citation issue, but its conclusion is correct either way.
- (A2) The journal numbering (3.16, 3.24, 3.25) at lines 10 and 201–202 comes only from search-engine excerpts. Keep the arXiv labels and mark the journal numbers as unverified.

## 3. Gate B: the reduction (PASS)

I read the survey (`2406.05509-CFH24TARarxiv.tex`) in full for the relevant parts:

- Definitions `def:original+assumed` (lines 435–452), `d:superX` (499–508) and `Robust-parameters-2` (520–530).
- Observation `r:n-1-isol` (531–533); Corollary `x-deg` (656–659).
- Theorem `t:main` (764–766) and its proof chain:
  - `x-deg` (656–659), `c:u-iso-props` (742–752);
  - `interval` (773–783), `lem:ord_pres` (785–791), `t:irrel-isom` (799–812);
  - `isomorph-isometry-u` (820–848), `isomorph-same-zfs` (855–887) and Remark `r:isomorph-same-zfs` (889–892).
- Line 1360: "power domination is an original X-set parameter, so Theorem t:main applies."

**Hypotheses.** I verified PD's original axioms directly:

- Superset: the closure is monotone.
- (n−1)-set: with no isolated vertices, N[V∖{v}] = V.
- Component consistency: observation never crosses components, and an empty trace in a component cannot observe it.
- PD(K₁) = 1.
- ∅ is not PD.

Hence PD is robust. The source also asserts that PD satisfies Definition 2.1 (line 429).

- G = K_{s,t} with s, t ≥ 1 has no isolated vertices.
- H has none by the uniqueness definition.
- So the branch "G and G′ have no isolated vertices" applies. The alternative X(K₁) = 0 is false for PD and is not needed.

**Conclusion.** "There is a relabeling of the vertices of G′ such that G and G′ have exactly the same X-sets." This is a bijection, so the orders are equal. Equal order is also stated separately in `c:u-iso-props`(1) and is used inside the proof of `isomorph-isometry-u`.

**Possible gaps, each checked.**

- **H of a different order.** Impossible: Δ(TAR) = |V| for graphs without isolated vertices.
- **Disconnected H.** No connectedness hypothesis appears anywhere in the chain. The Core Theorem then shows H′ = K_{A,B}, which is connected.
- **φ(V(G)) ≠ V(G′).** This is handled by ν_{R′} and irrelevant sets in `isomorph-isometry-u`.

PROOF.md §1 (lines 39–46) uses exactly this conclusion: H′ = ψ(H) on V with PD(H′) = PD(K_{A,B}). The converse direction (H′ = K ⇒ H ≅ K_{s,t}) is immediate.

**Caveat (not a gap).**

- The survey says the proof of `isomorph-isometry-u` follows Theorem 2.8 of Bong et al. I read the survey's own self-contained proof, which is sufficient. I did not read the Graphs Combin. version: Springer is denied.
- OpenAlex confirms Graphs and Combinatorics 39(4), 2023, doi 10.1007/s00373-023-02677-1. I did not verify the article number "86".

## 4. Gate C: the Core proof, line by line (PASS)

### 4.1 Hand check

**Lemma 0** (lines 52–63).

- (⇐) The rounds are monotone and deterministic, so P^i stabilises at some O ⊇ N[S]. Stability means no v ∈ O has exactly one neighbour outside O. Then F = V∖O is a non-empty fort avoiding N[S].
- (⇒) Take the least i ≥ 2 with P^i ∩ F ≠ ∅; i ≥ 2 because P⁰ ⊆ P¹ = N[S] is disjoint from F. Then the observer v ∉ F has a second F-neighbour u′, which is unobserved, a contradiction.
- The argument handles the simultaneous-round definition correctly, because the exclusivity condition is evaluated against P^{i−1} and P^{i−1} ∩ F = ∅.
- This duality is standard: forts block zero forcing (survey line 411), and PD is zero forcing from N[S]. The lane proves it directly, so no citation is needed.

**F1–F3** (lines 67–71) are correct. F3 uses that forts are non-empty.

**K1–K3** (lines 79–82) are correct.

- K2 needs s ≥ 2 so that A∖{x} ≠ ∅ dominates B.
- K3: {x,y} is a fort of K. N_K[A∖{x,y}] = (A∖{x,y}) ∪ B for s ≥ 3, and = ∅ for s = 2. Either way it avoids {x,y}.

**Lemma 1** (lines 86–93) is correct.

- (a) uses only K1 and K2 for the side that is not fully covered.
- (b) uses only K1 and s, t ≥ 2: {v} is a fort when v is isolated, and N[{v}] = {v} cannot meet every pair {a,b}.

**Lemma 2** (lines 97–102) is correct. It needs s ≥ 3 so that A∖{x,y} ≠ ∅ forces A ⊄ N[Ψ].

**Lemma 3** (lines 108–115) is correct.

- In the p ∉ Ψ branch, both neighbours would lie in Ψ ∩ A ⊆ {y}.
- In the p ∈ Ψ branch, N(p) ⊆ {y}.
- Two choices of y (s ≥ 3) give N(p) = ∅, which contradicts 1(b).

**Lemma 4** (lines 117–119) is correct. deg a = 1 rules out a ∉ Φ by F2, and a ∈ Φ puts c ∈ N[Φ] = A ∪ {c′,c″}. It needs t ≥ 3.

**Lemma 5** (lines 121–145) is correct.

- Step (i): the (α)/(β) dichotomy is exhaustive because a ∈ N[Ψ_{ay}]. In (β) the two Ψ-neighbours must be c and y, because β(a) = {c} and Ψ ⊆ B ∪ {a,y}.
- "Some y ≁ a" gives N_A(a) = ∅, which contradicts Lemma 4. So N_A(a) = A∖{a}.
- |N_A(a)| ≥ 2 (s ≥ 3) excludes (α). F1 applied to c, y ∈ Ψ_{ay} gives α(c) ⊆ {a,y} and N_A(y) ⊆ {a}.
- Step (ii) is the genuine mirror, triggered by |α(c)| = 1. It uses t ≥ 3 and s ≥ 3 through mirror Lemmas 2 and 4.
- Step (iii): N[a] = A ∪ {c} forces Ψ_{yy′} ⊆ B∖{c}. Every b ∈ B∖{c} has N_B(b) = {c}, so b ∈ Ψ. Then N[Ψ] ∩ A = ∪ α(b) does not depend on the pair, which forces s = 3. The mirror forces t = 3.

**Corollary 5′** (line 147) is correct.

**Lemma 6** (lines 153–176) is correct.

- The WLOG t ≥ 4 is legitimate. If t = 3 then s ≥ 4, and every ingredient (Lemma 2, Lemma 1(b), Corollary 5′, F1–F3) is side-symmetric because the PD family of K_{A,B} is symmetric. My exhaustive (4,3) run tests exactly the swapped case.
- First branch: Φ = {b,b′}, and a ∈ N[Φ]∖Φ forces a ~ b, b′.
- Second branch: β(p) = {b,b′} gives p ∉ Φ_{cc′} and |N_A(p)| ≥ 2. The same holds for p′ with β(p′) = {c,c′}.
- Then p, p′ ∉ Ψ_{pp′}, so Ψ ⊆ B, and b ∈ Ψ. F1 gives α(b) ⊆ {p}, which contradicts Corollary 5′. The only place t ≥ 4 is used is to choose c, c′ ∉ {b,b′}.
- Observation (cosmetic): the second-branch contradiction never uses the non-adjacent vertex a. The proof in fact shows Φ_{bb′} ∩ A = ∅ for every pair, after which completeness follows from the first branch. This is not an error.

**Lemma 7** (lines 180–188) is correct. Completeness gives N[z] ⊇ B, so Ψ_{xy} ⊆ {x,y}. F3 and 1(b) give Ψ = {x,y}, and then z ≁ x, y. It needs s, t ≥ 3.

**Hypotheses actually used, and where.** No lemma is used under weaker hypotheses than its proof requires.

| Lemma | PD facts used | Size conditions used |
|---|---|---|
| 1(a) | K1, K2 (both sides) | s, t ≥ 2 |
| 1(b) | K1 | s, t ≥ 2 |
| 2 A-side | K1, K2_A, K3_A | s ≥ 3 |
| 2 B-side | K1, K2_B, K3_B | t ≥ 3 |
| 3 A-side | as Lemma 2 A-side | s ≥ 3 |
| 4 A-side | as Lemma 2 B-side | t ≥ 3 |
| 5 | both sides | s, t ≥ 3 |
| 5′ | both sides | (s,t) ≠ (3,3) |
| 6 | both sides | t ≥ 4 or the swap; uses 5′ |
| 7 | both sides | s, t ≥ 3, plus A–B complete |

**Strengthening.** The whole Core proof needs only the PD facts K1–K3 in H, not the full PD family. My computation confirms that this weaker hypothesis already forces H = K at (3,4), (4,3), (4,4) and (3,5); see §4.2.

### 4.2 Own computation (no lane script imported or read)

- `scripts/rv_check.py` was written from scratch.
  - It computes PD with the source's simultaneous rounds and forts by definition.
  - Over all graphs it is **bit-sliced**: one bit per graph in a Python big integer.
  - Each surviving graph is then tested per lemma, under the hypotheses its proof uses.
- `scripts/run.sh` applies the caps: taskset 0,1; prlimit CPU 120 s and AS 6 GiB; timeout 140 s; MALLOC_ARENA_MAX=2; python3 -I.
- Results are in `logs/*.log`, with receipts in `logs/*.receipt.json` and the aggregate in `logs/agg-exhaustive.json`.

| (s,t) | graphs | K1 | HA | HB | H2 = K1–K3 both sides | full PD family = K's | failures |
|---|---|---|---|---|---|---|---|
| (3,3) | 32,768 (all) | 18,902 | 38 | 38 | 10 | 10 (K and 9 relabelled K_{3,3}) | 0 |
| (3,4) | 2,097,152 (all) | 1,089,408 | 4,360 | 8 | **1 (K)** | 1 (K) | 0 |
| (4,3) | 2,097,152 (all) | 1,089,408 | 8 | 4,360 | **1 (K)** | 1 (K) | 0 |
| (4,4) | 268,435,456 (all) | 115,480,182 | 88 | 88 | **1 (K)** | 1 (K) | 0 |
| (3,5) | 268,435,456 (all) | 120,519,894 | 990,634 | 8 | **1 (K)** | 1 (K) | 0 |

The brief asked only for random or structured tests at (4,4) and (3,5). The bit-sliced method made a fully exhaustive sweep affordable, so I ran that instead.

**Per-lemma tests.** All passed.

- L1(a), every fort of every graph satisfying K1 ∧ K2_A ∧ K2_B: 15,928 / 974,332 / 974,332 graphs at (3,3), (3,4) and (4,3). Skipped at n = 8 for CPU reasons.
- L1(b), no isolated vertex under K1: bit-sliced, 0 violations at all five sizes.
- L2, L3, L4 (each side, under its own one-sided hypothesis): for example, 990,634 graphs at (3,5) and 4,360 at (3,4).
- L5, Corollary 5′, L6, the Lemma 6 intermediate claim "every fort with N[Φ] = A ∪ {b,b′} misses A", L7 and the Core Theorem, all under H2.
- At (3,3), the Lemma 5 structure (steps i–iii) holds in all 9 relabelled copies that have a cross-degree-1 vertex. This shows that (s,t) ≠ (3,3) is necessary for Corollary 5′ and Lemma 6.

**Lemma 0.**

- Every (graph, S) pair on 5 vertices (32,768 pairs) and on 6 vertices (2,097,152 pairs) checked, with 0 mismatches.
- 25,235,456 pairs on 7 vertices (graph indices 1,900,000 to 2,097,151): 0 mismatches.

**Agreement with the lane's figures.** The proof lane's reported counts match mine: L2 4,360 / 8 / 38; 9 instances of Lemma 5; 10 relabelled copies of K_{3,3}; and the full-family results.

**Run note.** One run (`exh-3-5-f7-c64-128`) was killed at the 120 s CPU cap, with exit code 137. Its log is retained. That range was re-run in two parts (`c64-96` and `c96-128`), and only those two parts enter the aggregate.

## 5. Gate D: the small cases (PASS)

I read the source proofs:

- `upperPDn-3` (lines 608–615, using `c:pdequal1` at line 603 and `p:upperpdconnected` at lines 570–590);
- `k2tminimalsets` (629–635) and `mPDS:n-3:K2t` (699–705; the K_{2,2} case is handled in the sentence at line 699);
- `p:K33` (726–735).

| Pair (s ≤ t) | Coverage | Status |
|---|---|---|
| (1,1) = K₂ | Order 2 from Δ = n (`pd-deg-dist`) or `c:pd-iso-props`, so H = K₂ | unique |
| (1,2) = P₃ | P₃ and K₃ both have every non-empty set PD, and K₃ has no isolated vertices | not unique |
| (1,t), t ≥ 3 | `upperPDn-3` (r ≥ 3) | unique |
| (2,t), t ≥ 2 | `mPDS:n-3:K2t` (t ≥ 2); K_{2,t}(e) ≇ K_{2,t} by edge count | not unique |
| (3,3) | `p:K33` | unique |
| s, t ≥ 3, (s,t) ≠ (3,3) | Core Theorem + Theorem R | unique |

With s ≤ t, the cases s = 1, s = 2 and s ≥ 3 are exhaustive. (2,1) is covered as (1,2) by symmetry, and uniqueness is invariant under K_{s,t} ≅ K_{t,s}. So the pieces cover exactly the complement of the Core range, with no overlap problems.

**Independent computation** (`scripts/rv_small.py`, `logs/small-cases.log`). The scan covers every labelled graph H with no isolated vertices on 2 to 6 vertices: 1 + 4 + 41 + 768 + 27,449 graphs.

| Target | H with a relabelled PD family | of which ≇ G | verdict |
|---|---|---|---|
| K₂ | 1 | 0 | unique |
| K_{1,2} | 4 | 1 (K₃) | not unique |
| K_{1,3} | 4 | 0 | unique |
| K_{2,2} | 22 | 19 (P₄, K₄−e, K₄) | not unique |
| K_{1,4} | 5 | 0 | unique |
| K_{2,3} | 20 | 10 (K_{2,3}(e)) | not unique |
| K_{1,5} | 6 | 0 | unique |
| K_{2,4} | 30 | 15 (K_{2,4}(e)) | not unique |
| K_{3,3} | 10 | 0 | unique |

- For every target, **no** H with a different PD family even shares the colour-refinement invariant of the TAR graph. So these verdicts do not depend on Theorem R for H on up to 6 vertices. Larger orders are excluded by Δ(TAR) = |V|.
- The source witnesses check out: K_{2,t} and K_{2,t}(e) have the same PD family for t = 2, 3, 4, and so do K_{1,2} and K₃.

**Caveat.** The source's `upperPDn-3` proof has a harmless typo, pdbar(PD^TAR(K_{1,n−1})). The source's proofs of `p:upperpdconnected` and `p:K33` were read and found adequate. Their conclusions at n ≤ 6 are confirmed by the computation above.

## 6. Gate E: prior art and significance (QUALIFIED_PASS)

Fresh fetches made in this lane (receipts in `sources/web/receipts.txt`; downloads in a new directory `sources/web/`, parsed with python3 -I):

- **arXiv abs pages.**
  - 2201.01798: still v1 only (5 Jan 2022).
  - 2406.05509: v2, 28 Sep 2025.
  - 2205.09668: v1.
- **Survey restatement.** The cached survey v2 still lists the conjecture as open (line 1367: "It is conjectured there that PD^TAR(K_{p,q}) is unique for q ≥ p ≥ 3").
- **Hogben's arXiv author listing**, found by ORCID: https://arxiv.org/a/0000-0003-1673-3789.html.
  - 2024+ items: 2403.03921, 2406.05509, 2501.03472, 2509.18486, 2601.11912, 2606.30950.
  - None concerns PD-TAR uniqueness, except the survey, which lists it as open.
- **arXiv 2509.18486** (Curtis, Flagg and Hogben, 23 Sep 2025, "Universal perspectives on irredundance for X-set parameters"), HTML read. It cites the PD reconfiguration paper as "to appear in La Matematica" and does not address K_{s,t} PD-TAR uniqueness.
- **OpenAlex.**
  - The arXiv record W4226105401 has 0 citing works.
  - The journal record W7123339276 (2026-01-13) has 1 citing work, the survey's journal version W7147580019 (2026-03-31).
  - Bong et al. W4281261871 has 1 citing work, its own journal version.
  - The survey has 0 citing works.
  - Keyword searches ("power domination" reconfiguration since 2023-06, 81 hits; "power dominating sets" "complete bipartite" unique, 10 hits) show no resolution. The only on-topic hits are the source, the survey and the PD toolbox (JSAG 2026, about computing minimum PD sets, unrelated).
- **Web searches** (four queries, logged in `sources/web/websearch-log.md`) found no resolution.

**Journal version text.** Unread through every route available to me:

- Springer and the Swarthmore viewcontent PDF are denied and were not attempted.
- `dr.lib.iastate.edu` timed out (curl exit 28; not retried). OpenAlex in any case lists that record only as the 2022 submitted version.
- `aimath.org/~hogben/` returned 404.
- `works.bepress.com/leslie-hogben/88` now redirects to a "SelectedWorks retirement" page.

The survey's journal version (published 2026-03-31, after the source's 2026-01-13 publication) and the survey's arXiv v2 both treat the conjecture as open. This is strong indirect evidence that the journal version still states it as a conjecture. **Root should note that this is not a direct reading.**

**Is the Core proof a routine bridge?** No.

- **Domination analogue.** The survey's K_{p,q} domination proposition (lines 1214–1228) uses that domination is witnessed by closed neighbourhoods. "{a_i, b_k} dominates" directly gives A ⊆ N[b_ℓ], and minimality of A∖{a_i} kills edges. Power domination has no such local witness: a set like {a,b} or A∖{x} can be PD through propagation.
- **The source's (3,3) proof** uses that every 2-set is PD, together with degree counting on 6 vertices. It does not extend.
- **K_{1,t} and K_{2,t}** rely on the upper PD number, n−2 and n−3.
- **What the lane adds.** It converts the PD family into fort-blocker data (Lemmas 1–2). It then needs a genuinely new two-sided cross-degree argument (Lemmas 3–6) to isolate (3,3) and force completeness.
- **Assessment.** Lemma 0 is standard. The remaining argument is short and elementary, about two pages, but it is not a rewording of any stated lemma. The r119 lane's earlier attempt stalled exactly at the "missing lemma" that Lemma 6 supplies.

**Significance recommendation: MODEST BUT GENUINE.**

- The result resolves, in full, an explicitly stated conjecture from a 2022 paper (published 2026). The authors supported it by Sage computations and restated it as open in a 2024/2025 survey.
- The proof is elementary and short, but it needs a new idea: the fort-blocker and two-sided cross-degree argument.
- I do not consider it a routine corollary, a parameter instance or a wording correction.
- Root should weigh the brevity against the campaign's "mathematically significant" standard. In my judgement it clears the bar for a resolved, published, named conjecture.

## 7. Lean-statement fidelity notes (advisory; Lean is outside this review's gates)

Checked against `lean-draft/PDTAR/Defs.lean` (uncompiled; not run, per lane rules).

- `obs`/`IsPD` follow the source's rounds literally; `tar` and `TARUnique` follow source §3.3.
- (L1) `TARUnique G` omits the source's precondition that G has no isolated vertices. This is harmless for K_{s,t} with s, t ≥ 1, but the fidelity reviewer should note it.
- (L2) For an empty vertex type W, H has no isolated vertices vacuously, and `tar H` is a single vertex because ∅ = univ is PD. The source excludes empty graphs. This is harmless here, because PD^TAR(K_{s,t}) has at least 3 vertices, but the Lean proof must handle the case explicitly.
- (L3) Theorem R must be formalized in full for PD (LEAN-PLAN §3). It cannot be cited, because the user requires no residual bridges. K_{1,t} (via `p:upperpdconnected`) and K_{3,3} also need real Lean proofs; numerical checks cannot substitute.

## 8. Required fixes (none blocking for the ordinary proof)

1. **PROOF.md line 36 and line 200.** Cite Corollary `pd-deg-dist`(1) (survey `x-deg`) for Δ(PD^TAR(G)) = |V(G)|. Cite `c:pd-iso-props`(1) only for |V(G)| = |V(H)|.
2. **PROOF.md line 31.** Add doi 10.1007/s00373-023-02677-1 (Graphs Combin. 39(4), 2023). Either verify the article number "86" or drop it.
3. **PROOF.md line 25.** Justify the range explicitly. Source graphs have non-empty vertex sets (line 177), and "unique" is defined only for graphs without isolated vertices (line 568). So s, t ≥ 1 is the only coherent reading, and K_{0,t} is excluded.
4. **PROOF.md lines 10 and 201–202, and SUMMARY lines 38–40.** Mark the journal theorem numbers and the claim "still Conjecture 3.25 in La Matematica" as unverified search-engine evidence. Add this review's failed routes (Iowa State timeout, AIM 404, SelectedWorks retired) and the indirect evidence (survey arXiv v2 and the survey's journal version, 2026-03-31).
5. **PROOF.md §8 (line 214 and following).** State that Lemma 0 (fort duality) is standard, and that the new ingredients are Lemmas 1–6.
6. **Optional strengthening.** Note that the Core proof uses only facts K1–K3, as confirmed computationally above.
7. **Optional cosmetic edit in Lemma 6.** Note that the second branch is contradictory independently of a.
8. **Lean.** Address L1–L3 in §7 in the formal statement review.

## 9. Process

- **Every computation:** `scripts/run.sh`, one at a time, with 2 CPUs, CPU 120 s, wall 140 s, AS 6 GiB, MALLOC_ARENA_MAX=2, python3 -I, and lane-local TMPDIR and caches. Full logs and receipts are in `logs/`.
- **Peak RSS** was 81.5 MB, in `exh-3-4`.
- **Not run:** Lean, lake, leanchecker and SAT solvers.
- **No git, no ledger edits, no uploads, no messages, no browser tabs.** No background jobs remain.
- **Denied routes** (Crossref, Semantic Scholar, Springer, Swarthmore, ScienceDirect, the arXiv search API) were not used. No route was retried after a failure.
- **Files:**
  - `scripts/rv_check.py`, `scripts/rv_small.py`, `scripts/agg.py`, `scripts/run.sh`, `scripts/fetch.sh`;
  - `logs/`;
  - `receipts/inputs-{before,after}.sha256`;
  - `sources/web/`;
  - `manifest-sha256.txt`.
