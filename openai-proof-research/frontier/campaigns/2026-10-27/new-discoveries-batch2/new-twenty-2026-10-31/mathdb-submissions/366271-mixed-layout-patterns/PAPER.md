# Forbidden patterns in mixed linear layouts

MathDB 366271. Both conjuncts of the exact source statement are proved in Lean 4 with Mathlib. The written proof is reproduced and elaborated from the supplied proof lane; all source-scope and finite-certificate bridges are proved here.

## Source and literal statement

Deborah Haun, Laura Merker and Sergey Pupyrev, *Forbidden Patterns in Mixed Linear Layouts*, arXiv:2412.12786v2 (26 October 2026), Conjecture 31, p.34, Figure19. In v1 it is Conjecture27 and Figure14. The STACS2025 proceedings paper, DOI10.4230/LIPIcs.STACS.2025.45, p.45:17, explicitly leaves this characterization conjectural and points to v1 Conjecture27.

The source prints:

> An ordered matching with a fixed (non-separated) layout admits
> (i) a 1-stack 1-queue layout if and only if it avoids 12 patterns depicted in Figure 19a, and
> (ii) a mixed layout on 1 page if and only if it avoids 8 patterns depicted in Figure 19b.

The formal theorem is precisely this conjunction for **every finite ordered matching**, without any bound on its number of edges. The vertex order is fixed throughout; there is no reordering quantifier. Isolated vertices have no effect. “Contains a pattern” means an order-preserving copy of its edges, not necessarily consecutive vertices.

## Endpoint transcription of the source figures

Write `ab` for the edge with endpoints a<b, and list edges in increasing order of their left endpoints. In Figure19a, reading row by row and left to right:

| Figure position | Edges |
|---|---|
| row1 left | 05,14,27,36 |
| row1 right | 07,14,29,36,58 |
| row2 left | 06,17,24,35 |
| row2 right | (0,6),(1,3),(2,4),(5,11),(7,9),(8,10) |
| row3 left | 06,13,29,47,58 |
| row3 right | 07,14,25,39,68 |
| row4 left | 07,14,29,35,68 |
| row4 right | 07,13,29,46,58 |
| row5 left | 05,13,29,47,68 |
| row5 right | 07,13,25,49,68 |
| row6 left | 07,13,24,59,68 |
| row6 right | 04,13,29,57,68 |

In Figure19b, again row by row:

`04,13,25`; `02,15,34`; `05,13,24`; `02,13,47,56`;
`03,15,24`; `04,12,35`; `04,15,23`; `03,12,46,57`.

These are not inferred from the conjectured counts. The proof lane's `scripts/extract_figure.py` reads the actual Bézier-path endpoints of the source PDF after `pdftocairo -svg`, normalizes their integer coordinates, and compares them to the independently enumerated obstruction lists. Both set equalities passed. The rendered page was visually inspected too. The extraction script and evidence are in the sibling proof lane `../t1-pool039-proof-sol61-20261120-r1/`: `scripts/extract_figure.py`, `source-figure-patterns.json`, `source-figure.log`, and `tmp/pdfs/figure19.png`. The final-check lane independently compared the literal Lean tables with all 20 endpoint lists extracted from a fresh download of v2.

## Definitions

Regard each edge e as an interval [l(e),r(e)] with l(e)<r(e). Every endpoint of every edge of a matching is distinct. For distinct edges e,f let:

- C(e,f) mean that their endpoints alternate (they cross).
- N(e,f) mean strict containment of either interval in the other (they nest).
- D(e,f) mean disjoint intervals.

Exactly one of C,N,D holds. Color S means stack and Q means queue. A coloring is valid exactly when a C-pair is never colored S,S and an N-pair is never colored Q,Q. Thus the elementary implications are

    eS -> fQ  when C(e,f),
    eQ -> fS  when N(e,f).

Each implication has its reverse-complement implication, since C,N are symmetric.

Define the following **initially forced literals** (called seeds below):

    eS is a seed if N(e,u), N(e,v), C(u,v) for some u,v;
    eQ is a seed if C(e,u), C(e,v), N(u,v) for some u,v.

Any valid coloring satisfies every seed: coloring the center oppositely would force both other edges to have the same forbidden color. A seed is witnessed by three edges, including its center.

## Lemma 1: no seeds implies colorability

A matching containing no forcing triple admits a valid S,Q coloring.

**Proof.** Induct on the number of edges, including zero. Let e have the smallest right endpoint. Every interval intersecting e extends to the right of r(e), so any two such intervals intersect each other. Suppose e has a crossing neighbor u and a nesting neighbor v. The latter must contain e. If C(u,v), then u crosses the nested pair e,v, making uQ a seed. If N(u,v), then v nests both e and u, which cross, making vS a seed. Both are impossible. Therefore e's neighbors have only one of the two relation types. Delete e and use induction. If it has a crossing neighbor, color e Q; it then has no nesting neighbors. Otherwise color e S; it then has no crossing neighbors. Either choice is compatible with every other assigned color. This proves the induction. ∎

## Lemma 2: propagation detects every failure

Start with all seeds and close under the elementary implications. If this closure is consistent (no edge has both literals in it), the matching is colorable.

**Proof.** Assign every forced edge its unique forced color and leave the other edges unassigned. No clause with an assigned endpoint can be violated: a problematic color at its other endpoint would have been prohibited by propagation. More explicitly, an assigned S on a crossing pair forces the other edge Q, and an assigned Q on a nesting pair forces the other edge S. Therefore assigned/unassigned pairs impose no remaining restrictions, and assigned/assigned pairs are valid by consistency. The induced matching of unassigned edges has no forcing triple, since such a triple would make its center a seed, hence assigned. Apply Lemma1 to color it. ∎

Conversely every seed and implication is valid, so a contradictory closure cannot be colored. This proof does not assume the general 2-SAT satisfiability theorem.

## Lemma 3: shortening a C-N-C path

If C(a,b), N(b,c), C(c,d), then at least one of the following is a seed:

    aQ, bS, cS, dQ.

**Proof.** If C(a,c), the witnesses b,c force aQ. If N(a,c), the witnesses a,b force cS. Otherwise a,c are disjoint. Since b crosses a and nests c, b must contain c; c cannot contain b because it is disjoint from a. Since d crosses c, d intersects b. If N(b,d), the crossing pair c,d forces bS. If C(b,d), the nested pair b,c forces dQ. These cover the possibilities. The pairs a,c and b,d are distinct: equality in either would require the same pair to cross and nest. The case a=d causes no difficulty. ∎

## Lemma 4: a Q seed inside an interval

Suppose aQ is a seed and b properly contains a. Then either bS is a seed, or there are two nested Q seeds (giving a one-implication contradiction).

**Proof.** Choose witnesses u,v with C(a,u), C(a,v), N(u,v). Both u,v intersect b because both intersect a inside b. If either u or v nests b, that witness cannot contain b: it would then contain a, contradicting its crossing with a. Thus b contains that witness as well as a, and those two edges cross, so bS is a seed. Otherwise both witnesses cross b. Then u crosses the nested pair a,b, making uQ a seed, and likewise vQ is a seed. These two Q seeds nest. ∎

## Lemma 5: every failure has a six-edge certificate

If the matching is not colorable, it contains an uncolorable submatching with at most six edges.

**Proof.** By Lemma2 propagation is contradictory. Consequently there is an implication path from a seed p to the complement of a seed q. To see this carefully, if seeds p and q reach opposite literals x and not-x, reverse and complement the path from q to not-x; this is a path from x to not-q. Concatenate it with the path from p to x.

Choose such a path of smallest length L over **all** seed choices. If it contains a three-link subpath starting S, its relation types are C,N,C. Lemma3 supplies either a seed opposite one of the first two literals, or a seed equal to one of the last two. In the former case the path prefix ends at the complement of a seed; in the latter case its suffix starts at a seed. Each is a strictly shorter path of the required kind. Thus a shortest path has no such subpath. All paths alternate S,Q, so L<=3, and if L=3 its relation types are N,C,N, starting Q.

We now rule out L=2 and L=3.

For L=2, reverse and complement if necessary so that the path is

    aS -C-> bQ -N-> cS,

where aS and cQ are seeds. If C(a,c), the path triangle makes aQ a seed, giving L=0. If N(a,c), it makes cS a seed, also giving L=0. If D(a,c), b contains c, as in Lemma3. Apply Lemma4 to the Q seed c inside b. It gives either bS, yielding the one-link contradiction aS->bQ, or a one-link contradiction between nested Q seeds. Either contradicts minimality of L=2.

For L=3, the path is

    aQ -N-> bS -C-> cQ -N-> dS,

where aQ and dQ are seeds. If N(a,c), then a nests the crossing pair b,c, making aS a seed and giving L=0. If C(a,c), then c crosses the nested pair a,b, making cQ a seed; cQ->dS gives L=1. Otherwise a,c are disjoint, and b contains a. Apply Lemma4 to a inside b. It gives a one-link contradiction, or bS as a seed. In the latter case the suffix bS->cQ->dS has length2 and has the required seed endpoints, again contradicting minimality.

Therefore L<=1. If L=0, an edge has opposite seeds; the union of their two three-edge witnesses has at most five edges and is uncolorable. If L=1, either two S seeds cross or two Q seeds nest. The union of their witnesses has at most six edges and is uncolorable. The witness set need not be induced in any larger graph; retaining exactly these matching edges with their inherited order is sufficient. ∎

Equivalently, the full matching is colorable if and only if its S seeds do not cross, its Q seeds do not nest, and no edge is a seed of both colors. The reverse direction is now proved, rather than inferred from small-instance tests.

## Equivalent explicit saturation proof (also formalized)

The path argument above has the following independently formalized form. Let A be the S-seed centers, B the Q-seed centers, and let C(X),N(X) denote all crossing/nesting neighbors of a set X. Assume there is no opposite seed at one edge, no crossing pair in A, and no nesting pair in B. Put

    Q* = B union C(A),
    S* = A union N(Q*).

First, Q* is nonnesting. For two members of B this is the hypothesis. For one member in B and another crossing an A center, a nesting gives the two-link contradiction excluded in Lemma5. For two members crossing A centers, use the C-N-C lemma: it gives either an opposite seed or a crossing pair in A. Also Q* is disjoint from A, by the same local hypotheses, hence disjoint from S*=A union N(Q*).

Every crossing neighbor of S* lies in Q*. This is immediate for A. If a member of S* nests a B center and crosses e, trichotomy between that B center and e either makes e a Q seed, contradicts opposite seeds, or shows that the intermediate interval contains the B seed. Lemma4 then makes that intermediate interval an S seed, so e lies in C(A). If the nesting neighbor lies in C(A), apply the C-N-C lemma once more; its first two outcomes contradict local consistency and its last two put e in C(A) or B. Nesting neighbors of Q* lie in S* by definition.

Thus Q*,S* are consistent and implication-closed. All remaining edges have no forcing triple and are colored by the extreme-edge induction in Lemma1. This proves the same global criterion without formalizing shortest paths. `src/Criterion.lean` checks this construction for arbitrary finite edge types and literal proper intervals with disjoint endpoints. `src/SmallCore.lean` extracts an actual submatching of cardinality<=6 from any failure; the size bound is a proved conclusion, never a cap in the colorability definition.

## Exact finite remainder for part (i)

Every deletion-minimal uncolorable matching has at most six edges by Lemma5. Relabel its endpoints increasingly as 0,...,2m-1. The following exhaustive enumeration is complete: pair endpoint0 with each other endpoint, and recursively enumerate all matchings on the remaining ordered endpoints. This visits each perfect matching exactly once, since the mate of the least remaining endpoint uniquely determines its branch.

Colorability is checked directly for every Boolean assignment in the independent implementation: represent all 2^m assignments by bits of one integer, and intersect the masks of the crossing and nesting clauses. A nonzero final integer means an actual valid coloring exists. A matching is deletion-minimal uncolorable exactly when this integer is zero and the corresponding integer for every single-edge deletion is nonzero. Deletion-minimality is sufficient for all proper submatchings by heredity.

The two independent implementations agree exactly:

| Edges | Matchings | Uncolorable | Deletion-minimal uncolorable |
|---:|---:|---:|---:|
|0|1|0|0|
|1|1|0|0|
|2|3|0|0|
|3|15|0|0|
|4|105|2|2|
|5|945|82|9|
|6|10395|2206|1|

The resulting twelve endpoint lists are exactly Figure19a, by the independent vector extraction above. Every listed matching is uncolorable, and every one-edge deletion has a valid coloring (explicit deletion color masks are in `layout-core-certificate.json`). Lemma5 and deletion-minimality now prove both directions of part(i) for all finite sizes.

The earlier lane already enumerated much larger matchings. That was evidence only. The **new ingredient is the uniform six-edge certificate theorem**, which makes the small enumeration a complete proof. The new enumeration is an independent exact certificate of this finite remainder, not a claimed search discovery.

## Part (ii)

An ordered matching fails to admit a mixed layout on one page exactly when it has both a crossing pair and a nesting pair: the page must be wholly a stack or wholly a queue. Their union uses at most four edges. Hence every deletion-minimal failure has at most four edges. The same complete pairing recursion, with the direct predicate “contains both kinds of pair”, yields six critical matchings on three edges and two on four edges. Their endpoint lists are exactly Figure19b, as checked by the vector extraction. This proves both directions of part(ii). This elementary companion part is not claimed as a separate result or as the substantive contribution.


## Literal source definitions and Lean interpretation

The source (v2, §1) states:

> An ordered graph is a graph given with a fixed linear vertex order, ≺. A linear layout of an ordered graph is a partition of its edges such that each part satisfies certain requirements with respect to the order.

> In a stack layout each part, also called a stack, is required to be crossing-free with respect to ≺, that is, two edges in the same stack may not have alternating endpoints. A queue layout is a “dual” concept which forbids two edges to nest in the same part, called a queue; that is, if u ≺ x ≺ y ≺ v, then edges uv and xy must be in different queues. The two concepts are generalized in mixed linear layouts, where each part (called a page then) may either be a stack or a queue.

> An ordered graph (G, ≺1) contains a pattern (H, ≺2) if H is a subgraph of G and ≺2 is a suborder of ≺1; otherwise, the graph avoids the pattern.

The matching and relation definitions used in Lean are the following (namespaces are omitted here; the appendix contains the production declarations):

```lean
structure Arc where
  lo : ℕ
  hi : ℕ

def Cross (a b : Arc) : Prop :=
  (a.lo < b.lo ∧ b.lo < a.hi ∧ a.hi < b.hi) ∨
  (b.lo < a.lo ∧ a.lo < b.hi ∧ b.hi < a.hi)

def Nest (a b : Arc) : Prop :=
  (a.lo < b.lo ∧ b.hi < a.hi) ∨ (b.lo < a.lo ∧ a.hi < b.hi)

def Apart (a b : Arc) : Prop :=
  a.lo ≠ b.lo ∧ a.lo ≠ b.hi ∧ a.hi ≠ b.lo ∧ a.hi ≠ b.hi

structure OrderedMatching (ι : Type) where
  arc : ι → Arc
  proper : ∀ i, (arc i).lo < (arc i).hi
  apart : ∀ i j, i ≠ j → Apart (arc i) (arc j)

def endpt (a : Arc) (s : Bool) : ℕ := if s then a.hi else a.lo

def OneStackOneQueue {ι : Type} (M : OrderedMatching ι) : Prop :=
  ∃ isQueue : ι → Bool, ∀ a b, a ≠ b →
    (Cross (M.arc a) (M.arc b) → isQueue a ∨ isQueue b) ∧
    (Nest (M.arc a) (M.arc b) → ¬isQueue a ∨ ¬isQueue b)

def OneMixedPage {ι : Type} (M : OrderedMatching ι) : Prop :=
  (∀ a b, ¬Cross (M.arc a) (M.arc b)) ∨
  (∀ a b, ¬Nest (M.arc a) (M.arc b))

def Contains {ι : Type} (M : OrderedMatching ι) (P : List Arc) : Prop :=
  ∃ f : Fin P.length → ι, Function.Injective f ∧ ∀ i j : Fin P.length, ∀ s t : Bool,
    (endpt P[i] s < endpt P[j] t ↔
      endpt (M.arc (f i)) s < endpt (M.arc (f j)) t)
```

These quotations are transcribed from the supplied local source text. The adjacent Lean definitions in EndpointTransport are `OneStackOneQueue`, `OneMixedPage`, and `Contains`. The latter quantifies an injective edge map and preserves every strict comparison of either endpoint of any two edges. Properness plus Apart makes all matching endpoints distinct. Vertices are natural-number positions; isolated vertices and gaps do not affect these comparisons. The literal 12/8 tables are in Geometry, with aliases `fig19a` and `fig19b`; they are not generated from criticality.

## Rank normalization and complete enumeration

Let X be the finite set of all endpoints. The position map from edges times {left,right} to X is injective, by properness and pairwise endpoint separation. Hence |X|=2m. The increasing bijection from Fin(2m) to X defines endpoint ranks. Every comparison is preserved, including comparisons between endpoints belonging to the same edge. Sort the edge type by its distinct left endpoints and map each edge to its two ranks. This gives the canonical row E, length m, proper and increasing in left endpoints. Its endpoints are exactly 0,…,2m−1, each once: all 2m ranks occur, and its endpoint-list length is 2m.

For completeness of the pairing recursion, more generally let E be proper and sorted by left endpoints, and let xs be a strictly increasing permutation of its endpoints. If E is empty, xs is empty. Otherwise its first left endpoint is the least of all endpoints, so it is the head of xs. The right endpoint of that edge occurs in xs’s tail. Remove it; the tail row satisfies the same hypotheses. Induction places the tail in the corresponding recursive branch, and prepending the head edge places E in `matchings E.length xs`.

The canonical edge bijection preserves every endpoint comparison. Pulling back a coloring along this bijection and its inverse proves equivalence of colorability. Composing the literal containment injection with the bijection proves containment equivalence in both directions. Restricting the structural six-edge core and applying this bridge gives an uncolorable enumerated row on at most six edges. No bound on the original edge type enters the statement. These arguments are formalized in RankNormalization, EnumeratorCompleteness, CanonicalRow and EndpointTransport.

## Prior art and significance

The supplied independent Opus review, dated 2026-11-20, reports that arXiv v2 still states Conjecture 31 and that the STACS 2025 version still leaves the characterization open. The review checked Haun’s 2023 precursor thesis and found no characterization. The source’s separated-case lemmas do not apply to arbitrary non-separated matchings; its general infinite-obstruction theorem concerns s≥2 and k≥2. Ordinary 2-SAT does not provide a bounded contradictory cycle. The proof’s substantive content is the six-edge bound, obtained by the interval-geometric C-N-C shortening and the container lemma. The source already supplied the candidate patterns. The one-page assertion is routine: two witnessing pairs use at most four edges. This is a modest elementary result, and a specialist may judge the main argument routine. No new priority search is claimed by this formalization stage. MathSciNet, zbMATH and exhaustive ProbXiv clearance remain unchecked in the supplied review.

## Certified finite witnesses and formal endpoint

The formal finite remainder does not assume that a Python generator covered all rows. Each of the 119 inherited certificates checks a branch by kernel reduction. A row's even code supplies a coloring bitmask; its odd code supplies a selected submatching whose rank-count normalization equals a literal Figure 19a pattern. The mask semantics prove that no stack-stack crossing and no queue-queue nesting occur. The selection semantics retain an injective index map. For normalization, counting endpoints below x is strictly less than counting endpoints below y exactly when x<y, for endpoints in the selected list; this proves preservation of every endpoint comparison. The finite pair tables map literally to Geometry's source Arc tables.

The coverage assembly unfolds the first endpoint's mate and, for six edges, the next least endpoint's mate, and uses all 99 six-edge and 20 smaller certificates. Thus every row of every matching enumerator through six edges is colorable or contains a source pattern. Applying the proved six-edge core and enumerated presentation gives the forward characterization. Conversely a layout restricts along the injective containment map, while each of the twelve literal patterns is kernel-checked uncolorable.

For one page, a failure contains a crossing pair and a nesting pair on at most four edges. The same presentation bridge applies. Five additional certificate modules, covering the full enumerators at sizes 0,1,2,3,4, give either an entirely crossing-free page, an entirely nesting-free page, or a selected submatching normalizing to a Figure 19b pattern. All eight literal patterns are kernel-checked failures of a one-page layout. Heredity proves the converse.

The final theorem is:

```lean
theorem haun_merker_pupyrev_conj31 {ι : Type} [Fintype ι] (M : OrderedMatching ι) :
  (OneStackOneQueue M ↔ ∀ P ∈ fig19a, ¬Contains M P) ∧
  (OneMixedPage M ↔ ∀ P ∈ fig19b, ¬Contains M P)
```

The packet's hash-linked receipts report successful compilation and standalone kernel checking for all 148 production modules with the supplied guarded runner. The final-check review verified the current source hashes and appendix identity without compiling Lean; root's independent kernel replay is separate. The final endpoint and both separate characterizations depend only on propext, Classical.choice and Quot.sound. There is no ambient size cap or unproved normalization, coverage or model-equivalence hypothesis. The appendix reproduces every production source byte-exact in import order. REPORT.md and the hash-linked receipts document the build. Independent final review and acceptance remain with root; this packet is not a publication or a worldwide priority clearance.

## Final-check prior-art refresh (20 November 2026)

The independent final-check lane re-read arXiv v2 (still the latest listed version) and the STACS proceedings discussion, and checked the authors' publication listing, arXiv keyword results, and OpenAlex and Semantic Scholar citation lists. The two research citers found were [capacitated stack/queue layouts](https://arxiv.org/abs/2610.18071) and [transforming stacks into queues](https://arxiv.org/abs/2409.17776); their stated results do not supply the fixed-order matching obstruction characterization. No later journal resolution was found. Searches of the prescribed Principia, mio-qwq, omega and openai/math local archives, two GitHub code queries and the two required fresh omega issue queries found no relevant resolution. This is bounded evidence, not exhaustive priority clearance: ProbXiv returned HTTP 402 and was not accessed further; MathSciNet and zbMATH were not checked. The source's Lemma 27 already yields the four-edge bound behind part (ii); the claimed contribution remains the modest interval-geometric six-edge bound for part (i).
