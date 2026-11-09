# Symmetric-shell labellings of complete full trees with even branching

DRAFT • AI-assisted research manuscript • MathDB 354228

This draft was assembled with OpenAI Codex assistance from the frozen discovery, review and Lean packets identified in the accompanying dossier. No human authorship or affiliation is asserted. It has not been published or accepted. Acceptance and credit remain solely with the campaign root; this lane claims zero accepted credit.

## Abstract

For every even integer t ≥ 2 and every positive depth n, we construct a local antimagic labelling of the complete full t-ary tree with exactly t^n + 1 vertex weights. Together with the leaf lower bound, this proves the even case of Conjecture 6.1 of Bača, Semaničová-Feňovčíková, Lai and Wang [1]. The higher-depth construction replaces consecutive internal label blocks by symmetric shells and couples the final row to a displacement permutation. Binary trees require one transposition in row two. The depth-two binary labelling is already Figure 5 of [1]; the other depth-two case is built from that paper’s ingredients. The accompanying byte-identical Lean packet contains unconditional endpoints for the model and for every finite graph carrying the structural full-tree certificate. The literature screening is bounded and two closed-access leads remain unread. No priority claim is made; significance is modest and qualified.

## 1. Definitions and statement

All graphs here are finite, simple and undirected. As in [1, Definition 1.1 and its standing graph convention], isolated vertices and K₂ components are excluded. A local antimagic labelling is a bijection f: E(G) → {1, …, m}, where m = |E(G)|, such that the incident sums w(v) = Σ{f(e): e incident to v} differ at adjacent vertices. Its colour count is the number of distinct sums. The least attainable count is χ_la(G).

A complete full t-ary tree is rooted, every nonleaf has exactly t children, and all leaves have a common depth n [1, Definitions 1.3–1.4]. Write T(t,n) for this tree, with rows V_h of size t^h, h = 0, …, n. Its edges in row h join V_(h−1) to V_h. We assume n ≥ 1 and t ≥ 2; the isolated depth-zero tree is outside the source’s standing domain. There are l = t^n degree-one leaves and m = Σ_(h=1)^n t^h edges.

Published Conjecture 6.1 of [1], transcribed verbatim with mathematical typography, is:

“For any complete full t-ary tree T, t ≥ 2 even, χ_la(T) = l + 1, where l is the number of degree one vertices (leaves) of T.”

Theorem. For every even t ≥ 2 and n ≥ 1, χ_la(T(t,n)) = t^n + 1. Consequently every complete full t-ary tree T with even t ≥ 2 satisfies χ_la(T) = l + 1.

The source proves the odd-branching case in Theorem 4.1 and places the even case in {l + 1, l + 2} in Theorem 5.1. Only the even case is proved here. Sections 2–6 give a self-contained construction; Section 7 relates it to the formal endpoints.

---PAGE---
## 2. Source ingredients and the lower bound

The lower bound is [1, Theorem 1.2], which credits Arumugam, Premalatha, Bača and Semaničová-Feňovčíková [2]. It is distinct from the tuple statements in Lemmas 2.9 and 2.10. We include its proof for the present trees.

For any labelling, each leaf weight equals its incident edge label. Distinct leaves have distinct incident edges: an edge joining two leaves would be a K₂ component, impossible here. Thus there are l different leaf weights, all at most m. Take the edge labelled m and its endpoint nearer the root. This endpoint is internal and has at least t ≥ 2 child edges. At least one other incident edge therefore has a positive label, so its weight exceeds m. This is an additional colour. Hence every local antimagic labelling uses at least l + 1 colours. This argument even holds without assuming properness.

Published Lemma 2.9 of [1] says that any tq consecutive integers, with t ≥ 2 even and q odd, can be partitioned into q t-tuples with q consecutive sums. Its proof uses reversed outer blocks and the two-block pairing of Lemma 2.2. We make this ingredient explicit in Section 3.

Published Lemma 2.10 says that for t ≥ 2 even and q even one can obtain q − 1 consecutive tuple sums and one isolated sum, but cannot obtain q consecutive sums. The impossibility also follows from averages: the mean of t-tuples partitioning consecutive integers is t times a half-integer, hence an integer for even t, whereas the mean of q consecutive integer sums is a half-integer for even q. These cannot agree. For the source’s higher-depth scheme, the incoming final-parent labels form a consecutive block of even size q = t^(n−1). Making all final-parent weights equal would require consecutive leaf-tuple sums, which is impossible. The source obtains two colours above m instead. This obstruction concerns that scheme, not all labellings. Our incoming labels have a central hole and avoid the obstruction.

For n = 1, give root edges labels 1, …, t. The root weight t(t+1)/2 exceeds t, so the leaves and root give exactly t + 1 colours, properly.

For n = 2 and t = 2, use [1, Figure 5], up to swapping sibling leaves. The root edges have labels (1,4); the two ordered pairs of leaf labels are (2,3) and (6,5). The root and first-row weights are 5, 6 and 15. Leaf weights are 2, 3, 6 and 5, so the full colour set is {2,3,5,6,15}. Each first-row vertex differs from its own leaves and from the root. This gives five colours. This example is credited entirely to the source.

For all remaining cases we give a closed formula on ordered edges. Order each row V_h as (h,i), 0 ≤ i < t^h, with parent (h−1, floor(i/t)). Let f(h,i) label its incoming edge. These row coordinates impose no extra graph hypothesis: any choice of child orders gives this model. At the end we transport the result to arbitrary full trees.

---PAGE---
## 3. Depth two with t ≥ 4: a construction from source ingredients

Put t = 2s, s ≥ 2, q = t−1, k = s−1 and M = t²+t. The root labels are f(1,0) = 2 and f(1,p) = 3s+2−p for 1 ≤ p ≤ q. Their set is {2} ∪ [s+3,3s+1]. Vertex (1,0) receives the following leaf labels, in slots j = 0, …, t−1:

f(2,j) = 1 if j = 0; j+2 if 1 ≤ j ≤ s; 2s+1+j if s < j < t.

Their set is S* = {1} ∪ [3,s+2] ∪ [3s+2,4s]. It has t members. The root labels and S* partition [1,2t]. The remaining labels form B = [2t+1,M], a run of tq integers. We give an explicit version of the source’s Lemmas 2.2 and 2.9 to partition B.

For parent p = 1, …, q, set a = p−1 and β = 2t+(s−1)q. Its slots j < t−2 are indexed j = 2b,2b+1, 0 ≤ b < s−1, and have labels

f(2,tp+2b) = 2t+bq+a+1,
f(2,tp+2b+1) = 2t+(t−1−b)q+q−a.

If a ≤ k, the last two labels are β+2a+1 and β+3k+2−a. If a > k, put r = a−k; the last two labels are β+2r and β+4k+3−r. These are precisely the depthTwoLabel branches in AntimagicLabel.lean.

Bijectivity. The outer slots take every entry of the first s−1 and last s−1 blocks of B exactly once: a runs through 0, …, q−1, in forward and reverse order. The middle two blocks are the run β+[1,4k+2]. Their first coordinates are the odds 1,3, …, 2k+1 and evens 2,4, …, 2k. Their second coordinates are [2k+2,3k+2] and [3k+3,4k+2]. These four disjoint sets cover the middle run. Thus the whole edge labelling is a bijection onto [1,M].

Weights. Every outer pair sums to H = 4t+(t−1)q+1. The middle pair sums to 2β+3k+3+a in both branches. Thus the leaf tuple at p has sum D+p−1, where D = (s−1)H+2β+3k+3. Its parent weight is the constant C = D+3s+1. The root sum is 2+(2s−1)(2s+2) = M. The sum of S* is s(4s+1)·2−M = t², so (1,0) has weight t²+2.

Both M and t²+2 lie in B because t ≥ 4. Every ordinary-parent weight C exceeds t(2t+1) > M, since all its t leaf labels lie in B and its incoming label is positive. The exceptional parent weight exceeds 2t, the largest label in S*. It differs from M because t ≠ 2. Hence all adjacencies are proper, and the colours are exactly the t² leaf labels together with C. This proves the theorem at depth two.

---PAGE---
## 4. Closed formula for n ≥ 3 and its bijectivity

Let N = Σ_(h=1)^(n−1) t^h, q = t^(n−1), k = q/2, R = (N−t)/2, Z = R+1, and m = N+tq. For h ≥ 2 let O_h = Σ_(g=h+1)^(n−1) t^g. All these quantities are integers. Define P_h(i) = 4−i if t = 2, h = 2 and i is 1 or 3; otherwise P_h(i) = i. This transposition is the binary patch.

For internal edges the frozen formula is

f(1,0) = Z;    f(1,i) = N−t+1+i for 1 ≤ i < t.
For 2 ≤ h < n: r = O_h+P_h(i), d = 1+floor(r/2),
f(h,i) = Z−d for even r, and Z+d for odd r.

Define σ(a) = 2a for 1 ≤ a ≤ k, and σ(k+j) = 2j−1 for 1 ≤ j ≤ k. For an incoming parent label p = f(n−1,u), set a = p−Z if p > Z, and a = q+1+p−Z otherwise. Write λ_b(x) = N+(b−1)q+x. Its leaf labels in slots j = 0, …, t−1 are:

j = 2b−2, 1 ≤ b < t/2: λ_b(a);
j = 2b−1, 1 ≤ b < t/2: λ_(t+1−b)(q+1−a);
j = t−2: λ_(t/2)(a);
j = t−1: λ_(t/2+1)(q+1−σ(a)).

For t = 2 the first two families are empty. On the stated domains all subtractions above are nonnegative, agreeing with Lean natural subtraction. For n = 1 use f(1,i) = i+1; for n = 2 use Section 3 or Figure 5. This exhausts AntimagicLabel.label without any recursive search or unspecified assignment.

Internal bijectivity. The intervals [O_h,O_h+t^h), h = n−1, …, 2, concatenate to [0,N−t). They have even endpoints. Each P_h permutes its own row; hence r runs once through [0,2R). Even and odd coordinates give the pairs {Z−d,Z+d}, 1 ≤ d ≤ R. These pairs are disjoint and cover [1,N−t+1] except Z. Row one supplies Z and [N−t+2,N]. Thus internal edges receive exactly [1,N].

Leaf bijectivity. The final internal row has O_(n−1) = 0, so its labels are Z±d, 1 ≤ d ≤ k, even when n = 3 and the row is patched. Their a-values are d and q+1−d respectively, covering [1,q] exactly. The map σ permutes [1,q], sending the lower half to the evens and the upper half to the odds. In each leaf block [N+(b−1)q+1,N+bq], one slot family uses a permutation of [1,q]. Thus all leaf labels are exactly [N+1,m], once each. Combined with the internal bijection, this proves full bijectivity.

---PAGE---
## 5. Weight identities and the nonbinary higher-depth case

Write δ(a) = a−σ(a), now as an integer. Its values are −a for a ≤ k and k+1−j for a = k+j. Thus δ permutes {−k, …, −1,1, …, k}. The parameter associated to an incoming label p satisfies p+δ(a) = Z: for p = Z+d take a = d, and for p = Z−d take a = q+1−d. This is the cancellation that replaces consecutive tuple sums.

Every outer leaf pair has sum L = 2N+tq+1. The middle pair has sum L+δ(a). Consequently every final parent has the same weight

C = (t/2)(2N+tq+1)+Z > m.

The strict inequality holds since t/2 ≥ 1 and 2N+tq+1 > N+tq. Every leaf has weight its label in Λ = [N+1,m].

Suppose first t ≥ 4. The patch is absent. At a vertex in row h, 1 ≤ h ≤ n−2, its child coordinates are O_(h+1)+ti+j. The initial coordinate is even. Pairing j = 2b,2b+1 gives labels Z−d,Z+d, so the child-label sum is tZ. The weight at this vertex is therefore f(h,i)+tZ. The root weight is

W = Z+(t−1)N−(t−1)(t−2)/2.

To place the weights, note the geometric identities (t−1)N = t^n−t and N = 2Z+t−2. Also N−t = Σ_(h=2)^(n−1) t^h < 2q. Since N−t is even, N−t ≤ 2q−2, and Z ≤ q. Finally tZ−N = (t/2−1)(N−t) ≥ 0. It follows that

N+1 ≤ tZ+f(h,i) ≤ tZ+N ≤ tq+N = m.

For the root, substitution yields W−tZ = (t−1)N/2 > N because t ≥ 4. Hence W > N. On the other hand W < tN = m−t < m, since Z < N and the subtracted term is nonnegative. Thus every weight other than C is in Λ.

Properness follows by exhausting edge types. Leaves differ from final parents since C > m. Final parents differ from row n−2 since that row has weights at most m. Between any two remaining positive-depth rows, weights are their distinct incoming labels translated by the same tZ. Distinctness follows from internal bijectivity. Finally W > tZ+N is above every row-one weight. There are no other edges. Every value of Λ occurs at a leaf and C is attained, so the colour set is exactly Λ ∪ {C}, with tq+1 = t^n+1 elements.

The hole at Z is essential to this arrangement: the incoming final-parent labels Z±1, …, Z±k are cancelled by δ, while shell pairs in every earlier row retain the same sum. This is the higher-depth ingredient beyond the source’s consecutive-block scheme.

---PAGE---
## 6. The binary patch and checkable examples

Let t = 2 and n ≥ 3. Then N = 2^n−2 = 2Z, q = Z+1 and m = 4Z+2, with Z ≥ 3. The root edges have labels Z and 2Z. The row-two transposition in Section 4 gives row-two labels, in coordinate order,

(2, 2Z−1, 1, 2Z−2).

The first two belong to the child with incoming label Z, the next two to the child with incoming label 2Z. Their child-label sums are 2Z+1 and 2Z−1. Thus the root weight is 3Z and the first-row weights are 3Z+1 and 4Z−1. All are in Λ = [2Z+1,4Z+2]. The root differs from both first-row weights because Z ≥ 3.

All other middle vertices have child-label sum 2Z. Indeed only row two is permuted; when h ≥ 2, its child row is unpatched and begins at an even shell coordinate. Thus middle weights from row two onward are incoming label plus 2Z, lying in Λ. The final parents have the constant C from Section 5, which exceeds m. The same displacement and bijectivity arguments remain valid when n = 3, because the row-two transposition preserves the entire parent-label set and the leaf parameter is computed from the actual patched parent label.

For n = 3, row two is the final-parent row, so it differs from row one by C > m. For n ≥ 4, Z = 2^(n−1)−1 ≥ 7 and the row-two weights are (2Z+2,4Z−1,2Z+1,4Z−2). The first-row weight 3Z+1 differs from its own children 2Z+2 and 4Z−1, since equality would force Z = 1 or Z = 2. The other first-row weight 4Z−1 differs from its children 2Z+1 and 4Z−2 since Z ≥ 7. Lower middle edges separate by distinct incoming labels under the same translation. The edges at the final parents and leaves separate by C > m. This proves properness and the exact colour set Λ ∪ {C} for the binary case.

Example t = 2, n = 3. Here N = 6, Z = 3, q = 4 and m = 14. The ordered edge-label rows are (3,6), (2,5,1,4), and (10,14,8,13,9,12,7,11). The weight rows are (9), (10,11), (26,26,26,26), followed by the eight leaf labels. Thus the colour set is [7,14] ∪ {26}, nine colours. The first-row weights already appear on nonincident leaves; equality of nonadjacent weights is permitted.

Example t = 4, n = 3. Here N = 20, Z = 9, q = 16, m = 84. The internal rows are (9,18,19,20) and (8,10,7,11,6,12,5,13,4,14,3,15,2,16,1,17). The root weighs 66 and row one weighs (45,54,55,56). All 16 final parents weigh C = 219. Leaves use [21,84]. For the first final parent, p = 8 gives a = 16 and σ(a) = 15, so its leaf tuple is (36,69,52,54), summing to 211; adding p gives 219. The other tuples follow the same explicit formula, partitioning the high interval. Hence exactly 65 colours occur.

---PAGE---
## 7. Formal correspondence, audits and reproducibility

The reused packet lean-source.zip has SHA-256 987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175. It contains 54 Lean modules, developed through rounds r1–r7a and the r4b bridge. Earlier endpoints explicitly assumed residual construction predicates; only the final namespace Antimagic.Round7A has both construction and bridge obligations discharged. No fresh Lean execution is claimed in this manuscript lane.

AntimagicBasics.Labeling is an equivalence from G.edgeSet (unordered Sym2 edges) to Fin |E|. Weight sums each incident value plus one, exactly translating zero-based Fin values to labels 1, …, |E|. IsLocal compares adjacent vertices. colorCount is the cardinality of the image of weight; spectrum is the set of attainable local colour counts, and chiLA is its natural infimum. An IsLeast conclusion supplies a member and a lower bound, preventing a false conclusion from an empty totalized spectrum. numLeaves counts graph degree one.

AntimagicModel.tree has vertices (h,i), h ≤ n, i < t^h, with child relation h increasing by one and child index divided by t equal to parent index. The FullTree certificate records treehood, a root characterized by depth zero, oriented adjacency, unit depth increments, unique parents, a depth bound n, and exactly t children below depth n and zero at n. Source trees provide such data from their root and common leaf depth. Conversely the data force all terminal vertices to be at n; taking children reaches that depth. The modelStructure theorem supplies actual data for t ≥ 2, n ≥ 1, so the theorem is not vacuous. Model leaves are exactly row n; root degree t is not one, and other internal degrees are t+1.

The r4b bridge orders each finite child set, constructs layer equivalences by induction from the unique roots, and uses unique parents to obtain bijections between successive layers and parent-slot pairs. It preserves and reflects children, hence adjacency. This gives G ≃g tree t n for every FullTree G t n. AntimagicIso transports edge labellings, incident sums, spectra, colour counts, degree-one leaves and chiLA through that isomorphism.

The exact final endpoints, with natural t,n, are:

Antimagic.Round7A.even_case (t n) (ht: 2 ≤ t) (he: Even t) (hn: 1 ≤ n): IsLeast (spectrum (tree t n)) (t^n+1).

Antimagic.Round7A.mathdb_354228, for every finite vertex type with decidable equality and every SimpleGraph G with decidable adjacency, takes t,n, ht,he,hn as above and full: FullTree G t n, and proves IsLeast (spectrum G) (numLeaves G+1) ∧ chiLA G = numLeaves G+1.

The formalization proves agreement with the frozen formula on every child edge, rather than only existence of weights with desirable values. Incidence reindexing links row sums to graph weights. Depth-two, nonbinary higher and binary higher constructions combine with the star and Figure 5 cases. The lower bound and isomorphism bridge then yield both endpoints. The packet’s definitions are total outside the source’s domain, but the endpoint trees have no isolated vertices or K₂ components, as does every graph isomorphic to them.

---PAGE---
## 8. Evidence, trust limits and related work

The formal r7a report records strict serial local and fresh-extracted replays: all 54 modules compiled and all 54 explicit-module leanchecker calls passed, using Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The independent fidelity review reports a corrected fresh extraction with the same 54+54 successes, 1,434 local declarations audited, and both endpoints depending only on propext, Classical.choice and Quot.sound. Its source and metadata scans found no local proof placeholders, added axioms, unsafe, partial, implemented_by, extern or _unsafe_rec declarations. Pinned upstream execution metadata is separately reported; this is not a claim that all imported implementation metadata is absent.

That review’s preliminary process-group-monitoring run was stopped and excluded; the qualifying run used the corrected wrapper. Its numerical transcription checked 23 cases, with missing-patch and duplicate-label negative controls. Numerical evidence is diagnostic, not the proof. The present lane checks archive safety and byte identity, reproduces the two worked examples, hashes inputs before and after, and renders every manuscript page. It does not run Lean, lake or leanchecker. The parent receipt of 2026-11-04 07:31 UTC reports PASS for its own fresh 54-module strict replay and explicit-module checks, with the same three endpoint axioms. Its registry refresh reports no relevant path hits at OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae and Omega head 1fbcd475b38a8b2edc731cef42f143dcd25f15e1; this was a complete selected-tree path screen, not a full-body proof search. Kernel checking validates a formal statement relative to Lean, its foundations and pinned dependencies; correspondence review connects that statement to the paper. Neither establishes literary novelty or priority.

The root ruling rates significance QUALIFIED_PASS, modest. The full even case is the intended scope, with the higher-depth shell arrangement as its substantive ingredient. Figure 5 is pre-existing; depth two with t ≥ 4 uses [1, Lemmas 2.2 and 2.9]. The discovery notes’ HTML numbering is not used here. The lower bound is [1, Theorem 1.2], not Lemma 2.9.

The inherited prior-art work consists of bounded arXiv and OpenAlex screens, not an exhaustive literature review. The fidelity refresh screened 319 OpenAlex records and narrower title queries. Two arXiv listing requests failed, so complete listing coverage is not claimed. Brondani–Franca, arXiv:2610.22783 [3], concerns counterexamples to the general tree leaf conjecture, not a resolution of this even complete-full-tree case. Sarath–Prajeesh [4] is closed access and UNREAD: its advertised diameter-three and certain diameter-four scope could overlap at most depth two, since diameter T(t,n) = 2n. Premalatha–Arumugam–Lee–Wang [5] is also closed access and UNREAD. Its abstract’s unspecified tree families do not justify restricting its possible overlap to depth two. This residual uncertainty qualifies the earlier root assessment. No priority claim is made and no acceptance is inferred from these searches.

## References

[1] Martin Bača, Andrea Semaničová-Feňovčíková, Ruei-Ting Lai and Tao-Ming Wang. On Local Antimagic Vertex Coloring for Complete Full t-ary Trees. Fundamenta Informaticae 185(2) (2022), 99–113. DOI: 10.3233/FI-222105. arXiv:2204.04479v2. Published PDF read from the frozen review cache.

[2] S. Arumugam, K. Premalatha, M. Bača and A. Semaničová-Feňovčíková. Local antimagic vertex coloring of a graph. Graphs and Combinatorics 33(2) (2017), 275–285. DOI: 10.1007/s00373-017-1758-7. Cited via [1], not independently read here.

[3] André Ebling Brondani and Francisca Andrea Macedo França. Counterexamples to the local antimagic leaf conjecture. arXiv:2610.22783v1 (16 October 2026). Source metadata checked in the archived body; scope discussion follows the inherited review.

[4] Sarath–Prajeesh. ICEEICT (2023). DOI: 10.1109/ICEEICT56924.2023.10157500. Closed-access, unread lead; advertised tree scope as stated above. Citation metadata is limited to the frozen review evidence.

[5] K. Premalatha, S. Arumugam, Y.-C. Lee and T.-M. Wang. Local antimagic chromatic number of trees - I. DOI: 10.1080/09720529.2020.1772985. Online 2020 / journal 2022 according to the archived metadata; closed access and unread.
