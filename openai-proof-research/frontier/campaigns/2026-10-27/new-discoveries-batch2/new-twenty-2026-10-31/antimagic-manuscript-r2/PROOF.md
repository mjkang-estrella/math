# Mathematical proof and exact formula

DRAFT; AI-assisted. No acceptance or priority claim. Source attributions and limitations are retained in paper.md.

## 1. Definitions and statement

All graphs here are finite, simple and undirected. As in [1, Definition 1.1 and its standing graph convention], isolated vertices and K₂ components are excluded. A local antimagic labelling is a bijection f: E(G) → {1, …, m}, where m = |E(G)|, such that the incident sums w(v) = Σ{f(e): e incident to v} differ at adjacent vertices. Its colour count is the number of distinct sums. The least attainable count is χ_la(G).

A complete full t-ary tree is rooted, every nonleaf has exactly t children, and all leaves have a common depth n [1, Definitions 1.3–1.4]. Write T(t,n) for this tree, with rows V_h of size t^h, h = 0, …, n. Its edges in row h join V_(h−1) to V_h. We assume n ≥ 1 and t ≥ 2; the isolated depth-zero tree is outside the source’s standing domain. There are l = t^n degree-one leaves and m = Σ_(h=1)^n t^h edges.

Published Conjecture 6.1 of [1], transcribed verbatim with mathematical typography, is:

“For any complete full t-ary tree T, t ≥ 2 even, χ_la(T) = l + 1, where l is the number of degree one vertices (leaves) of T.”

Theorem. For every even t ≥ 2 and n ≥ 1, χ_la(T(t,n)) = t^n + 1. Consequently every complete full t-ary tree T with even t ≥ 2 satisfies χ_la(T) = l + 1.

The source proves the odd-branching case in Theorem 4.1 and places the even case in {l + 1, l + 2} in Theorem 5.1. Only the even case is proved here. Sections 2–6 give a self-contained construction; Section 7 relates it to the formal endpoints.


## 2. Source ingredients and the lower bound

The lower bound is [1, Theorem 1.2], which credits Arumugam, Premalatha, Bača and Semaničová-Feňovčíková [2]. It is distinct from the tuple statements in Lemmas 2.9 and 2.10. We include its proof for the present trees.

For any labelling, each leaf weight equals its incident edge label. Distinct leaves have distinct incident edges: an edge joining two leaves would be a K₂ component, impossible here. Thus there are l different leaf weights, all at most m. Take the edge labelled m and its endpoint nearer the root. This endpoint is internal and has at least t ≥ 2 child edges. At least one other incident edge therefore has a positive label, so its weight exceeds m. This is an additional colour. Hence every local antimagic labelling uses at least l + 1 colours. This argument even holds without assuming properness.

Published Lemma 2.9 of [1] says that any tq consecutive integers, with t ≥ 2 even and q odd, can be partitioned into q t-tuples with q consecutive sums. Its proof uses reversed outer blocks and the two-block pairing of Lemma 2.2. We make this ingredient explicit in Section 3.

Published Lemma 2.10 says that for t ≥ 2 even and q even one can obtain q − 1 consecutive tuple sums and one isolated sum, but cannot obtain q consecutive sums. The impossibility also follows from averages: the mean of t-tuples partitioning consecutive integers is t times a half-integer, hence an integer for even t, whereas the mean of q consecutive integer sums is a half-integer for even q. These cannot agree. For the source’s higher-depth scheme, the incoming final-parent labels form a consecutive block of even size q = t^(n−1). Making all final-parent weights equal would require consecutive leaf-tuple sums, which is impossible. The source obtains two colours above m instead. This obstruction concerns that scheme, not all labellings. Our incoming labels have a central hole and avoid the obstruction.

For n = 1, give root edges labels 1, …, t. The root weight t(t+1)/2 exceeds t, so the leaves and root give exactly t + 1 colours, properly.

For n = 2 and t = 2, use [1, Figure 5], up to swapping sibling leaves. The root edges have labels (1,4); the two ordered pairs of leaf labels are (2,3) and (6,5). The root and first-row weights are 5, 6 and 15. Leaf weights are 2, 3, 6 and 5, so the full colour set is {2,3,5,6,15}. Each first-row vertex differs from its own leaves and from the root. This gives five colours. This example is credited entirely to the source.

For all remaining cases we give a closed formula on ordered edges. Order each row V_h as (h,i), 0 ≤ i < t^h, with parent (h−1, floor(i/t)). Let f(h,i) label its incoming edge. These row coordinates impose no extra graph hypothesis: any choice of child orders gives this model. At the end we transport the result to arbitrary full trees.


## 3. Depth two with t ≥ 4: a construction from source ingredients

Put t = 2s, s ≥ 2, q = t−1, k = s−1 and M = t²+t. The root labels are f(1,0) = 2 and f(1,p) = 3s+2−p for 1 ≤ p ≤ q. Their set is {2} ∪ [s+3,3s+1]. Vertex (1,0) receives the following leaf labels, in slots j = 0, …, t−1:

f(2,j) = 1 if j = 0; j+2 if 1 ≤ j ≤ s; 2s+1+j if s < j < t.

Their set is S* = {1} ∪ [3,s+2] ∪ [3s+2,4s]. It has t members. The root labels and S* partition [1,2t]. The remaining labels form B = [2t+1,M], a run of tq integers. We give an explicit version of the source’s Lemmas 2.2 and 2.9 to partition B.

For parent p = 1, …, q, set a = p−1 and β = 2t+(s−1)q. Its slots j < t−2 are indexed j = 2b,2b+1, 0 ≤ b < s−1, and have labels

f(2,tp+2b) = 2t+bq+a+1,
f(2,tp+2b+1) = 2t+(t−1−b)q+q−a.

If a ≤ k, the last two labels are β+2a+1 and β+3k+2−a. If a > k, put r = a−k; the last two labels are β+2r and β+4k+3−r. These are precisely the depthTwoLabel branches in AntimagicLabel.lean.

Bijectivity. The outer slots take every entry of the first s−1 and last s−1 blocks of B exactly once: a runs through 0, …, q−1, in forward and reverse order. The middle two blocks are the run β+[1,4k+2]. Their first coordinates are the odds 1,3, …, 2k+1 and evens 2,4, …, 2k. Their second coordinates are [2k+2,3k+2] and [3k+3,4k+2]. These four disjoint sets cover the middle run. Thus the whole edge labelling is a bijection onto [1,M].

Weights. Every outer pair sums to H = 4t+tq+1. The middle pair sums to 2β+3k+3+a in both branches. Thus the leaf tuple at p has sum D+p−1, where D = (s−1)H+2β+3k+3. Its parent weight is the constant C = D+3s+1. The root sum is 2+(2s−1)(2s+2) = M. The sum of S* is s(4s+1)·2−M = t², so (1,0) has weight t²+2.

Both M and t²+2 lie in B because t ≥ 4. Every ordinary-parent weight C exceeds t(2t+1) > M, since all its t leaf labels lie in B and its incoming label is positive. The exceptional parent weight exceeds 2t, the largest label in S*. It differs from M because t ≠ 2. Hence all adjacencies are proper, and the colours are exactly the t² leaf labels together with C. This proves the theorem at depth two.


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


## 6. The binary patch and checkable examples

Let t = 2 and n ≥ 3. Then N = 2^n−2 = 2Z, q = Z+1 and m = 4Z+2, with Z ≥ 3. The root edges have labels Z and 2Z. The row-two transposition in Section 4 gives row-two labels, in coordinate order,

(2, 2Z−1, 1, 2Z−2).

The first two belong to the child with incoming label Z, the next two to the child with incoming label 2Z. Their child-label sums are 2Z+1 and 2Z−1. Thus the root weight is 3Z and the first-row weights are 3Z+1 and 4Z−1. All are in Λ = [2Z+1,4Z+2]. The root differs from both first-row weights because Z ≥ 3.

All other middle vertices have child-label sum 2Z. Indeed only row two is permuted; when h ≥ 2, its child row is unpatched and begins at an even shell coordinate. Thus middle weights from row two onward are incoming label plus 2Z, lying in Λ. The final parents have the constant C from Section 5, which exceeds m. The same displacement and bijectivity arguments remain valid when n = 3, because the row-two transposition preserves the entire parent-label set and the leaf parameter is computed from the actual patched parent label.

For n = 3, row two is the final-parent row, so it differs from row one by C > m. For n ≥ 4, Z = 2^(n−1)−1 ≥ 7 and the row-two weights are (2Z+2,4Z−1,2Z+1,4Z−2). The first-row weight 3Z+1 differs from its own children 2Z+2 and 4Z−1, since equality would force Z = 1 or Z = 2. The other first-row weight 4Z−1 differs from its children 2Z+1 and 4Z−2 since Z ≥ 7. Lower middle edges separate by distinct incoming labels under the same translation. The edges at the final parents and leaves separate by C > m. This proves properness and the exact colour set Λ ∪ {C} for the binary case.

Example t = 2, n = 3. Here N = 6, Z = 3, q = 4 and m = 14. The ordered edge-label rows are (3,6), (2,5,1,4), and (10,12,8,11,9,14,7,13). The weight rows are (9), (10,11), (24,24,24,24), followed by the eight leaf labels. Thus the colour set is [7,14] ∪ {24}, nine colours. The first-row weights already appear on nonincident leaves; equality of nonadjacent weights is permitted.

Example t = 4, n = 3. Here N = 20, Z = 9, q = 16, m = 84. The internal rows are (9,18,19,20) and (8,10,7,11,6,12,5,13,4,14,3,15,2,16,1,17). The root weighs 66 and row one weighs (45,54,55,56). All 16 final parents weigh C = 219. Leaves use [21,84]. For the first final parent, p = 8 gives a = 16 and σ(a) = 15, so its leaf tuple is (36,69,52,54), summing to 211; adding p gives 219. The other tuples follow the same explicit formula, partitioning the high interval. Hence exactly 65 colours occur.


