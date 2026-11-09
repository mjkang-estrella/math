# A six-vertex obstruction to cube common-cover transitivity

Status: complete ordinary mathematical refutation of the universal assertion in Hemminger–Landesman–Yao, *Peckness of Edge Posets*, arXiv:1501.04540v2 (10 December 2017), Question 6.6, PDF p17. Source Definition 1.4 and Theorem 1.5 are on p3. No acceptance or discovery credit requested by this document alone. No Lean endpoint is supplied.

**Literal result.** For every integer n≥5, the group of linear automorphisms of the cube with vertices {−1,1}^n does **not** induce a common cover transitive action on the Boolean algebra of its 2^n vertices. Thus the answer to the source's all-dimensional question is negative. No claim is made that its main Conjecture 1.3 (Peckness of edge posets of Boolean quotients) is false. CCT is a sufficient hypothesis there, not a necessary one.

Recall the exact definition: an action on a poset is CCT if, whenever X and Y are both covered by Z and Y belongs to the orbit of X, some group element stabilizing Z sends X to Y.

Identify cube vertices with binary vectors v=(v0,…,v4) by sending vi to (−1)^vi; write the vector as the integer Σ2^i vi. Hamming distance is denoted d. Take

Z={2,9,10,13,19,20}, X=Z\{9}, Y=Z\{2}.

Both X and Y are covered by Z in the Boolean inclusion order. Define a cube symmetry g by permuting bit positions via

p=(0,3,4,2,1), followed by flipping bit0:
g(v)=1 XOR Σ_i 2^{p(i)} vi.

In real coordinates this is a signed coordinate permutation, so it is a linear automorphism of the centered cube. Its action on X is

|v|2|10|13|19|20|
|---|---|---|---|---|---|
|g(v)|9|13|20|10|19|

Consequently gX=Y. We prove that no symmetry stabilizing Z sends X to Y.

Every linear automorphism of the cube preserves Hamming distance on its vertices. For completeness, an invertible linear map carrying the vertex set onto itself carries its convex hull onto itself, carries faces and edges onto faces and edges, and hence preserves distance in the cube graph. That graph distance is exactly the number of differing coordinates. This argument does not assume orthogonality in advance.

For v∈Z define its distance profile c(v)=(#{w∈Z:d(v,w)=j})_{j=0}^5. Direct bit comparison gives:

|v|c(v)|
|---|---|
|2|(1,1,1,2,1,0)|
|9|(1,1,1,2,1,0)|
|10|(1,1,1,2,1,0)|
|13|(1,1,0,2,2,0)|
|19|(1,0,1,3,1,0)|
|20|(1,0,0,3,2,0)|

Thus 13 is the unique vertex of Z with its profile. Any symmetry h stabilizing Z fixes 13. If hX=Y, then h(Z\X)=Z\Y implies h(9)=2. But d(9,13)=1 and d(2,13)=4, a contradiction. This proves the dimension-5 obstruction.

For every n>5 append n−5 zero bits to each of the same six vectors, and extend g by fixing the extra coordinates. The mapping table and all pairwise distances remain unchanged. Any n-cube symmetry stabilizing this embedded Z preserves its intrinsic distance profiles and therefore fixes 13, giving exactly the same contradiction. Extra-coordinate permutations cannot evade a metric invariant. This proves the literal all-n≥5 assertion without extrapolating from a finite computation.

## Independent exact checks and sustained routes

The initial full orbit enumeration in dimension4 found no CCT obstruction among all 65,536 subsets under all384 signed coordinate permutations. This negative search is not used in the proof and is not claimed as a new theorem. A separate cycle construction in dimension5 produced a 24-point Z; complete enumeration of unions of the fixed symmetry's cycles plus one partial cycle reduced it to the six vertices above. The proof then discarded search dependence in favor of the distance-profile invariant.

`verify_math.py` reconstructs the map, all distances and profiles from integers, and independently enumerates all 3,840 signed coordinate permutations in dimension5. It finds two transports X→Y and only the identity stabilizer of Z. The metric proof only needs the weaker fact that no such stabilizer transports X→Y. `math-verification.json` contains the full matrix and exact output. No floating point, solver trust, probabilistic inference or numerical approximation is used.

## Strongest classical bridge objection and priority limits

This is a small point-set deletion ambiguity, expressible through standard permutation-group stabilizers and metric vertex signatures. A reviewer should actively check prior work on pseudosimilar vertices, hypomorphic point configurations and cube reconstruction: a published example or theorem yielding this exact cube action would defeat novelty even under another vocabulary. The proof is short; shortness itself is not evidence of novelty or of duplication.

The closest source-level negative theorem is Proposition4.20(2), PDFp15: every finite non-elementary-abelian-2 group has **some** non-CCT Boolean action, specifically its left-regular action on its own group elements. That does not supply the particular action of the n-cube group on its 2^n vertices. For n5 the two underlying sets have sizes3,840 and32. Non-CCT for a subgroup also does not imply non-CCT for a larger group, since a larger stabilizer may restore the missing transport. The metric obstruction above handles the entire cube group and every higher-dimensional stabilizer; this is the missing bridge that the regular-action theorem does not establish. Source Theorem1.5 is only sufficient and provides no converse.

The source's semidirect-product Proposition1.9 additionally requires the quotient action K on P/H to be CCT. Knowing the sign-flip subgroup and abstract coordinate-permutation group are separately familiar does not establish that quotient-action hypothesis. Its product/wreath-product preservation results concern their specified product actions; the imprimitive action of the hyperoctahedral group on2n signed coordinate directions is different from its action on2^n cube vertices. Abstract group isomorphism cannot transfer CCT between these permutation representations.

The bounded immutable history screen (1,596 bound references, expanded aliases) found no target hit. A current arXiv phrase query for common-cover transitivity returned this source only. This is not complete citing coverage and does not clear all literature or the current public proof registries. Forbidden/parked registry routes were not reopened. Root must obtain independent adversarial review, adequate novelty qualification and its own acceptance gates before any credit. Counts remain9 additional/39 total/next40.
