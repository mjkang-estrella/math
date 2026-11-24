# An affine trade for even-by-odd flower-bouquet graphs

**Implementation status: COMPLETE.** The accompanying Lean 4.34.1 packet proves Conjecture 5.1 in its full range for the literal graph and local antimagic definitions. Both parameter-dependent assemblies, the final equality, and attainment of the minimum are proved. Every source module has been extracted afresh from the printed appendix, compiled, and kernel-checked through the pinned runner; the endpoint uses only propext, Classical.choice and Quot.sound. This is the implementation lane's own replay; an independent final review and prior-art refresh remain the campaign's next step. No publication or acceptance claim is made. See REPORT.md for exact statements and receipts.

## Literal source definitions and their Lean counterparts

Source: Gee-Choon Lau, Wai Chee Shiu, M. Nalliah, and K. Premalatha, *Construction of local antimagic 3-colorable graphs of fixed even size: Matrix approach*, Bulletin of the ICA **107** (2026), 68–89, received 3 May 2024 and accepted 24 April 2025. Journal URL: https://bica.the-ica.org/Volumes/107/Reprints/BICA2024-24-Reprint.pdf . Cached journal text: sources/flower-journal.txt. Quotes below transcribe mathematical notation from the printed text; P₃ means the path on three vertices.

The introduction, p. 68, says:

> “Let G = (V, E) be a connected graph of order n and size m. A bijection f : E → {1, 2, …, m} is called a local antimagic labeling if f⁺(u) ≠ f⁺(v) whenever uv ∈ E, where f⁺(u) = ∑_{e∈E(u)} f(e) and E(u) is the set of edges incident with u.”

The Lean counterpart is `vsum G f v := ∑ e ∈ univ.filter (fun e => v ∈ (e : Sym2 V)), ((f e : ℕ) + 1)` and `IsLocalAntimagic G f := ∀ u v, G.Adj u v → vsum G f u ≠ vsum G f v`, with `f : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)`. The extra one exactly produces the source labels 1 through m.

The same paragraph defines:

> “The local antimagic chromatic number χla(G) is defined to be the minimum number of colors taken over all colorings of G induced by local antimagic labelings of G”.

The source immediately extends its discussion on p. 69: “Thus, local antimagic chromatic number is well defined for all graphs without a K₂ component.” Its theorems explicitly apply the same definition to disconnected graphs. The Lean definition below is accordingly defined for every finite simple graph, including the disjoint union in the conjecture.

Lean uses `colorCount G f := (univ.image (vsum G f)).card` and `chiLA G := sInf {c | ∃ f, IsLocalAntimagic G f ∧ colorCount G f = c}`. Existence is required in the upper bound; the minimum argument explicitly uses a nonempty feasible set. On an empty set the natural-number infimum is zero, so this definition cannot make the target three vacuous.

On p. 69 the source says:

> “Let G + H and mG denote the disjoint union of graphs G and H, and m copies of G, respectively.”

On p. 70 it says:

> “The join graph of the graphs G and H is denoted by G ∨ H. We denote nP₃ ∨ K₁ by FB(n), the fan graph with n blades.”

And in the proof of Theorem 2.1:

> “Let the vertex set and edge set of the i-th copy of FB(1) be {uᵢ, vᵢ, wᵢ, xᵢ} and {uᵢwᵢ, vᵢwᵢ, xᵢwᵢ, xᵢuᵢ, xᵢvᵢ}, respectively”.

The Lean graph has vertices `Fin r × Option (Fin s × Fin 3)`; `none` is x and roles 0,1,2 are u,w,v. `FBAdj` joins x to each peripheral vertex, and connects u–w and w–v inside the same blade. `rFB.Adj` additionally requires equal component indices. There are no other edges. `edgeEquiv` proves that the indexed five-edge type is exactly the actual SimpleGraph edge set, and `vsum_transfer` proves equality of full incident sums, not just equality of cardinalities.

Conjecture 5.1, p. 87, reads verbatim (typeset subscripts normalized):

> “For even r ≥ 2 and odd s ≥ 3, we expect χla(rFB(s)) = 3.”

The required Lean statement is:

```lean
theorem conj_5_1 (r s : ℕ) (hr : 2 ≤ r) (hre : Even r)
    (hs : 3 ≤ s) (hso : Odd s) : chiLA (rFB r s) = 3
```

This endpoint, both component-grouping assemblies, and attainment on the actual edge set have been proved in Lean and passed the fresh extracted kernel replay. The written argument follows; exact statements and verification receipts are recorded in REPORT.md.

## 1. Blade arithmetic

Represent a blade by the ordered five-tuple (a,b,c,d,e) on the explicit edge order (xu, uw, xw, wv, vx). This is a reordering of the source’s edge-set listing; w is the middle vertex of the path u–w–v. Its endpoint weights are a+b and d+e; its middle weight is b+c+d; its contribution to the hub is a+c+e.

Put rs=2k and set

A=10k+1, B=13k+1, J=17k-1.

An **ordinary** blade satisfies a+b=d+e=A and b+c+d=B. A **flipped** blade satisfies a+b=d+e=B and b+c+d=A. A blade with center label c and role ε∈{0,1} contributes

    7k+1+9kε+2c                                      (1)

to its hub. Consequently a set of t blades, with f flipped blades and center sum C, has total hub contribution

    t(7k+1)+9kf+2C.                                  (2)

Any two ordinary blades whose center labels sum to 10k-2 have total hub contribution 2J. An ordinary blade with center 5k-1 has contribution J.

## 2. The original ordinary blade supply

For k≥11 the following 2k ordinary blades use every label in {1,...,10k} exactly once. These are the source's five-row array, written in the present edge order:

| Index i | (a,b,c,d,e) |
|---|---|
|1|(10k,1,7k,6k,4k+1)|
|2≤i≤k|(9k+2-i,k+i-1,6k+3-2i,6k+i-1,4k+2-i)|
|k+1≤i≤2k-1|(11k-i,i-k+1,8k-2i,6k+i,4k+1-i)|
|2k|(8k+1,2k,3k+1,8k,2k+1)|

For completeness, the a-labels are [8k+1,10k], the b-labels are [1,2k], the d-labels are [6k,8k] with 7k omitted, and the e-labels are [2k+1,4k+1] with 3k+1 omitted. The c-labels are [4k+2,6k-1] together with 3k+1 and 7k: the two internal index ranges give its two parity classes. These five sets partition [1,10k], with no repetition in a row. Direct addition verifies the three ordinary-blade equations. In particular the center identifies each blade uniquely.

Remove the following 21 columns:

    1,...,7; k-3,...,k; k+1,...,k+5; 2k-4,...,2k.     (3)

They are distinct for k≥11. Their centers are the two outliers 3k+1,7k, the bottom eight values [4k+2,4k+9] and the top eleven values [6k-11,6k-1] of the old interval. Thus the remaining ordinary blades have center labels exactly

    I_k=[4k+10,6k-12],                               (4)

an odd-length interval of 2k-21 integers with midpoint 5k-1.

## 3. A 21-blade affine trade

Replace the 21 removed blades by the 21 blades in Table 1 below, keeping the seven displayed groups of three. The first two blades in group 0 are flipped; all other blades are ordinary.

Three finite affine identities establish everything needed about this replacement:

1. Its 105 edge labels, as affine polynomials in k, are exactly the 105 edge labels in the removed columns (3), with the same multiplicities.
2. Each row has the stated role's endpoint and middle weights.
3. The center sum of group 0 is 6k-3; the center sum of each other group is 15k-3.

Each identity follows by substituting Table 1 and collecting the coefficient of k and the constant term. For (1), compare the 105 ordered pairs (coefficient,constant) against the five-row supply at the explicit indices (3). This is an equality of finite multisets of affine expressions, so it applies to every k, not merely to sampled k. The table is included in full; the accompanying Lean modules check the coefficient-pair permutation, the explicit edge reindexing, and their evaluations at every k ≥ 11.

The removed labels were positive, distinct and at most 10k. Identity (1) therefore proves those properties for the replacement as well. Equation (2) and identity (3) show that **every one of the seven groups has hub contribution 3J**. For group 0 this is

    3(7k+1)+18k+2(6k-3)=51k-3=3J;

for each other group it is 3(7k+1)+2(15k-3)=3J.

The result is a supply of seven three-blade blocks, each with contribution 3J, and 2k-21 remaining ordinary blades with centers (4). The edge labels of these objects form a partition of [1,10k].

## 4. Equal-sum partition of an odd interval

We need only the following elementary row-partition fact, not a magic-rectangle theorem.

**Lemma.** If h≥1 and s≥3 are odd, any interval of hs consecutive integers can be partitioned into h sets of size s, all with the same sum, namely s times the interval's midpoint.

**Proof.** First partition [1,3h] into equal-sum triples. Write h=2t+1. For i=0,...,h-1 put

    a_i=i+1,
    b_i=h+1+((i+t) mod h),
    c_i=(9h+3)/2-a_i-b_i.

The a_i enumerate [1,h], and the b_i enumerate [h+1,2h]. For i=0,...,t, the values i+((i+t) mod h)=2i+t enumerate t,t+2,...,3t. For i=t+1,...,2t they enumerate t+1,t+3,...,3t-1. Together these are the consecutive values [t,3t]. Hence the c_i enumerate [2h+1,3h]. Every triple has sum (9h+3)/2.

Write s=2u+3. For [1,hs], shift these triples by uh, placing them in the middle 3h integers. Pair each x∈[1,uh] with hs+1-x, and give u such pairs to each triple, using all pairs once. Each resulting set has s elements and sum

    3uh+(9h+3)/2+u(hs+1)=s(hs+1)/2.

Translation gives any interval. This construction includes h=1 and u=0. ∎

## 5. All even r≥8

Here k=rs/2≥12, so §3 applies. From the two ends of I_k remove 7(s-3)/2 complementary pairs, each of sum 10k-2. Give (s-3)/2 pairs to each of the seven three-blade blocks. Each block now has s blades and hub contribution 3J+(s-3)J=sJ.

The central interval that remains has length

    (2k-21)-7(s-3)=(r-7)s.

This is positive, and its midpoint is still 5k-1. Both r-7 and s are odd. The lemma partitions its centers into r-7 groups of s centers with sum s(5k-1). Using the corresponding ordinary blades gives r-7 additional components. By (2), each has hub contribution s(7k+1)+2s(5k-1)=sJ.

We have exactly r groups of s blades, and each group is one FB(s). Each peripheral vertex has weight A or B, and every hub has weight sJ. The label partition already proved gives a bijection onto [1,10k]=[1,5rs]. Since k≥12 and s≥3, sJ>B>A; each blade's endpoints and middle have opposite peripheral colors. This is a local antimagic three-coloring.

## 6. Small r with large odd s

For r=2,4,6, remove the median-center blade from I_k. It is an eighth block, consisting of one ordinary blade with hub contribution J. The other seven blocks have sizes 3 and contribution 3J. Their sizes are therefore (3,3,3,3,3,3,3,1), totaling 22, and each block's contribution is its size times J.

Merge these eight blocks into r groups with sizes as follows:

|r|Merged sizes|Condition on odd s|
|---|---|---|
|2|9,13|s≥13|
|4|3,3,9,7|s≥9|
|6|3,3,3,3,3,7|s≥7|

Explicitly, numbering the size-3 blocks 0,...,6 and the singleton 7, use index groups {0,1,2},{3,4,5,6,7}; or {0},{1},{2,3,4},{5,6,7}; or {0},{1},{2},{3},{4},{5,6,7}, respectively.

The remaining centers occur in complementary pairs about 5k-1. For every merged group of size d, give it (s-d)/2 of these pairs. These are nonnegative integers. Exactly all pairs are used, because their required total is (rs-22)/2, the number of remaining pairs. Every group now has s blades and contribution sJ. The relevant minima k are 13,18,21, respectively, so the supply and trade are valid. As in §5, the three colors A,B,sJ give a bijective local antimagic labeling.

## 7. Ten remaining cases and conclusion

The cases outside §§5–6 are exactly

    (2,3),(2,5),(2,7),(2,9),(2,11),
    (4,3),(4,5),(4,7),(6,3),(6,5).

Table 2 below supplies complete finite labelings for all ten, with the same edge order as §1. Within each case every integer from 1 to 5rs occurs exactly once. Add the two endpoint sums and the middle sum of each blade, and add a+c+e over each component: the colors are exactly the three values shown in the table. The checker reconstructs all vertices and edges, verifies bijectivity, all vertex weights, and every adjacent inequality directly; it does not assume a role pattern. These finite equalities are a certificate, not an appeal to a solver's feasibility status.

Together the parameter constructions and ten certificates cover every even r≥2 and odd s≥3. Each gives a local antimagic labeling with exactly three colors. The triangle lower bound gives χ_la(rFB(s))≥3, completing χ_la(rFB(s))=3. ∎

## Prior-art qualification and significance

The supplied independent review (Claude Opus 5.5, 20 November 2026) read the journal source and checked the public registry, source versions, author publications, later arXiv papers, and campaign duplicates. It found no public solution in that bounded investigation. Its prior-art conclusion is qualified by `CCO2025_BODY_UNREAD`: Chan–Lau–Shiu, *Complete solutions on local antimagic chromatic number of three families of disconnected graphs*, Commun. Comb. Optim. 10(4) (2025), 973–988, DOI 10.22049/cco.2024.29032.1818, was unavailable in full text. The journal abstract as returned in two independent snippets covers disjoint unions of two stars, paths, and 2-regular graphs with at most one odd-order component. Those families have different degree structure from rFB(s), and the 2026 source still poses this conjecture. The unread body remains a bibliographic limit. No live prior-art refresh was performed by this implementation lane.

The review judged the mathematics correct and provisionally tier-1, pending a literal Lean endpoint, with a borderline nonroutine probability of 0.65. The construction uses a standard general pattern—finite trade, complementary pairs, equal-sum grouping—but its specific two-flip 21-blade affine trade is not supplied by any checked published theorem. The 21-blade gadget was found by a computer search using role-aware exact cover and MILP; the search discovers the table, while the proof verifies its explicit affine identities. The trade changes roles to evade the parity obstruction of the source's single-role matrix grouping. After the trade is supplied, most remaining work is elementary arithmetic. This is a moderate explicit combinatorial construction, not a claim of a deep new graph-theoretic method. The finite exceptional witnesses alone are not a resolution of the conjecture.

## Tables certifying the written construction

## Table 1: the affine replacement

The table entries use (a,b,c,d,e). Group 0 has role pattern (flipped,flipped,ordinary); every other row is ordinary.

|Group|Blade (a,b,c,d,e)|
|---|---|
|0|(10k-1, 3k+2, k-3, 6k+2, 7k-1)|
|0|(9k-1, 4k+2, 2k-4, 4k+3, 9k-2)|
|0|(9k+1, k, 3k+4, 9k-3, k+4)|
|1|(3k-3, 7k+4, 4k-1, 2k-2, 8k+3)|
|1|(3k, 7k+1, 4k+1, 2k-1, 8k+2)|
|1|(10k-2, 3, 7k-3, 6k+1, 4k)|
|2|(2k+2, 8k-1, 3k-2, 2k+4, 8k-3)|
|2|(6k-5, 4k+6, 6k-1, 3k-4, 7k+5)|
|2|(4k+5, 6k-4, 6k, k+5, 9k-4)|
|3|(9k+2, k-1, 2k+5, 10k-3, 4)|
|3|(6k-6, 4k+7, 6k-11, 3k+5, 7k-4)|
|3|(8k, 2k+1, 7k+3, 4k-3, 6k+4)|
|4|(8k-2, 2k+3, k+3, 10k-5, 6)|
|4|(3k-1, 7k+2, 6k-2, 1, 10k)|
|4|(6k-3, 4k+4, 8k-4, k+1, 9k)|
|5|(4k-5, 6k+6, k+2, 6k-7, 4k+8)|
|5|(9k-5, k+6, 6k-10, 6k+5, 4k-4)|
|5|(9k+3, k-2, 8k+5, 4k-2, 6k+3)|
|6|(5, 10k-4, 2, 3k+3, 7k-2)|
|6|(7k, 3k+1, 6k-9, 4k+9, 6k-8)|
|6|(8k+1, 2k, 9k+4, 2k-3, 8k+4)|

## Table 2: all exceptional finite labelings

Each component row below is a list of blade tuples; the colors apply to the entire case.

### (r,s)=(2,3), colors [30, 31, 191]

Component 0: (29,2,27,1,30), (17,14,13,3,28), (18,12,9,10,20).

Component 1: (22,8,16,7,23), (19,11,15,5,25), (24,6,21,4,26).

### (r,s)=(2,5), colors [50, 51, 518]

Component 0: (49,2,47,1,50), (34,16,25,10,40), (31,19,14,18,32), (33,17,21,13,37), (38,12,28,11,39).

Component 1: (46,5,42,3,48), (36,15,29,6,45), (26,24,4,23,27), (43,8,35,7,44), (30,20,22,9,41).

### (r,s)=(2,7), colors [70, 71, 1005]

Component 0: (69,2,67,1,70), (66,5,62,3,68), (64,7,57,6,65), (36,35,4,31,40), (43,27,30,14,56), (38,32,10,29,41), (44,26,25,20,50).

Component 1: (60,11,51,8,63), (58,13,45,12,59), (47,23,39,9,61), (48,22,34,15,55), (52,18,37,16,54), (42,28,19,24,46), (49,21,33,17,53).

### (r,s)=(2,9), colors [91, 118, 1368]

Component 0: (60,31,82,5,86), (51,40,62,16,75), (32,59,56,3,88), (30,61,8,49,42), (22,69,36,13,78), (15,76,38,4,87), (10,81,23,14,77), (65,53,9,29,89), (63,55,1,35,83).

Component 1: (74,17,90,11,80), (54,37,57,24,67), (50,41,58,19,72), (48,43,68,7,84), (44,47,26,45,46), (27,64,2,52,39), (25,66,34,18,73), (21,70,28,20,71), (12,79,33,6,85).

### (r,s)=(2,11), colors [111, 144, 2046]

Component 0: (109,35,8,68,76), (98,46,18,47,97), (100,11,37,96,15), (33,78,45,21,90), (108,3,74,67,44), (24,87,31,26,85), (101,10,27,107,4), (86,25,14,105,6), (32,79,64,1,110), (63,48,84,12,99), (102,9,93,42,69).

Component 1: (30,81,43,20,91), (61,50,65,29,82), (49,62,66,16,95), (60,51,55,38,73), (88,23,80,41,70), (39,72,13,59,52), (94,17,56,71,40), (5,106,2,36,75), (77,34,57,53,58), (89,22,103,19,92), (104,7,54,83,28).

### (r,s)=(4,3), colors [61, 79, 303]

Component 0: (11,50,28,1,60), (42,37,3,21,58), (40,39,2,20,59).

Component 1: (47,14,52,13,48), (29,32,16,31,30), (6,55,19,5,56).

Component 2: (34,27,45,7,54), (25,36,33,10,51), (17,44,9,26,35).

Component 3: (38,23,41,15,46), (18,43,24,12,49), (8,53,22,4,57).

### (r,s)=(4,5), colors [101, 131, 845]

Component 0: (82,19,97,15,86), (50,51,44,36,65), (26,75,8,48,53), (73,58,4,39,92), (70,61,2,38,93).

Component 1: (66,35,62,34,67), (56,45,57,29,72), (32,69,52,10,91), (22,79,46,6,95), (18,83,28,20,81).

Component 2: (76,25,99,7,94), (42,59,55,17,84), (30,71,33,27,74), (24,77,49,5,96), (16,85,9,37,64).

Component 3: (54,47,63,21,80), (41,60,68,3,98), (23,78,40,13,88), (14,87,43,1,100), (12,89,31,11,90).

### (r,s)=(4,7), colors [141, 183, 1659]

Component 0: (139,44,11,86,97), (125,58,24,59,124), (127,14,46,123,18), (42,99,57,27,114), (61,80,84,19,122), (119,22,69,92,49), (131,10,66,107,34).

Component 1: (79,62,83,38,103), (128,13,33,137,4), (41,100,82,1,140), (98,43,75,65,76), (134,7,72,104,37), (133,8,70,105,36), (132,9,68,106,35).

Component 2: (138,3,95,85,56), (112,29,101,53,88), (110,31,17,135,6), (5,136,2,45,96), (113,28,130,25,116), (120,21,71,91,50), (118,23,67,93,48).

Component 3: (39,102,55,26,115), (30,111,40,32,109), (78,63,73,47,94), (81,60,108,15,126), (51,90,16,77,64), (121,20,74,89,52), (129,12,117,54,87).

### (r,s)=(6,3), colors [91, 118, 456]

Component 0: (27,64,48,6,85), (71,47,2,42,76), (56,62,1,28,90).

Component 1: (51,40,68,10,81), (38,53,29,36,55), (17,74,35,9,82).

Component 2: (46,45,65,8,83), (32,59,52,7,84), (19,72,15,31,60).

Component 3: (50,41,63,14,77), (37,54,43,21,70), (3,88,26,4,87).

Component 4: (34,57,39,22,69), (33,58,49,11,80), (30,61,44,13,78).

Component 5: (67,24,89,5,86), (18,73,20,25,66), (12,79,23,16,75).

### (r,s)=(6,5), colors [151, 196, 1270]

Component 0: (87,64,126,6,145), (56,95,89,12,139), (44,107,13,76,75), (113,83,3,65,131), (111,85,4,62,134).

Component 1: (120,31,146,19,132), (92,59,127,10,141), (42,109,60,27,124), (18,133,20,43,108), (8,143,17,36,115).

Component 2: (97,54,103,39,112), (82,69,98,29,122), (67,84,66,46,105), (63,88,78,30,121), (41,110,25,61,90).

Component 3: (104,47,148,1,150), (55,96,93,7,144), (52,99,86,11,140), (14,137,38,21,130), (9,142,5,49,102).

Component 4: (118,33,147,16,135), (57,94,68,34,117), (51,100,24,72,79), (50,101,73,22,129), (15,136,58,2,149).

Component 5: (119,32,138,26,125), (81,70,91,35,116), (74,77,48,71,80), (45,106,53,37,114), (23,128,40,28,123).


## Formal implementation correspondence

The appendix is authoritative for the formal statements. `RFBGraph` and `RFBLabeling` prove the source-to-Lean graph and label bridges. `RFBSupply` proves the source matrix label partition and sums for all k ≥ 11. `RFBAffine`, `RFBTrade`, and the removed-column modules prove Table 1 coefficientwise and evaluate it uniformly. `RFBPool`, `RFBPoolEval`, and `RFBPoolProperties` implement the trade as a permutation of the true source labels; any bijective blade reindexing retains a certified graph labelling. `RFBCentres` enumerates the remaining centres bijectively. `RFBTriples`, `RFBPadding`, and `RFBPartition` prove the complete translated odd-interval partition. `RFBExceptions` collects the ten literal finite equalities.

The parameter-dependent grouping is implemented in `RFBCanonical`, `RFBSandwich`, `RFBSandwichSums`, `RFBLargeOrder`, `RFBLargeAssembly`, `RFBSmallPool`, `RFBSmallGrouping`, and the three `RFBPlan` modules. The large construction preserves the seven padded triples and applies the proved odd-interval partition to all remaining rows. The small construction allocates every seed and every complementary pair bijectively, then proves every row has size s and hub sum sJ. `RFBConjecture.small_r_assembly` and `large_assembly` discharge both hypotheses of the earlier closure helper; `RFBConjecture.conj_5_1` has only the source's four numerical hypotheses. `conj_5_1_attained` additionally gives a bijection on the actual graph edge set realizing three colours. Together with `triangle_lower`, this proves that the natural-number infimum is an attained minimum of exactly three, without any residual graph, grouping, or existence premise.
