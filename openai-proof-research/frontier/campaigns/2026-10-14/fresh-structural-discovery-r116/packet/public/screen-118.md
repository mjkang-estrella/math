# Source 118: finite resource contractions, before any freeze

No theorem target was frozen. These are feasibility calculations and a narrowly scoped obstruction. The source is *Additive hardness and unbounded configuration gaps in bin packing*, at the pinned revision. Operative labels are `thm:reduction`, `lem:competing-trees`, `lem:geometry`, `lem:encoding`, `lem:good-feasibility`, `prop:completeness`, `prop:fractional`, and `thm:unbounded-gap`. Its original construction has five roles X,A,U,D,F and exactly B copies of each. Its input graph and tolerance parameters are retained in all calculations below.

## Strongest compatible existing route

The source's four permitted subclass tuples are

| Row | Anchor | Global | Local | Flag |
|---|---|---|---|---|
| T+ | Z | U+ | DM | FT |
| T- | Z | U- | DM | FT |
| S | Z | U+ | DM | FM |
| S | Y | W | DG | FG |

The source completeness proof puts the d length-one global auxiliaries at each funded vertex on root rows, with length-zero local auxiliaries. All S rows in M use length-zero U+. Thus the following U/F joint stock does not depend on which k vertices are selected:

| Composite species | Multiplicity |
|---|---:|
| (U+ of length 1, FT) | dk |
| (U+ of length 0, FT) | sum_v t_(v,+) - dk |
| (U+ of length 0, FM) | sum_v J_v |
| (U- of length 1, FT) | d(n-k) |
| (U- of length 0, FT) | sum_v t_(v,-) - d(n-k) |
| (permit of edge e, FG) | dR for each e |
| (nonpermit of edge e, FG) | dR for each e |

Every multiplicity is nonnegative, including k=0,n, since each tree has d root rows at every vertex. The source's K4, k=2 fractional witness is formed from equal-weight selected/unselected local templates. The joint stock in that witness also balances: positive U's remain on tree rows and all W's remain with FG. This is the compatibility calculation that must precede invoking a gluing analogy. The source already provides distinct-copy assignment and fractional distribution over the global pools; no independently discovered correlation theorem is needed here. The r51 body also already uses deterministic local templates and physical resource pools for its separate hierarchy question.

Rothvoss, [arXiv:1301.4010v1, Section 4.2, Lemma 8 and Corollary 9](https://arxiv.org/pdf/1301.4010v1), gives a concrete gluing/decompression operation with stock divisibility, repeated types, and rational column denominators. It is not, by itself, a theorem permitting arbitrary heterogeneous U/F pairings. The preceding explicit stock calculation resolves that interface for this particular route. Jansen–Pirotton–Tutas, [full version arXiv:2512.02758v1, Section 3, Lemma 5](https://arxiv.org/pdf/2512.02758v1), proves bounded integer-equation aggregation with added slack and a radix domination argument. It does not supply a new packing-gap decoder. Source 118 already spells out the relevant bounded aggregation and score-defect operation, and explicitly cites that classical lineage.

## Rebasing and arbitrary-packings feasibility calculation

Write an old size as 1/5 + gamma p + mu q + nu w, and write its perturbation as e. Replace a retained X,A,D item by 1/4+e, and each paired U/F item by 1/4+e_U+e_F. There are 4B physical items. The source bounds imply all these sizes exceed 1/5, so every feasible bin has at most four items. The perturbations in a bin represent at most eight old constituent items, not merely five; this distinction is needed when applying the radix equations.

Every coefficient total in the ten primary equations has absolute value below 100 for eight constituents. Thus a zero radix score forces all ten equations. Their role equations force equal constituent counts in all five old roles. Since U and F occur only in pairs and the other three roles are singletons, four physical items then force exactly one constituent of each old role. The four source subclass patterns follow. The lower-scale terms on at most eight constituents are smaller than one primary-score unit, so a feasible full bin cannot have positive primary total. On a zero-primary full bin, the new and old sums agree: the new four baselines and the old five baselines both total one. Decompression of such a bin is therefore feasible without any label restriction. This last point preserves the source's treatment of mismatched labels rather than silently demanding good tuples.

For a provisional extra-bin allowance c, at most 4c bins of a packing into at most B+c bins are nonfull. A loose bound is 16c items in those bins. Let P0=100^11, as in the source; every new item's primary score has absolute value below 2P0 and total inventory score is zero. The number of full bins with negative primary score is consequently at most 32cP0. At most 16c(1+8P0) new items lie outside zero-primary full bins. Decompress these exceptional items to at most twice as many old singleton items and retain all other decompressed bins. This gives the conservative old-bin allowance

    c0 = c(33 + 256 P0).

The source tolerance would be chosen to be c0 at the outset. P0 is fixed independently of c0; the other source constants may depend on c0 and rho, exactly as permitted by `thm:reduction`. There is no circular constant choice. Rational bit complexity and the fixed-parameter interpretation remain those of the source. A fractional construction would use the preceding joint pools and the source's copy allocation; a uniform dual weight 1/4 uses the new four-item capacity bound.

These calculations explain why this route does not leave an identified unpaid operation after the actual source proof is checked. They are not a frozen four-item theorem submission or a contribution verdict. A stronger numerical/item-threshold conclusion alone would not satisfy the assignment. No claim is made that a primary paper states this exact rebasing verbatim.

## A further fixed pairing fails

Consider only the following proposed contraction. At a fixed vertex label v, pair every Z deadline z with a DM length ell, using the same physical pairs in both the selected and unselected source local states. Preserve the source row sets, their M/G allocation, and their funded-root global-auxiliary choices. This is a restricted question about the source's two templates, not arbitrary three-item constructions.

After moving the local length to the anchor, the available deadlines are z+ell. For a feasible bijection of M rows to these deadlines, the prefix counts must satisfy

    #{z+ell <= a} <= #{r <= a},

where r is a row's completion after its global auxiliary and short-row shift, but before any local auxiliary. This inequality follows directly: every deadline at most a must be matched to a row at most a.

Let B_v(a) be the source baseline prefix count. At a point a in a plus leaf test, in the unselected state the plus roots are unfunded. Funded minus roots move from 5 to 4, entirely to the right of a; job shifts occur beyond the plus tree's first tenth. Hence #{r<=a}=B_v(a). At a point in a minus leaf test, use the selected state instead: the plus-root and job shifts occur entirely to its left, and the minus tree is unfunded, so the same equality holds. The stipulated `eq:deadline-prefix` gives #{z<=a}=B_v(a)+d on each such leaf test.

Because ell>=0,

    #{z+ell<=a} = #{z<=a} - #{z<=a<z+ell}.

The fixed collection of intervals [z,z+ell) must therefore cover every leaf test in both trees at least d times. Zero lengths contribute nothing. There are only p_ell positive intervals of length lambda_ell at each depth ell. By `lem:geometry`, each such interval can meet at most one depth-ell cell, and any leaf it meets descends from that cell. Mark that cell, with multiplicity, if the interval meets a leaf. Choosing one interior point in each leaf test shows that every root-to-leaf path in each tree gets at least d marks. The total marks at depth ell, across both trees, are at most p_ell. Now discard repetitions: the resulting sets still hit every path at least once and satisfy the same quotas. This contradicts `lem:competing-trees`, whose combined-quota conclusion forbids even a shared one-hit marking. No assertion that deduplication preserves d distinct hits is needed.

Thus this fixed anchor/local pairing cannot support both source local states. The argument allows arbitrary rematching of rows to those fixed extended deadlines, so it is stronger than failure of one sorting choice. It does not address state-dependent pair stocks, other grouping schemes, altered gadgets, mixed labels, or new fractional witnesses. It does not refute a full three-item gap statement. The missing work is a different simultaneous resource mechanism preserving both the fractional inventory and arbitrary-packing soundness; merely letting the pairing depend on the state changes the physical instance.

## Priority and scope limits

The closest primary rounding lower bound inspected was Eisenbrand–Pálvölgyi–Rothvoss, [arXiv:1007.2170v2, Theorems 1–2 and Section 6 opening](https://arxiv.org/pdf/1007.2170v2). Its support-constrained rounding lower bound must not be read as the same full configuration-LP gap statement. Version 3 returned HTTP 404; version 2 was successfully read. That proof was not read completely. The support lower-bound section of Jansen–Pirotton–Tutas was likewise not read completely. There is no asserted global priority clearance. No limited repair is nominated.
