# 342414: ordinary counterexample, zero accepted credit

This is an ordinary mathematical candidate, not a completed Lean solution. No claim of independent review, publication, worldwide novelty or campaign acceptance is made. The missing formal endpoint is material.

## Exact source scope

Pirot and Sereni, *Fractional chromatic number, maximum degree and girth*, arXiv:1904.05618v6, Definitions 1–2, Section 4.2.2, Conjecture 2. The same conjecture appears in the retrieved v1. Both PDFs and dated hash receipts are in sources/. The final journal is SIAM Journal on Discrete Mathematics 35(4), 2815–2843, DOI 10.1137/20M1382283; the publisher body was not independently retrieved.

An edge-rooted pattern of depth 2 has every vertex at distance at most 2 from the root edge. For d=3 its two root vertices have degree exactly 3; vertices in the other two layers have degree at most 3. The source constraint e_i is the expected number of layer-i vertices in a uniformly random maximum independent set. It is maximum, not maximal, and the distribution is uniform on all maxima.

The claim is that for every such pattern P of girth 6, some convex combination of tree constraints is weaker than P in the source's all-positive-weight implication sense. The construction below negates that claim, provided the ordinary tree-normalization argument is accepted. It does not refute the numerical Hall-ratio bound proved in the paper.

## The graph

Use root edge 01 and edges

    01, 02, 03, 15, 17, 34, 46, 56.

This is the six-cycle 0–1–5–6–4–3–0, with a pendant vertex 2 at 0 and a pendant vertex 7 at 1. Thus it is a connected simple graph of girth exactly 6. Its root degrees are 3 and every other degree is at most 2. The layers are

    L0={0,1}, L1={2,3,5,7}, L2={4,6}.

The exact maximum independent sets are

    [1, 2, 3, 6]
    [2, 3, 5, 7]
    [0, 4, 5, 7]
    [2, 4, 5, 7]
    [2, 3, 6, 7]

All have size 4; there are exactly five. The total layer occupancies over the five sets are (2,14,4), so

    e(P)=(2/5,14/5,4/5).

This is verified independently by direct enumeration of all 256 subsets in edgeverify.py, as well as the general deletion/component-splitting MIS recursion in edgepatterns.py. edge_graph_check.py independently verifies all cycles and the root-distance layers.

## All depth-2 cubic tree patterns

Let T be any acyclic edge-rooted cubic pattern of depth at most 2. Removing its central root edge gives two rooted halves. Each root has exactly two other neighbours, called branch vertices. Each branch vertex has 0, 1 or 2 children in layer 2. There can be no repeated vertex, extra edge or child shared between branches: any such configuration closes a cycle. No vertex lies farther away, by the depth condition. Consequently each half is specified, up to rooted isomorphism, by the unordered pair of its two leaf counts.

This establishes the six exhaustive half types

    A=(0,0), B=(0,1), C=(0,2), D=(1,1), E=(1,2), F=(2,2).

Including the shallower tree A+A only strengthens the bound below. This classification is an ordinary proof at present; its complete Lean graph-isomorphism bridge has NOT been implemented.

Put W(I)=7|I∩L1|+9|I∩L2|. For a half with leaf counts k1,k2, let n_j count branches with j leaves. If the half root is excluded, the maximum size is sum max(1,k_i); there are 2^n1 choices, with mean layer occupancies (n0+n1/2, n1/2+2n2). If the half root is included, its two branch vertices are excluded, every leaf is included, the size is 1+k1+k2, and there is one choice. Here the root itself contributes to size but has weight 0.

For each pair of halves, the root-edge constraint allows states (excluded,excluded), (included,excluded), and (excluded,included). Retain the states of largest total size. Their numbers of maxima multiply, their weighted totals add with those multiplicities, and uniform averaging over the retained states gives the following complete table of E[W]:

| | A | B | C | D | E | F |
|---|---|---|---|---|---|---|
| A | 28 | 27 | 71/2 | 32 | 41 | 50 |
| B | 27 | 27 | 36 | 33 | 42 | 51 |
| C | 71/2 | 36 | 136/3 | 43 | 52 | 61 |
| D | 32 | 33 | 43 | 34 | 130/3 | 262/5 |
| E | 41 | 42 | 52 | 130/3 | 53 | 187/3 |
| F | 50 | 51 | 61 | 262/5 | 187/3 | 72 |

Every entry is at least 27. This six-type calculation is separate from the direct enumeration of all 3^4=81 labelled leaf-count sequences in edgeverify.py. The entries can be reproduced without a floating solver by edge_table.py using Fraction arithmetic.

Therefore every T in the exact source tree family satisfies

    (7/27)e1(T)+(1/3)e2(T) >= 1.

## Strictly positive rational separation

Take alpha=(1/1000,7/27,1/3), so all three coordinates are strictly positive rationals. Since e0(T)>=0, the previous inequality shows alpha·e(T)>=1 for every tree T. Every real convex combination of such constraints also has alpha·sum(lambda_i e(T_i))>=1.

But for the displayed P,

    alpha·e(P)=134/135+1/2500=67027/67500<1.

This violates the required implication for every proposed convex combination, not merely for one LP solution. No conversion of a floating LP output into a proof is used: the weight vector and all verification inequalities are exact rational arithmetic.

## Source-own-results and significance gate

The source's optimal cubic r=2 vector is (1/2,13/44,3/44). Its value on this graph is 119/110>1. Thus the source's checked optimal bound and this counterexample are consistent. The false strengthening is simultaneous convex domination for all positive vectors. The counterexample is within r=2,d=3, rather than beyond that parameter range, because the authors report checking the optimum value there, not the full convex-combination conjecture. Beyond-range diagnostic searches at d=4 and d=5 also ran, but produced no additional obstruction; they are not separate candidate results.

The inspected source lemmas do not assert this separating inequality or exhibit this witness. Whether the finite obstruction is sufficiently significant, or is subsumed by an older general failure mechanism, requires root's independent assessment. It is human-posed source conjecture material, not an automatically generated degree-index inequality.

## Prior-art investigation and limits

Live /commits/HEAD receipts: OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae; Omega e26965e84ef74f66ce64631e23f293569195a4c1. Complete untruncated current Omega D5/Problems and OpenAI preprints path trees were retrieved. These are path screens, not exhaustive proof-body clearance. No exact edge-pattern/Pirot–Sereni path match was found.

OpenAlex title/full-text navigation and citation queries returned seven citing records. Actual bodies retrieved include the 2023 thesis tel-04259639, Hurley–Pirot arXiv:2109.15215, and Martinsson–Steiner's 2025 random-independent-set article. Inspected theorem/proof passages concern refined hard-core constraints, list colouring, or existence of other distributions; they do not provide a demonstrated bridge to the uniform-maximum edge-rooted-tree claim. The 2023 thesis Lemma 5 was inspected especially: its convex combination is for a different refined, vertex-rooted, two-stage distribution. It is not a proof of the reserved statement. These checks do not clear all cited papers, all thesis content, the final SIAM body, MathDB comments or unindexed/deleted registry history.

## Exact remaining formal work

1. Formalize finite simple rooted graphs, the source distance layers and maximum-independent-set averaging.
2. Prove the eight-vertex graph is a d=3,r=2 pattern with girth 6; certify its five maxima and exact occupancies.
3. Prove in Lean the universal rooted-isomorphism normal form for EVERY finite acyclic cubic depth-2 pattern; prove independent-set, layer and averaging invariance under that isomorphism.
4. Kernel-check the six-type root-state calculation or the equivalent 81 canonical actual graphs, and connect it to the preceding universal theorem. A theorem over 81 integer tuples alone is NOT the requested endpoint.
5. Prove linearity and separation for arbitrary finite real convex combinations, negating the literal conjecture.
6. Complete strict sanitized replay, leanchecker and transitive axiom audit on the pinned dependencies, then seek independent fidelity and significance review.

No Lean packet is supplied because none of those partial calculations is being substituted for the full source endpoint. Credit remains zero.
