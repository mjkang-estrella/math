# A counterexample to Conjecture 3 (full mathematical endpoint)

Source: Bille–Buchstaber–Spodarev, *Some open mathematical problems on fullerenes*, arXiv:2410.19322v1, 25 October 2024, Definition 5 and Conjecture 3, PDF p13; degree convention and graph class, Section 2 pp2–3. The current arXiv record retrieved 30 October 2026 lists v1 only. Source PDF SHA256: 244ea62bb54ea6ac818a924f16c5729629dc0d36c6e756e57da110ef4105eb64.

The quantified claim is: for each alpha,beta in (0,1), and each pair of dual fullerenes of feasible original orders, equality of tr exp(alpha A+beta D) implies isomorphism (and conversely). It is not the weaker claim that equality as a function of both parameters implies isomorphism. We refute the printed pointwise claim.

## Explicit graphs

Let G,H be the simple undirected graphs on {0,...,31} specified by the following neighbor table. Adjacency is symmetric; each edge is included once in the JSON edge lists. These exact graphs, not a graph-generator enumeration claim, are the witness.

| Vertex | G neighbors | H neighbors |
| --- | --- | --- |
| 0 | 1,12,13,14,15,16 | 1,12,13,14,15,16 |
| 1 | 0,12,16,17,18,19 | 0,12,16,17,18,19 |
| 2 | 3,17,18,20,21,22 | 3,17,18,20,21,22 |
| 3 | 2,20,21,23,24,25 | 2,20,21,23,24,25 |
| 4 | 23,24,26,27,28 | 23,24,26,27,28 |
| 5 | 6,15,16,19,26,27 | 15,16,19,26,27 |
| 6 | 5,17,19,20,23,26 | 17,19,20,23,26 |
| 7 | 13,14,29,30,31 | 13,14,29,30,31 |
| 8 | 12,13,18,22,29 | 12,13,18,22,29 |
| 9 | 21,22,25,29,30 | 21,22,25,29,30 |
| 10 | 24,25,28,30,31 | 24,25,28,30,31 |
| 11 | 14,15,27,28,31 | 14,15,27,28,31 |
| 12 | 0,1,8,13,18 | 0,1,8,13,18 |
| 13 | 0,7,8,12,14,29 | 0,7,8,12,14,29 |
| 14 | 0,7,11,13,15,31 | 0,7,11,13,15,31 |
| 15 | 0,5,11,14,16,27 | 0,5,11,14,16,27 |
| 16 | 0,1,5,15,19 | 0,1,5,15,19 |
| 17 | 1,2,6,18,19,20 | 1,2,6,18,19,20 |
| 18 | 1,2,8,12,17,22 | 1,2,8,12,17,22 |
| 19 | 1,5,6,16,17 | 1,5,6,16,17,26 |
| 20 | 2,3,6,17,23 | 2,3,6,17,23 |
| 21 | 2,3,9,22,25 | 2,3,9,22,25 |
| 22 | 2,8,9,18,21,29 | 2,8,9,18,21,29 |
| 23 | 3,4,6,20,24,26 | 3,4,6,20,24,26 |
| 24 | 3,4,10,23,25,28 | 3,4,10,23,25,28 |
| 25 | 3,9,10,21,24,30 | 3,9,10,21,24,30 |
| 26 | 4,5,6,23,27 | 4,5,6,19,23,27 |
| 27 | 4,5,11,15,26,28 | 4,5,11,15,26,28 |
| 28 | 4,10,11,24,27,31 | 4,10,11,24,27,31 |
| 29 | 7,8,9,13,22,30 | 7,8,9,13,22,30 |
| 30 | 7,9,10,25,29,31 | 7,9,10,25,29,31 |
| 31 | 7,10,11,14,28,30 | 7,10,11,14,28,30 |

Each has 32 vertices, 90 edges, 12 vertices of degree 5 and 20 of degree 6. `graph-certificates.json` supplies rotation systems and 60 triangular faces. Their dart-face permutation has only 3-cycles and Euler characteristic 32−90+60=2. Connected orientable cellular embeddings with Euler characteristic 2 are sphere embeddings. The independent checker verifies connectivity after deletion of every pair of vertices in both graphs and both dual graphs. The duals are simple 3-connected cubic planar graphs with 60 vertices and 32 faces: 12 pentagons and 20 hexagons. By Steinitz, each is the graph of a convex polytope of the source class. Thus G,H really are dual fullerenes of feasible order n=60; n is not their dual order 32. No IPR premise is present in Conjecture 3.

## Exact heat-trace bounds

For graph X put M_X(alpha,beta)=alpha A_X+beta D_X with D_X(v,v)=deg_X(v). Define f(beta)=tr exp(M_G(9/10,beta))−tr exp(M_H(9/10,beta)). All matrices at the two endpoints beta=1/50,9/10 have nonnegative entries and maximum row sum R=6(alpha+beta). For K=90 define

S_X=sum_{k=0}^90 tr(M_X^k)/k!,  E=32 * 3^ceil(R) * R^91/91!.

Entrywise positivity gives S_X <= tr exp(M_X) <= S_X+E. Indeed tr(M_X^k) <= 32 R^k by the induced infinity norm, and

sum_{k=91}^infinity R^k/k! <= (R^91/91!) exp(R) < (R^91/91!) 3^ceil(R),

since (91+j)!>=91!j! and exp(1)<3. Hence the exact rational interval for f is [S_G−S_H−E,S_G−S_H+E]. All arithmetic in these inequalities is rational. `exact-signs.json` stores the full rational endpoints; `independent_check.py` reproduces them using standard-library integers/Fraction and sparse matrix multiplication, without NumPy or NetworkX.

At beta=1/50 the integer matrix is 45A+D divided by 50; at beta=9/10 it is 9A+9D divided by 10. The independently checked exact rational comparisons are

1/1000 < f(1/50) < 1/500,

−2 < f(9/10) < −1.

The decimal indications 0.00151005689 and −1.66314024 are dispensable: the inequalities above follow by integer cross multiplication of the stored rational endpoints. No float sign or numerical near-equality is used in the proof.

## Nonisomorphism and an interior zero

For B_G=45A_G+D_G, B_H=45A_H+D_H, exact integer multiplication gives

tr(B_G^6)=540051518791920,

tr(B_H^6)=540051567999420.

An isomorphism simultaneously conjugates A and D by a permutation matrix and preserves every pencil moment. These distinct integers prove G and H are nonisomorphic, independently of a graph-isomorphism algorithm.

The matrix exponential is analytic in its entries, so f is continuous on [1/50,9/10]. Its rigorously opposite endpoint signs imply an interior beta_* in (1/50,9/10) with f(beta_*)=0. Thus alpha=9/10 and beta_* both lie strictly in (0,1), and two nonisomorphic source-class dual fullerenes have equal character at that same pair. This refutes the complete universal Conjecture 3. Existence of beta_* is exact; a closed form or floating approximation is unnecessary.

## Scope, alternative mechanism and novelty limits

This is a full mathematical refutation of the printed source endpoint. It is not a refutation of injectivity at the singled-out default (1/2,1/4), nor of entire-function injectivity, nor a proof of a degree-weighted isospectral pair. No universal lemma remains missing for the pointwise refutation. Classical continuity, matrix-norm tail bounds, surface classification and Steinitz are routine supporting bridges, not separate discoveries.

A deterministic-seed walk through 600 WL-distinguished C60 dual candidates sustained the alternative pencil route. Exact moments k=1..8 for A+tD, t=0,1,2 left three candidate pairs; exact moments 9 or 10 at t=0 rejected all three. Those are finite exclusions, not an impossibility theorem. No switching theorem was imported without hypotheses; the successful witness is certified directly in the source class.

The 2019 Bille–Buchstaber–Spodarev paper, arXiv:1910.00846v1 Section 3 pp8–9, gives a C44 adjacency-cospectral pair and Conjecture 1 about adjacency spectra. Its fragment flip is explicitly not generally spectrum preserving. Neither that construction nor adjacency cospectrality alone settles a nonconstant degree-weighted pencil. This C60 witness is not adjacency cospectral and uses an interior parameter crossing instead. The 2024 source itself cites the 2019 paper and nevertheless poses Conjecture 3.

Bounded prior work: r285 source and parent handback read, semantic cache filter applied, current author arXiv listings and source record retrieved, current regular GitHub registry heads recorded. No matching fullerene proof body was found in the inspected cached Problems corpus. That does not clear all current registry files, all citations, or the full specialist literature. No worldwide novelty or campaign acceptance is asserted. Root must commission independent adversarial source/prior review and decide eligibility. No Lean or manuscript was written.
