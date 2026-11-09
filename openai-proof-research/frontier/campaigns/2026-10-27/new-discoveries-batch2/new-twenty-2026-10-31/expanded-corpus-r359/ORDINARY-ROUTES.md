# Ordinary proof routes and separate gates

This is discovery work only. No solver, mathematical enumeration, CAS, Lean execution, acceptance or Pi dispatch occurred. Credit is zero and 52/60 is unchanged. Literal statements and complete records are in literal/ and provenance.json. A full refutation of a conjunction needs only one false conjunct, but that logical fact does not make an equality-condition correction eligible for campaign credit.

## 352285: secure domination — complete exact refutation, already a source reduction

Definitions actually read: arXiv:2110.09190v2, introduction and Section 2. A dominating set D meets the closed neighbourhood of every vertex. It is secure if for every vertex u outside D some adjacent v in D can be replaced by u while preserving domination. The 2-subdivision replaces each edge by a path with two edges, not by a path with two new vertices.

Take G=P4 with vertices a,b,c,d and edges ab,bc,cd. Its subdivision is the path on seven vertices indexed 0,1,...,6, with original vertices 0,2,4,6. Let D={1,3,5}. It dominates. The outside vertices are precisely 0,2,4,6. Respectively choose defenders 1,3,3,5. The four replacement sets are {0,3,5}, {1,2,5}, {1,4,5}, {1,3,6}. Their unions of closed neighbourhoods, intersected with {0,...,6}, are respectively
[0,1] union [2,4] union [4,6];
[0,2] union [1,3] union [4,6];
[0,2] union [3,5] union [4,6];
[0,2] union [2,4] union [5,6].
Each union is the whole vertex set. Thus D is secure and gamma_s(P7)<=3. Each closed neighbourhood in P7 has at most three vertices. Two selected vertices can dominate at most six vertices, so every dominating set has size at least three. Consequently gamma_s(P7)=3. The proposed inequality would assert 3>16/5, which is false.

The route was pursued beyond testing a minimum set: the explicit swaps establish security, the neighbourhood bound establishes optimality, and the subdivision isomorphism establishes exact source semantics. No program enumerated sets.

Decisive exclusion: Remark 2.5 of BOTH the fetched v1 and v2 explicitly gives P4^(1/2)=P7 and gamma_s(P7)=3. Theorem 2.2 already gives gamma_s(Pn)=ceil(3n/7). Specializing n=7 and multiplying 3>16/5 by five yields the contradiction 15>16. This is a complete same-source/classical bridge, not a novel mathematical outcome. It is not excluded for being small.

A broader approach based only on gamma(H)>=|V(H)|/(Delta(H)+1) fails to give the proposed 4|V(G)|/5 bound when maximum degree is large. Paths explain why that general bound is not repairable by this shortcut. No corrected universal inequality is claimed.

Gates: ordinary exact refutation COMPLETE; source-definition fidelity COMPLETE for arXiv v1/v2; substantive novelty FAILS by explicit earlier-result bridge; journal/correction completeness OPEN (journal DOI GET returned 403, not retried); independent review and formalization NOT RUN. No CANDIDATE.md and no dormant implementation request: this route is ineligible.

## 350444: Laplacian coefficients — complete equality-clause refutation, correction only

Definitions read in arXiv:2104.08476v1, opening and Theorem 3.5/Conjecture 5.1: psi(G,lambda)=sum_k (-1)^(n-k)c_k lambda^k; A1 is adjacency of the line graph. The displayed first bound concerns c_(n-4). Its claimed equality condition is that girth is not three.

Take G=K3 disjoint union three isolated vertices, so n=6. This is a finite simple graph in the literal unrestricted graph domain. Its Laplacian has a 3x3 block 3I-J and three zero rows and columns. The triangle block has eigenvalue zero on the constant vector and eigenvalue three on the two-dimensional coordinate-sum-zero subspace. Thus psi=lambda^4(lambda-3)^2=lambda^6-6lambda^5+9lambda^4, and c_(n-4)=c_2=0. This can equivalently be obtained by a direct determinant of the triangle block; no spectral approximation is involved.

The line graph is K3. For its adjacency B=J-I, B^2=J+I, giving tr B^2=6, tr B^3=6, tr B^4=18 (also eigenvalues 2,-1,-1). The original adjacency has the same nonzero block, so tr A^2=6. Substituting into the numerator of the first proposed bound gives
0 - 6*36*6 + 6*(60*6+8*6) - (144*6+48*6+6*18) + 3*36
= 0 -1296+2448-1260+108 = 0.
After division by 24, the proposed upper bound equals c_2=0. Nevertheless girth(G)=3. Therefore the first equality biconditional is false, and hence the full literal conjecture (a conjunction of three bounds and equality clauses) is false.

This was pursued through both the coefficient semantics and the entire trace substitution; merely observing a triangle or quoting a forest identity would not suffice. Adding isolated vertices does not change the relevant traces and shifts the characteristic polynomial indices in the way computed above. n=6 avoids negative-index ambiguities in all three clauses. We make no assertion that the second and third bounds fail.

The more ambitious route was to identify the right side with an elementary symmetric polynomial of a signless/incidence matrix and prove all coefficient inequalities via rooted forests or Cauchy–Binet. Theorem 3.5 is stated with a FOREST hypothesis for these formulas. Removing that hypothesis has not been justified: cycle contributions to traces of the line graph must be tracked. This is the precise missing identity, so the forest theorem cannot silently prove the general conjecture. No CAS or matrix enumeration was run.

Gates: literal conjunction refutation COMPLETE; source definitions COMPLETE for v1; substantive novelty FAILS under equality/domain/endpoint-correction precedent. The journal counterpart is Computing some Laplacian Coefficients of Forests, Journal of Applied Mathematics 2022, article 8199547 (identified by search; Wiley body remains unread under inherited denied-route restriction). Source references include Das–Ghalavand–Ashrafi on k-matchings and Zhou–Gutman on ordinary/Laplacian spectra of bipartite graphs; these bodies were not read, so neither the universal inequality nor literature completeness is cleared. No eligible candidate or Pi plan.

## 326842: finite quandle separation — sustained full-endpoint attempt, unresolved

Primary source read: arXiv:1312.3307v2, Lemma 3.2, Conjectures 3.4–3.6, Proposition 3.7 and its proof. The endpoint is separation of EVERY pair in ANY finite symmetry-closed knot set, modulo equality or simultaneous mirror/reversal mr; merely distinguishing different four-element symmetry orbits is weaker. Col_Q(K) counts all colorings, not merely existence of a nontrivial coloring.

First route: for each pair K,K' not equivalent modulo mr, obtain a finite quandle Q with unequal coloring counts, then collect one witness for every pair. Because the knot set is finite there are finitely many pairs, so the collected list is finite. Lemma 3.2 supplies equality of coloring counts for K and mr(K), yielding the reverse direction of the required iff. This reduction is complete CONDITIONAL ON pairwise count separation. It is not itself a solution: the pairwise separation assertion is the main missing lemma, not a certificate-management detail.

Attempted justification by residual finiteness fails: separating two elements of one fundamental quandle by a finite quotient does not separate two different knot quandles by HOMOMORPHISM COUNTS. A nontrivial homomorphism may exist on both. Even obtaining a quotient of one object that does not occur as a quotient of another requires a distinction of their finite quotient theories, not elementwise residual finiteness. A finite-target counting characterization for finite algebras cannot simply be applied to infinite fundamental quandles. Needed bridge: non-mr-equivalent knot quandles have different finite-target hom-count profiles, with orientation/peripheral semantics retained.

Second route: use known completeness of the fundamental knot quandle, then pass through finite quotients. Completeness of the full quandle invariant is weaker than recoverability from finite quotient data and counts. A reconstruction theorem with exactly these marked/orientation conventions is missing. Without it, the proposed finite certificate contains an unproved infinite bridge.

Third refinement: Proposition 3.7 reduces verification to orbit representatives and four kinds of inequalities, including K versus m(K) for chiral/negative-amphicheiral knots. Its proof uses invariance under mr to reduce all cases to (A)–(D). Conditions (A)–(C) only give the weaker orbit separation; dropping (D) does not establish Conjecture 3.4. The paper's experiments up to twelve crossings establish no arbitrary-knot pairwise lemma. No computation was launched.

Gates: source statement/definition reading PARTIAL but substantive; ordinary full exact proof OPEN at pairwise hom-count separation; current literature, all versions and journal comparator bodies OPEN. v1 was acquired and text-extracted but not substantively compared; journal metadata is J. Knot Theory Ramifications 23 (2014), no.6, 1450035. No Lean/Pi plan, since the missing lemma is mathematical and unbounded.

## Other useful complete bridge: 323992 is not cleared by index metadata

The current LeanPool catalogue has a Nivat project, and its public paper nivat.tex states rectangular complexity <=mn implies a nonzero period h. Cyr–Kra's actual definition of expansive subspace and their modified conjecture were read in arXiv:1208.4090v2, pp.2–3. Here is the exact elementary deduction, conditional on the public periodicity theorem.

The closed subset of configurations fixed by h contains every translate of eta, so it contains X_eta. Let L be any line not parallel to h, and let nu be a unit normal to L, with a=nu dot h nonzero. For each z in Z^2 choose an integer k nearest to -(nu dot z)/a. Then |nu dot(z+kh)|<=|a|/2. If two h-periodic configurations agree on the strip of width |a|/2+1 around L, they agree at z+kh and hence at z. Thus every such L is expansive. In the product metric, choose delta so that distance<delta forces agreement at the origin; the stated strip criterion implies the paper's metric definition. The only possible nonexpansive line is span(h), so there is at most one. This is a complete routine bridge from a full Nivat theorem, not a new result.

The public paper's main statement and part of its descent argument were read, but its complete proof/dependency audit and exact pinned formal declaration were NOT independently checked. LeanPool/projects.yml and LeanPool.lean only route that further investigation. Therefore this lane records a material public subsumer HOLD rather than claiming novelty clearance or accepted resolution. No formal execution was performed.
