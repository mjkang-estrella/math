# T019S59 — attempted full two-prime section theorem

The exact question is `original-scope.md`. It is unresolved. This file records proved elementary interface deductions and outstanding geometric interfaces; it is not a unified proof. The source theorem is stipulated, not audited.

## 1. The first selection was paid

Mochizuki–Tsujimura, revised 30 March 2024, Theorems A and 2.17, give Sigma-RNS whenever p belongs to Sigma and Sigma has at least two primes. The model-domination formulation allows a geometrically pro-Sigma finite étale Galois cover. In particular Sigma={p,ell} is allowed. The pinned exterior-sheet manuscript subsequently uses cyclic ell residue covers, cyclic p graph covers, conjugate composita, and a stabilizer quotient. These operations preserve a finite group whose prime divisors lie in Sigma. Burnside's two-prime theorem then makes that group solvable. Thus merely asserting a solvable or two-prime exterior-sheet cover is a transfer of a stronger primary interface, not a new contribution.

There is still a distinction between producing these geometric covers and classifying all sections of a quotient fundamental group. A quotient section need not lift to a full section. The source's full section theorem cannot silently supply such a lift.

## 2. Exact equivariant patching

Let C -> X over an algebraically closed characteristic-zero field be a connected Galois curve cover with finite group Gamma. Let Y -> X be finite, with the collar roots required by the source's Proposition `prop:patching`. Over the exterior U, C x_X Y is a Gamma-torsor. The root hypothesis splits it on the *entire* inverse image of each boundary annulus.

This split torsor admits a Gamma-equivariant trivialization on each connected overlap: choose one of its sections and send gamma to its translate. Different components can use different choices. The overlap is a finite cover of an annulus, hence has finitely many connected components; the choices define an analytic equivariant isomorphism. Over each inner-disk inverse image use the trivial Gamma-torsor Y_b x Gamma. Glue with these equivariant identifications. There are no intersections between distinct inner disks. The Gamma-action glues, and the torsor identity is local, so the result is a finite étale Gamma-torsor over Y. GAGA algebraizes both the algebra and this finite action, as in the source's proof.

For a connected component V, its monodromy image H is a subgroup of Gamma: a fiber is the regular Gamma-set and geometric monodromy acts through left translations. Its orbit H is a component fiber, with right H giving the deck group of V -> Y. Consequently the connected component is Galois over Y with a group isomorphic to H. The exterior projection still supplies the same point-transfer map as in the source. No action on an arbitrarily chosen component by *all* Gamma is asserted.

If the Galois closure of Y -> X has Sigma-order, and Gamma has Sigma-order, the normal closure of V -> X also has Sigma-order. After passing to the normal closure Y' of Y, each conjugate upper extension has group a subgroup of H. Their compositum has group a subgroup of a finite product of these groups, and the total group is an extension by Gal(Y'/X). This proves the assertion without bounding it by a symmetric group of the degree. This distinction matters: a degree-ell non-Galois cover need not have ell-group normal closure.

This is an equivariant version of the source's already credited patching method, not a separate nominee.

## 3. Prime control in the second collar stage

Suppose m is a Sigma-integer. In `05-arbitrary-roots.tex`, the auxiliary cover Z -> P1 is cyclic of degree ell. The cover pulled back from [m]:J -> J is a torsor under J[m], an abelian Sigma-group. Each connected component has subgroup monodromy. The preceding normal-closure argument shows that Q -> P1 has Sigma-order Galois closure. Pullback along t_b/beta_b, normalized components, and composita preserve this property. The source's horizontal indices-divide-ell assertion is a separate constraint and also persists.

Therefore the source's *second* root stage and its subsequent patching retain Sigma if the first-stage étale collar root covers can be chosen with Sigma-order Galois closures. The analytic estimates, slope-one character, period-coset gluing, and logarithm/exponential margin are exactly the source's work. No new estimate is claimed here.

The missing first-stage assertion is precise: each stable node annulus must acquire an ell-th root on its entire inverse image in a finite étale cover with Sigma-order Galois closure. The printed metrized-complex construction has degree ell, but arbitrary gluing of cyclic residue covers does not by itself prove cyclic global monodromy. One must produce compatible cyclic actions through the annular gluing/lifting, including the separating-edge preliminary cover. Equivariant residue data suggest a repair, but this packet does not claim that ABBR's non-equivariant existence statement alone proves it. Sigma-RNS does already handle the subsequent disk-to-stable-node step.

Subject to that first-stage assertion, equivariant patching and the source's realization proof would show K^Sigma_bir lies in the completion of K^Sigma_et for every rank-one norm extending the p-adic norm. Here K^Sigma_bir is the maximal geometrically pro-Sigma extension, including all constants. It is essential to replace *both* fields: containment of the entire separable closure is not proved and is not needed.

## 4. A proved repair of the Brauer entry point

Let Pi=pi_1(X), Delta=pi_1(X_bar k), N=ker(Delta -> Delta^Sigma), and Pi^Sigma=Pi/N. Put A=Q_ell/Z_ell(1). Delta acts trivially on A. Then

    H^1(N,A)^Pi = 0.

Indeed a continuous character chi:N -> A has finite image, since N is compact and A discrete. Pi-invariance implies Delta-invariance. Its kernel is consequently normal in Delta. If chi is nonzero, Delta/ker(chi) is an extension of the pro-Sigma group Delta/N by the finite ell-group N/ker(chi). Such an extension is pro-Sigma: every finite quotient has a normal Sigma-subgroup and Sigma quotient. Maximality of Delta^Sigma forces N into ker(chi), a contradiction. This does not assert that N has no arbitrary ell-quotients, only that the relevant invariant characters vanish.

The five-term Hochschild–Serre sequence now makes inflation

    H^2(Pi^Sigma,A) -> H^2(Pi,A)

injective. A section of Pi^Sigma -> G_k splits the first pullback in

    H^2(G_k,A) -> H^2(Pi^Sigma,A) -> H^2(Pi,A) -> H^2(X,A).

The last comparison is injective in degree two, exactly the comparison used in Stix's Proposition 12. Thus the composite is injective. Stix's Leray/Kummer diagram proves that the Brauer obstruction b kills Pic_X(k)[ell-infinity].

Stix Theorem 9 identifies the order of Br^0(X/k) with the period. The Mattuck decomposition used in his Corollary 14 writes J(k) as a pro-p part and a finite torsion part. The pro-p part has no nonzero finite ell-primary quotient (multiplication by ell is bijective); the ell-primary torsion part is killed by the preceding argument; prime-to-ell torsion cannot map nontrivially to an ell-group. Hence ell does not divide the period. By Lichtenbaum's index | 2 period (Stix Theorem 10), ell does not divide the index because ell is odd.

Exactly the same reasoning applies to every finite quotient-section neighborhood Y/k: the maximal pro-Sigma quotient of pi_1(Y_bar k) is its corresponding open subgroup of Delta^Sigma. This follows from stability of finite Sigma-groups under extensions and taking a finite conjugate compositum; it is not an assumption that every arbitrary finite cover remains in the tower. Roquette–Lichtenbaum therefore implies that the class of invariant 1/ell survives in Br(k(Y)) and in the direct limit over all these neighborhoods.

This repairs the *entry point* to Pop–Stix Theorem 25. Their Proposition 24 proves more (an isomorphism on an ell-primary Brauer group), but the local–global extraction only needs this survival. The new bookkeeping is the elementary invariant-character argument; the Leray diagram, Mattuck, local duality, and index-period relation are fully credited classical tools.

## 5. What the remaining localization proof must establish

Pop–Stix Theorem 26 is stated for a full section, not a quotient section. After the Brauer repair, their Theorem 25 extraction of a Sylow subgroup into valuation decomposition can be repeated in the restricted tower using their local–global principle, provided every occurrence of the tower is changed consistently. This alone does not place the full section in one decomposition group.

Theorem 27 then requires, inside the *restricted* geometric tower:

1. cofinal equivariant models with every stable component of genus at least two;
2. separation so distinct components meet at most once;
3. independence of the positive-genus ell-inertia lines in the restricted specialization kernel;
4. compatibility with logarithmic inertia and the model-refinement inverse limit.

The actual Proposition 4 computation uses a limit over finite étale covers of the special fiber and its induced modules. It cannot be imported merely because the full group's inertia lines are independent: a quotient can destroy their independence. A promising adaptation is to redo that computation over Sigma-covers and use cyclic ell covers of positive-genus residue components to make the relevant degrees unbounded. The required log-cover/component construction and cofinality were not completed here.

The printed Lemma 11 uses the maximal geometrically abelian exponent-2 graph cover; 2 need not belong to Sigma. Its elementary graph replacement does work with exponent ell: choose a spanning tree and label each non-tree edge by its independent basis vector in H_1(G,F_ell). The voltage lift is the maximal abelian exponent-ell graph cover. Two distinct edges between the same base vertices differ by a nonzero length-two cycle, so their lifted endpoints cannot agree. A loop has nonzero voltage, and for odd ell its opposite orientations do not create a second undirected edge with the same endpoints. Thus distinct lifted vertices meet at most once. This repairs the *graph* condition, not its realization as the needed equivariant curve cover or the inertia computation.

Mochizuki's November 2010 comments, read in full, do not close these obligations: assertion (6) extends the tempered local-ring consequences to Sigma containing a prime different from p; (A5) is the injection from tempered sections; (A6) states the profinite/tempered bijection only for all primes. A section of Pi^Sigma cannot be treated as tempered without another argument.

## 6. A shorter birational endgame, conditional on the two missing interfaces

The following reduction avoids an unnecessary generalization of the source's two-henselian-valuations contradiction. It remains a reduction, not a result on T019S59.

Assume quotient localization and the prime-controlled completion statement above for every curve in the frozen scope. Given a quotient section of Y/k, localize it at a valuation extending the p-adic valuation. If a coarsening trivial on constants is a closed-point valuation, decomposition surjectivity onto G_k forces that point to be rational, so Y(k) is nonempty. Otherwise a rank-one coarsening extends the p-adic norm. Restriction from birational to étale decomposition groups is surjective by transitivity on prolongations; prime-controlled completion makes its kernel trivial, because a kernel automorphism fixes the dense étale subfield and thus its completion. The quotient section therefore lifts to the geometrically pro-Sigma birational group.

Let k'=k(mu_p). The birational Sigma-extension contains the maximal elementary p-metabelian extension of k'(Y), since its geometric group is pro-p. Compose the restricted birational section with this quotient. Functoriality of the elementary p-derived series makes it a liftable elementary abelian section in the exact sense of Pop's 2007 Theorem A. That theorem supplies a unique k'-rational point attached to this elementary section. For sigma in Gal(k'/k), conjugation by the original birational section transports the restricted section to itself with the natural sigma action. Uniqueness in Pop's theorem forces its point to be fixed by sigma. Hence it descends to Y(k). This uses uniqueness only for the elementary quotient, and does not assert that the whole birational Sigma-section is contained in its horizontal decomposition group.

Apply this existence conclusion to every finite neighborhood of the original section. The images of Y(k) in X(k) are nonempty closed subsets of the compact p-adic space X(k). They have the finite intersection property, since intersections of finitely many open subgroups containing the section give a common finite neighborhood. Thus they share a point x. Equivalently, consider all pointed neighborhood fibers above x: they are finite, and every finite subsystem has a compatible rational lift by passing to a common neighborhood. Compactness gives a compatible G_k-fixed point of the inverse-limit fiber. The stabilizer is a conjugate of the point-section group, so the original section is geometric.

Injectivity is also retained in the frozen target. Hoshi's May 2010 introduction identifies pro-p point-section injectivity as known, citing Mochizuki Theorem C and Theorem 4.12. Those original operative bodies were not read here; this packet therefore records a primary lead, not a completed independently checked injectivity input. The source's elementary Jacobian proof with all n cannot just be restricted to Sigma: prime-to-Sigma torsion survives that abelian test.

## 7. Disposition

There is no counterexample to T019S59 here, and no complete proof. The useful exact progress is equivariant torsor patching, the invariant-character/Brauer repair, the odd-ell graph separation, and the conditional birational-neighborhood endgame. None is nominated separately. The two remaining geometric interfaces are explicit in sections 3 and 5. Any future full candidate must prove those interfaces with actual prime-controlled lifting/cofinality, check the primary injectivity input, and compare the resulting operation against the existing pro-Sigma literature. A proof assembled from standard prime-control repairs would still need a separate contribution assessment; module count is not substantiality.
