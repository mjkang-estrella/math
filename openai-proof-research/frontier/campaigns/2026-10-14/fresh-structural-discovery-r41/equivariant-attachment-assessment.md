# Family317: the orbitwise attachment interface is a technical source adaptation

This is an author-side operation comparison, not a nominated theorem or independent gate. It explains why genuine discrete-group equivariance alone is not being claimed as a substantial new construction. The source is Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026 at the stipulated pin. Its §§3–6 provide every hard nonequivariant operation used below. No general assertion that fixed points preserve arbitrary categorical pushouts is made.

Fix any small discrete group G, any subgroup H≤G, the orbit S=G/H, any subgroup K≤G, and any strict dimension1≤n≤ω. Write U(P)=c_n N_ord(P). Let A⊂B be a FINITE sieve of posets, whose inclusion in its upward closure Z⊂B has a right adjoint retraction. Give U(A),U(B) trivial G-actions and S⊗U(P) the disjoint-copy action. For any equivariant map S⊗U(A)→X, form the actual equivariant pushout Y=X⊔_{S⊗U(A)}S⊗U(B).

The source operations give the fixed-nerve comparison

    N(X^K) ⊔_{S^K×N U(A)} (S^K×N U(B))  →  N(Y^K)

as a weak equivalence. Here fixed categories mean cells fixed in every dimension, and S^K is an ordinary set. This is a homotopy comparison, not an asserted isomorphism of fixed categorical pushouts.

First consider B=Z, so A⊂B itself has the retraction. Induct on the number of new elements in the FINITE template B\A, without enumerating the possibly infinite orbit S. When B\A has greatest element b, source Lemma greatest-new constructs two right Gray cylinders, stationary on U(A), from identity to a common endomorphism and from a retraction endomorphism to that same endomorphism. Use exactly these chosen template maps on every S-copy. Tensoring with the interval preserves the disjoint coproduct, so these give cylinders on S⊗U(B); they commute with G because G only permutes copies. The source pushout-cylinder lemma is natural in the attaching map. Its glued cylinders on Y are therefore G-equivariant and stationary on X, and the glued retraction Y→X is equivariant.

Restrict these cylinders to K-fixed cells. Explicitly the inclusion Y^K→Y gives a map Y^K⊗D1→Y⊗D1. Compose with the equivariant cylinder. Every K-action fixes this composite because it fixes Y^K and the interval has trivial action; by the equalizer property it factors uniquely through Y^K. The endpoints and stationarity restrict as well. No claim that Gray tensor commutes with fixed points is needed. The source Gray-nerve lemma then gives the same homotopy zigzag on N(Y^K), with retraction to N(X^K). Thus X^K→Y^K is a Street weak equivalence.

If the new template has no greatest element, choose two distinct maximal new elements b1,b2 exactly as in source §5. Delete b1, b2, or both from EVERY orbit copy. These template deletions define G-invariant full sieve subcategories Y1,Y2,Y12 of Y by source labelled-pushout and attachment-cover results. They cover Y on objects and have the stated full intersection. Their K-fixed categories are again full sieves of Y^K, cover its fixed objects, and intersect in Y12^K. This is immediate from fullness and cellwise fixedness; it does not commute a general pushout with a limit. Source nerve-cover and simplicial gluing apply to the three smaller-template induction comparisons. This proves the retraction case for any orbit size and any subgroup K. The zero-new-element case is identity.

For general B, put C=B\A and T=Z\A. Source §6 identifies Y_Z=X⊔_{S⊗U(A)}S⊗U(Z) and S⊗U(C) as G-invariant full cosieves covering Y, with intersection S⊗U(T). The same source formulas apply to the poset S×B, a disjoint union even when S is infinite. Their fixed categories are full cosieves covering Y^K and intersect in S^K⊗U(T). The identity

    (S⊗U(P))^K = S^K⊗U(P)

holds because every cell belongs to one disjoint copy and the action inside a copy is trivial. A non-fixed copy contains no fixed object and hence no fixed cell.

The retraction case says N(X^K)→N(Y_Z^K) is a weak equivalence. Also NU(A)→NU(Z) is a monomorphism and weak equivalence by the source. Taking S^K copies and pushing out makes

    N(X^K)→P_Z := N(X^K)⊔_{S^K×NU(A)}S^K×NU(Z)

a weak equivalence. Two-out-of-three gives the canonical P_Z→N(Y_Z^K) weak equivalence. Source cosieve-cover identifications now express both sides of the desired B-comparison by adjoining S^K×NU(C) along S^K×NU(T). The specified intersection-to-C leg is monic. Simplicial left properness gives the desired comparison, with the same source §6 proof. All maps compared are canonical; the auxiliary contractions establish weak equivalence and need no compatibility between distinct maximal-element pieces.

This calculation addresses exactly the apparent higher-composite fixed-point concern for generating boundary/horn attachments. Twice-subdivided generators have the finite poset form by source Lemma subdivision-posets. Horn acyclicity and boundary-attachment invariance on each fixed nerve follow by the same two-out-of-three/gluing argument. Transfinite sequences of these attachments are unions of full sieve inclusions, so fixed cells commute with those unions even for an infinite subgroup K: an element of an invariant subobject fixed in the union was already fixed in that subobject. General filtered colimits with noninjective arrows would require a different argument and are NOT being used.

Marc Stephan's arXiv1308.0856v2 Proposition2.6 was read with its exact cellularity conditions, and Example2.18 already gives the ordinary Cat case. Its pushout condition is an ISOMORPHISM assertion stronger than the comparison just proved; we do not assert that hypothesis without proof or invoke the proposition verbatim. The direct source small-object transfer can instead use horn acyclicity on fixed nerves. Standard model-category bookkeeping is not written out as a complete new candidate here. The hard local contractions, invariant labelled covers and attachment comparison are the stipulated source machinery, with the template choices repeated uniformly on orbit copies. Under this project's contribution standard, this is a technical equivariant adaptation, not a nominee based merely on a new parameter G.
