# Pairing and repetition after ribbon substitution

Prefreeze calculations, not a theorem submission. All maps here refer to the ordinary irreducible determinant-one, unframed complexes used by Source306. Replacing them with framed instanton groups changes the question.

## 1. Exact map needed

Write B:C(Y_+)→C(Y_-) for the source's integral signed negative interval map, and H=f_+f_-:C(Y_-)→C(Y_+) for its integral positive return. Both are mod-two homology units, hence rational homology isomorphisms by the source finite-free cone argument. A proposed ribbon replacement needs maps F=F_W and Fbar=F_Wbar on THESE complexes, with compatible determinant transitions, and needs Fbar F to be a nonzero scalar identity or at least a rational homology isomorphism. Since the source handle units identify the rational dimensions of the two end homologies, split injectivity of F then makes both F and Fbar isomorphisms.

The published ribbon theorem for framed I# on general closed manifolds is not this assertion. Its ordinary unframed theorem is stated for integral homology spheres. A late read of Daemi–Miller Eismeier v2, Corollary 7.2 and its operative proof, supplies the existence and functoriality of irreducible maps for our pseudo-unobstructed cobordisms. Thus existence of an abstract unframed map is not the remaining gap. The ribbon-double identity and the common geometric realization with the source tests are analyzed in OPERATION.md. The following calculations assume that stronger interface, not merely functoriality.

## 2. Cap nonvanishing is more robust than a chosen covector

Start with the source enhanced closure of Y_0, its odd determinant, retained genus-two tight surfaces and nonzero ordinary Donaldson pairing. The closed manifold obtained by inserting k copies of the return

    T=f_- Fbar f_+

has the same rational H^2 additions as in the source. CARRIER.md establishes simple connectivity of its handle return, so the source's local irreducibility reason for comparing exact tests with Donaldson probes is not lost merely because W has 1-handles. The original cap pieces and their tight surfaces remain untouched.

For a surface insertion of multiplicity a use the finite ring

    L=Q[t_1,...,t_a]/(t_1^2,...,t_a^2), J=(t_1,...,t_a).

Each occurrence is labelled; t_i t_j is retained for i≠j. If a geometrically defined labelled return T_L reduces to T modulo J, its mapping cone is filtered by J^j. Each associated quotient is copies of the cone of T. Acyclicity of those quotients implies acyclicity of the cone, by successive short exact sequences. Thus T_L is a rational homology isomorphism. A rational isomorphism of the undeformed homology alone does not manufacture the labelled map: compactness and coherent incidence representatives remain necessary.

Let x and y be the deformed cap states and suppose the designated coefficient of yx is nonzero. Regard the finite L-module homology as a finite-dimensional Q-vector space. Its invertible operator T_L has characteristic polynomial p(t)=a_0+a_1t+...+t^d with a_0≠0. Cayley–Hamilton gives

    id=-(a_1 T_L+...+T_L^d)/a_0.

If every positive-power coefficient [t_1...t_a] y T_L^k x vanished, the coefficient for yx would vanish too. Hence some positive k has a nonzero closed pairing. This is the actual source positive-power mechanism, and it is already paid once the geometrically compatible labelled return exists. It is not enough to pick a nonzero linear functional on Floer homology and call it a cap invariant.

After this positive power, allocate all probes to the two fixed caps across a rational seam, as the source does, and clear denominators. The resulting q=yx is a nonzero integer. Again this conclusion is conditional on the geometric labelled-map interface, not only the displayed linear algebra.

## 3. Two-adic invertibility is not the essential missing operation

Suppose the new ribbon maps are only available over Q. Choose finite rational bases and one integer D that clears all entries, inverse entries and cap-pairing denominators for the finite list of maps. Let q_0≠0 be the resulting numerator of the pairing. Select an odd prime ell that divides neither D nor q_0. Then all these maps and their inverses are defined over Z_(ell), and reduction modulo ell lies in a finite general linear group.

This gives a precise repair to the overly strong demand that the ribbon map itself be a mod-two unit. The source B and H are already rational isomorphisms. After excluding finitely many primes their reductions are invertible too. For rank r≥1 an explicit usable common multiple of all element orders is

    E=8 |GL_r(F_ell)|,
    |GL_r(F_ell)|=product_{i=0}^{r-1}(ell^r-ell^i).

A common multiple over the finite list of ranks works if necessary. Choosing counts in multiples of E preserves the source's mod-eight bundle/index congruence and returns each repeated matrix to the identity modulo ell. The scalar 2^eta in the final phase-link count remains nonzero modulo the odd prime; integrally/rationally it is nonzero regardless. Thus changing the prime introduces no new obstruction to the contradiction.

Do NOT rescale a geometric map by an arbitrary integer and then pretend the rescaled matrix is the geometric cobordism count. The localization argument chooses a coefficient ring where the actual rational map and its inverse are defined. If a normalization constant occurs in the surgery formula, exclude its numerator and denominator from ell as well. No artificial geometric rescaling is needed.

## 4. Noncommuting blocks and the growth constraint

Set A=F B and D_0=H B as endomorphisms of the Y_+ homology. Following the source convention, a four-interval block with one positive return and three W returns is the word A^3 D_0, up to the fixed chronological convention. The argument needs finite order of this entire word, not the false equality (A^3 D_0)^j=A^{3j}D_0^j. Both A and A^3D_0 are invertible modulo ell.

Take left and right pads with counts multiples of E and m blocks with m a multiple of E. The product matrix is the identity modulo ell, so the pairing of the repeated stack is q modulo ell and cannot vanish. Since E is divisible by 8, increasing m through these multiples preserves the index congruence. With n=4m+d the formula in CARRIER.md gives n_D=m/8+C, hence eventually positive. No uniform estimate on E, the small perturbations, or the geometric threshold is asserted; all are finite choices after the fixed problem and maps are specified.

These calculations remove finite-lattice repetition, cap algebra and index growth as independent conceptual barriers. They do not prove the ribbon map or the equality between the long-neck geometric count and this matrix product.
