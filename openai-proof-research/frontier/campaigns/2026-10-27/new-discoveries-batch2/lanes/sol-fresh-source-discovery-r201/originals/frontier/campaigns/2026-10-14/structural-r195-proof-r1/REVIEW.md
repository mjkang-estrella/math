# Structural195: independent full correctness review, round 1

**Verdict: PASS for the entire unchanged frozen theorem and unchanged author proof, relative to the stipulated truth of Source319 and all operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.** No necessary correction or essential uncompleted mathematical verification remains in this review. This is a correctness verdict only. It assigns no contribution verdict, acceptance, or count.

Provenance: Codex / GPT-6 Astra / high / default service tier. The review override controls; the retained standing discovery instructions do not authorize a substitute theorem, a new freeze, author development, or downstream work. No author file was modified. The derivations below reconstruct arguments already present in the author proof against the actual source interfaces; they are not repairs offered in place of missing author arguments.

## 1. Identity, scope, and evidence standard

The reviewed FROZEN.md is exactly 2265 bytes, SHA256 `823bddbdf60d3827d4f0cbf5684d559de760646b811f1626db497ed1786f8be8`. AUTHOR-PROOF.md is exactly 34147 bytes, SHA256 `c0c2a3205e9f5a1eccb5fb5dbc87c97402c1740c251fe4c0f40aa0cf86c7cc27`. Both are under `../fresh-structural-discovery-r195/`; exact private copies are retained here for the review packet. The original modes and bytes were recorded and checked again at handoff.

The quantifier is **every prime p admitting an odd M with M>=81, p>16M^2, and 2 floor(M/8)>p^(1/3)**. For each such fixed p there is a countable family indexed by all positive integers. The object b_p is the p-completion of the source's standard regular BP-module quotient by the Araki v_i, i>2. All closures are ordinary thick closures in p-complete spectra: finite sums, arbitrary integer shifts, cofibers, and retracts. Every numbered item is reviewed for every j, and the nonmembership is against b_p and **all** i different from j.

The assertion that every sufficiently large prime is covered is consistent with these exact inequalities: choose an odd integer just below sqrt(p)/4; then 2 floor(M/8) is sqrt(p)/16 up to a bounded error and eventually exceeds p^(1/3). No numerical threshold is substituted. These inequalities imply the source's other prime bounds, in particular the periodic sparsity used below.

The review uses the actual canonical wrapper, all eight operative section bodies, references and README. The complete tree, not the truncated tree, authenticates the twelve blobs in the single fourteen-entry manuscript folder. All eleven text blobs were read completely; the compiled PDF was authenticated only. Source truth, including the source's single-object headline, is paid by the brief. Applicability of those operations to the new symbols, targets and relative transport is what is being tested.

Primary reading includes the final Lee-Pstragowski mathematical body, the operative Mahowald-Rezk and Christensen proofs, Pstragowski Section 6 and Appendix B, and the original Bhargava p-ordering/Newton arguments. Barkan's stronger comparison and Hahn-Wilson's statements were checked only at the recorded extents; their full proofs are not dependencies. The unavailable AVVO paper is not a dependency: the source contains the actual complete microlocal proof used here. Exact independent extents and access limits are in `private/READING-AND-ISOLATION.md` and its records. Neither metadata nor the parent assessment was treated as proof reading.

Author byte locators are: §1 [563,2820), §2 [2820,7062), §3 [7062,10425), §4 [10425,17926), §5 [17926,22485), §6 [22485,26733), §7 [26733,30693), §8 [30693,34147). Source labels below are located exactly in `private/source-labels.json` and in the complete private source copies.

## 2. Weighted operations and tame eigenlifts

Author §2.1 uses the ordered basis in `geom:group-filtration`, `geom:group-graded`, and `geom:skew-filtration`. Raising wt(x) from the source value to any integer W>3 preserves the required inequalities. The commutator of the two weight-one group directions has weight at least 3, strictly larger than 2. Commuting a weight-one direction past the weight-three direction produces weight at least p>4. The coefficient commutators have weight at least 2W>W+3. Thus each reordering increases the filtration strictly. The same finite binomial bases give the independent ordered initial monomials; increasing W does not add an initial relation.

Completeness and topology are also preserved: all four weights are positive, finite coefficient/group quotients have nilpotent augmentation ideals, and sufficiently high ordered degree contains the prescribed neighborhoods. Consequently gr_W Delta is k[X,A,B,C] with weights W,1,1,3, and Delta/(x)=Omega remains valid with x normal and regular. This is not an assertion that the filtrations have equal degree functions.

The tame group has order prime to p. Its first-digit action over k has the two characters chi and chi^(-1): multiplication by a norm-one element has eigenvalues lambda and lambda^p=lambda^(-1). Character averaging therefore gives exact eigenlifts V_1,V_2 with chosen independent initial vectors A,B. The product V_1 V_2 is invariant even though the lifts need not commute. The source's U_3 is exactly invariant, so the ordered polynomial defining b_j is invariant as well. Only the associated graded ring is made commutative here.

## 3. The symbols, parity, and the first quotient

The author chooses distinct increasing prime integers d_j>=p and monic irreducibles f_j over k of degree d_j. Frobenius orbits in the degree-d_j field extension give ((p^2)^(d_j)-p^2)/d_j such polynomials, so the family exists at the same fixed p. Their constant coefficients are nonzero.

For e_j=6d_j,

P_j = sum_h c_(j,h) C^(2h)(AB)^(3(d_j-h))

is homogeneous of weight e_j. Over an algebraic closure it is the product of C^2-alpha A^3B^3 over the roots alpha of f_j. Each factor is irreducible: alpha A^3B^3 has odd A-valuation in kbar(A,B), so is not a square; Gauss's lemma applies to the monic polynomial in C. Finite fields are perfect, so the roots are distinct. A factorization over k would choose a Frobenius-stable proper nonempty subset of those factors, impossible by transitivity. Thus P_j is irreducible over k. Its leading C term and nonzero constant-in-C term exclude factors A,B,C. Different weighted degrees make the irreducibles pairwise nonassociate.

The lift

b_j = sum_h c_(j,h) U_3^(2h)(V_1 V_2)^(3(d_j-h))

has exactly this initial form. All summands are invariant. Under the graded sign involution A,B,C -> -A,-B,-C, C has even exponents and AB is unchanged, so P_j is fixed. This checks the later adjoint operation, not merely tame invariance.

The distinction between H_2 and H(2) is addressed in §2.3. The displacement calculation and `op:initialization` show that H(2) lies in H_2 and both have index p^2. Thus H/H_2 is the elementary abelian first-digit quotient. In its group algebra every augmentation element y satisfies y^p=0: commutativity allows the Frobenius power calculation, and every group element has pth power 1. U_3 maps to zero. Each term with h>0 vanishes for that reason, while the h=0 term vanishes because the image of V_1 V_2 is in the augmentation ideal and 3d_j>=p. Hence the exact condition b_j -> 0 in k[H/H_2] is established for every j.

## 4. Initialization, digit matching, and gluing

I compared the preceding quotient condition with the complete proof of `op:initialization`, `op:coefficient-control`, `op:correction-bound`, `op:rank-matching`, and `op:operator`, rather than substituting into the statement that was originally written for U_3.

The normalized first-digit functions (u_g/x)^n modulo x factor through H/H_2. A measure with zero pushforward to that quotient has all their moments zero modulo x for 0<=n<p^2. The first p^2 balanced points have distinct normalized residues in k, so the Vandermonde matrix is invertible over R. Its correction vector lies in xR because the right-hand side does. These corrections kill the moments exactly while preserving b_j modulo x. Equivariant averaging preserves the vanishing and the invariant reduction. The half-weight h_g^(-1/2) is defined in the source range and is 1 modulo x, so it does not change the reduction either.

The later construction uses the killed initial moments, invariant measure, the orbit-index bounds, and the exact p,M inequalities. Its changes at a chosen digit depth can realize the required degree-at-most-M polynomials independently at lower labels; they preserve previous depths, lie in the stated positive x-powers, and converge. The retained-digit argument and finite-field pivot choice do not use that the starting measure was U_3, that its symbol was linear, or that its group weight was 3. The author explicitly retains these operations in §3. It follows that the constructed a_j has reduction b_j, finite crossings, and at least c_j N^beta persistent paired defects for all sufficiently large N, where beta=log_p(2 floor(M/8))>1/3. The positive constant and onset may depend on j.

This is an actual operator with the source's compatible finite-level action. The symbol argument is separate: whenever W>e_j, every x-divisible correction has weight at least W>e_j. Therefore sigma_W(a_j)=P_j. The operator is not redefined when W changes. An infinite family requires no finite common W; each comparison later involves only finitely many operators.

The hypotheses used in `glue:overlap`, `glue:pairs`, `glue:object`, and `glue:global-maps` are precisely these finite crossings, paired defects, and coefficient/action properties. The closed-image proof and discrete paired lattice therefore apply. The finite sum over all D residue shifts gives perfect completion Y_j. The realized open object V_j and the actual fracture pullback give U_j with that completion and finite sections homotopy in each degree. The compact kernel/polar projections have the source's independence modulo x^(qN+1)R.

The class C_fin is thick and closed under retracts: completion is exact and perfection is so closed; the long exact sections sequence preserves degreewise finite-dimensional homotopy under finite cofibers, sums and shifts, and retracts preserve finiteness. This is the target class used later. Nothing requires all of C_fin to lie in Thick(T').

## 5. Microlocalization at a non-coordinate prime

Author §4 gives the actual extension of `obs:microlocal-flat`; merely citing coordinate localization would not suffice. The extension is valid. The set of homogeneous elements outside (P_j) is multiplicatively closed and consists of regular elements. The finite-field completeness/ordered basis gives complete good filtrations on finite modules and closed finitely generated submodules by convergent initial-term subtraction. This supplies strict finite presentations on both sides.

In the truncated Rees ring modulo s^n, a lifted denominator is regular through the s-layers. Commutators are divisible by s, and the iterated commutator ad_d^n(e) vanishes modulo s^n. Expanding it gives the needed Ore relations with sufficiently high powers of d on both sides. These are the operations of the source proof; they use regular homogeneous denominators, not a coordinate equation. Localized finite modules are exact at each truncation, with surjective transitions in fixed degree. Inverse limits and the union over shifts preserve the strict exact sequences here. Identification on finite presentations with tensor by S_j proves both left and right flatness, not just associated-graded exactness.

In the homogeneous localized polynomial UFD, every nonzero homogeneous element is P_j^v times a homogeneous unit, v>=0. For a nonzero right ideal choose an element of minimum initial P_j-order. Every remaining initial term is divisible by that term; right subtraction increases the filtration and the multipliers converge. The same proof on the left makes S_j a two-sided principal domain. This uses completeness in the source microlocal filtration. It is not a claim that P_j can be changed to a polynomial coordinate. The source principal-domain and periodic-splitting consequences apply with this argument: an Ore division ring, finite free-plus-torsion decomposition, and length-one finite free resolutions.

X is outside (P_j), so x becomes a unit. Initial forms outside (P_j) lift to units by the convergent inverse correction. The initial form of a_j is P_j, which has no inverse in the associated graded ring, so a_j has no one-sided inverse; S_j/a_j S_j is nonzero torsion. The source tame finite-free decomposition of Delta[x^(-1)] over E, followed by the two-sided flat microlocal extension, makes E -> B_j=S_j[t,t^(-1)] flat on both sides. Thus the exact functor Psi_j on C_comp has Psi_j(T')=B_j and the specified nonzero torsion homology on U_j. Left and right uses of flatness below are both available.

## 6. The exponent 1/3 at P_j

The first part of `obs:growth` and `obs:newton-basis` uses orbit functions, bounded poles from Weierstrass preparation, and the source balanced valuations. It is independent of whether the operator's symbol is C or P_j. The normalized Newton basis is integral by those valuations and spans by successive evaluation. The factor-replacement estimate shows that residues depend only on the appropriate congruence quotient when N_l exceeds the polynomial degree J=O(n). Taking T=p^s with N_(p^s)>J and N_(p^s)>=p^(3(s-1)) gives T=O(n^(1/3)).

The left-translate annihilation equations bound the residue lattice by the associated graded finite quotient

k[A,B,C]/(P_j,Q,A^T,B^T,C^T),

where Q is the second initial reduction outside (P_j). The ordered finite-group basis gives the three power relations. The change of basis in the first two variables preserves their power ideal because T is a p-power. The equations P_j,Q impose at least the displayed relations; equality of full initial ideals is not required for this upper bound.

If Q is a nonzero constant the quotient is zero. Otherwise P_j,Q is a homogeneous regular sequence: the ambient polynomial ring is a domain and its quotient by the irreducible P_j is a domain in which Q is nonzero. Its Hilbert series is

(1-z^(e_j))(1-z^(deg Q))/((1-z)^2(1-z^3)).

At z=1 the numerator cancels two of the three denominator zeros; the other cube roots give at most simple poles. Thus the coefficients are bounded, with bound depending on the fixed degrees. After imposing the Tth powers, all representatives are spanned by monomials of weighted degree at most (T-1)+(T-1)+3(T-1)=5(T-1). Summing the bounded Hilbert function over those degrees gives O(T), hence O(n^(1/3)). This is the new estimate the proof actually needs. Constants may depend on j,a,b and the bounded lattice L. No step compares constants over an infinite family; a single fixed positive c_j beats this bound because beta>1/3.

## 7. Sides, remainders, and adjoint

In §4.2(a), J is a right ideal, contains a_j Delta, and is right x-saturated. If every reduction were in b_j Omega, writing j=a_j d_0+j_1 x and iterating gives a convergent right expansion and J contained in a_j Delta. That contradicts J S_j=S_j. Thus some reduction lies outside b_j Omega. Repeated initial-symbol right subtraction must terminate outside (P_j), since nontermination would put that reduction in the closed principal right ideal b_j Omega. The resulting b remains in J.

For §4.2(b), x-denominators are cleared on the left. Every subtraction is a left multiple of a_j, and division by x is on the left. These operations preserve annihilation of the prescribed subspace of ker(a_j). Nontermination puts the cleared integral element in Delta a_j, which puts the original Laurent element in S_j a_j because x is invertible there. This is the meaning of the author's convergence conclusion; it does not require commuting x with a_j. Initial-symbol left subtraction then supplies an integral annihilator with symbol outside (P_j). Applied to the span of all relevant vectors at once, it gives one fixed annihilator, not a sequence depending on N.

The constant-term pairing gives on c delta_g the integral adjoint

g^(-1)(c) [x (g^(-1)x)'/(g^(-1)x)] delta_(g^(-1)).

The change-of-variable factor is essential. Modulo x it is group inversion, so on gr Omega it sends each of A,B,C to its negative. By the parity already proved it preserves P_j and sends a symbol outside (P_j) to another outside it. The growth estimate therefore applies to the two adjoint integral operators. Neither the author nor this review needs an action of S_j on Laurent functions, which would not follow just from the construction of S_j.

## 8. The enlarged ordinary-to-dual ghost implication

This is checked with its full quantifier: **for every P in C_fin and every global g:U_j -> P**, ordinary homology vanishing after Psi_j implies dual homology vanishing after Psi_j, as in (5.1).

Precompose the completed map on m_j[r] with its free cofiber inclusion and call the class h. Before microlocalization its right annihilator intersects Delta in a right x-saturated ideal J_h containing a_j Delta. Clearing denominators on the right identifies the Laurent annihilator. The cyclic module injection into target homology stays injective under tensor to S_j by left flatness. The assumed ghost kills its generator after that tensor, hence J_h S_j=S_j. The right remainder statement gives the integral b with initial reduction outside (P_j).

The equations h a_j=h b=0 are zero maps from free shifts. Derived tensor with the Laurent representation preserves them without a flatness assumption on that representation. The tame projection is applied after the tensor operation and is E-linear; no Delta-linear tame projection is asserted. The resulting overlap map annihilates the two projected operator images.

For a compact open C_P, continuity bounds the pullbacks of functionals annihilating C_P inside one lattice x^(-L)R under CT_x. They solve both adjoint equations. The preceding growth bound therefore limits the rank of polar images up to N modulo C_P by O(N^(1/3)). The full `complete:topology` proof uses degreewise finite sections homotopy for this topology and discrete lattice, and perfect completion for the finite-module realization. It does not assume a particular expression for P in terms of T'. These are exactly the hypotheses available for every member of C_fin.

Enlarge C_P by the image of the compact kernel lattice. A discrete subspace meets this compact open in finite dimension. Applying the rank bound to the c_j N^beta source pairs then leaves a killed subspace of dimension at least c_j N^beta-O(N^(1/3)); a fixed finite-dimensional error is absorbed here. Its kernel projection has the same independence modulo x^(qN+1)R by the source pairing construction. This proves the quantitative statement (5.2) for these targets, not only for Thick(T').

For each pre-extension perfect-module dual class theta, its composite with the free inclusion is a coefficient c with c a_j=0. The coefficient algebra embeds in a domain, so c=0. The composite factors through the connecting map as b' partial_r, with b' Laurent invariant after the stated degree/t normalization. The other residue components do not supply a second kernel term in that residue. The composite annihilates every projected killed subspace. If b' were outside S_j a_j, the left remainder lemma would give a single integral second annihilator of their entire span. The O(N^(1/3)) joint-kernel estimate contradicts c_j N^beta-O(N^(1/3)) as N tends to infinity. Thus b' lies in S_j a_j. Being a left multiple, it kills the connecting map after extension with the correct module convention.

Finally finite-cell evaluation and retracts identify the extended dual of a perfect right E-module with B_j tensor_E RHom_E(-,E). Right flatness commutes this tensor with homology. Every dual class is a finite sum of coefficients times pre-extension classes theta, so their proved zero composites give all of dual homology vanishing. The target assumptions have been accounted for at every step. There is no unproved appeal to generation by T' left in (5.1).

## 9. Conjugates and the finite-tower obstruction

The base charts, formal law and scalar central subgroup descend to F_p. Their degree-two field extension therefore gives an exact semilinear involution tau preserving T', finite sections homotopy and completion, compatible with r^*. It fixes the chart variable x and applies Frobenius to group digits, preserving H(i), Gamma_s and Lambda. On H(2) the first two ordered coordinates are divisible by p; their difference terms have weight at least p>3. Consequently the leading term of tau(U_3) is a nonzero scalar times C. The first-degree plane is carried isomorphically to itself. Applying tau twice verifies the inverse filtration assertion. Thus tau preserves every W-filtration used here, and tau(P_i) is homogeneous irreducible of weight e_i.

Fix j and any finite F not containing j, and choose an integer W larger than e_j and every e_i for i in F. Since their degrees differ, neither P_i nor tau(P_i) is associated to P_j. Hence a_i and tau(a_i) become units in S_j. Psi_j kills both U_i and tau U_i for i in F, but sends

T_F = T' plus direct sum_(i in F)(U_i plus tau U_i)

to B_j. T_F lies in C_fin; H(Psi_j U_j) is nonzero torsion. This deliberately retains both Galois conjugates. There is no requirement that tau(P_j)=P_j and no missing same-degree separation claim.

The finite-tower argument in §6 reproduces `rew:obs:tower-criterion` and its normal form, with the enlarged implication from §8 of this review. Over the two-sided principal domain, the source's length-one free resolutions split perfect D-periodic modules into free shifts and a torsion-homology summand. Ordinary thick expressions are retracts of finite towers with finite sums of shifts of T_F as layers: cones concatenate by octahedra and retract complements can be carried to the end.

Induct backwards through such a tower. Vanishing of dual homology at the next tail makes its projection to every free shift a zero derived map, so the map lifts to the fiber of that free projection. The fiber has triangle F_free -> Z -> L with H(L) torsion. Its homology sequence injects H(F_free) into H(Z), since the preceding map is torsion-to-free. Ordinary vanishing at the next tail forces the image from H(Psi_j U_j) into this free submodule. It is zero because that source is torsion. The enlarged (5.1) restores dual vanishing at the preceding tail. At the initial retract insertion the resulting homology vanishing contradicts its nonzero split injection. This proves exactly (6.1) for every finite F, including the empty set.

## 10. Relative transfer, both nilpotent triangles, and separable descent

The empty-set instance gives all three hypotheses of `transfer:criterion`. Set F_i=e_*r^*U_i, realize i_*F_i as Z_i under the stipulated homology-compatible triangulated comparison, and set X_i=tau_(>=0)Z_i. This gives the connective p-complete, degreewise finite p-group and localization properties used to begin §7. No monoidal comparison is invoked.

Suppose X_j belongs to Thick(b_p,X_i:i in F) for a finite F not containing j. Exact L_2 and the source's actual standard-generator identification transport this to i_*F_j in Thick(T_Zp,i_*F_i). Derived reduction gives R_j in Thick(T_0,R_i), where R_i=Li^*i_*F_i and the source triangle is

F_i[1] -> R_i -> F_i -> F_i[2].

Its degree-two boundary delta_i is nilpotent uniformly on shifts. The author does not infer this just from nilpotence on a single object. Perfect completion puts completed r^*U_i and e_*r^*U_i in the finite closures specified by `transfer:central-completion`. On complete generators the boundary is zero by the periodic sparsity, on the pure open it is zero, and the source thick-nilpotence/fracture argument gives the required uniform statement on F_i. These hypotheses depend on perfection and the actual fracture square, not on the symbol C or an assumption U_i in Thick(T').

There is a second issue for natural transformations not assumed shift-compatible. The proof explicitly uses the stronger source lemma: the cone at A[h] is a shift of B(A[h]) for an exact functor B. Exactness puts these cones in Thick(B(A)); octahedra put the cone of any successive power there. A uniformly vanishing power has split cone with a shift of A as a retract, hence A lies in Thick(B(A)). Here B=Li^*i_* and its triangle supplies the cone hypothesis. Thus F_j lies in Thick(R_j), and consequently in Thick(T_0,R_i:i in F). This checks the precise source nilpotence interface.

For the finite separable extension, k tensor_(F_p) k is k times k with the two embeddings. Its decomposition commutes with differentials, twists and groupoid maps, so it gives the exact natural identity e^*e_*G = G direct-sum tau G on the category in question. It is not merely an equality on homotopy or K-groups. Thus r^*U_j is a retract after e^*, and applying the exact Q=Rr_* gives Qr^*U_j in Thick(T',Qe^*R_i).

Each R_i lies in Thick(F_i) by its triangle, without any splitting assumption. Retaining both embeddings now yields

Qe^*R_i in Thick(Qr^*U_i,Qr^*tau U_i).

The central comparison triangle for V has terms V, Qr^*V, V[-1], so Qr^*V lies in Thick(V). Its boundary epsilon on U_j is nilpotent by the same complete-generator/open/fracture argument, and the exact-cone uniform lemma gives U_j in Thick(Qr^*U_j). Combining these two directions gives U_j in Thick(T',U_i,tau U_i:i in F), contradicting (6.1). Neither the reduction triangle nor the central triangle was silently split.

Finally, a member of the ordinary thick closure of an arbitrary set has a finite expression, involving only finitely many generators. Equivalently the union of the thick closures of finite subsets is itself thick and contains the generating set. Thus the contradiction for every finite F proves the asserted nonmembership against **all** other family members. No transfinite operation or compactness of these spectra in the ambient category is assumed.

## 11. Exact fp-type and the canonical localization maps

The proof fixes the same standard Araki quotient throughout. `comp:bp-comodule`, `comp:standard-cohomology`, and `comp:generators` identify its image; the review does not replace it by an arbitrary multiplicative form of BP<2>.

Each Z_j is E(2)-local with degreewise finite p-primary homotopy. Smashing its connective cover with a finite type-three spectrum gives finite total homotopy by the source's finite-duality and bounded-range argument. The upper bound comes from the E(2)-acyclicity of that finite spectrum and the bounded-above negative tail, while the lower bound comes from connective bounded-below input and finite cells. Mahowald-Rezk Proposition 3.2 supplies finite presentation over the Steenrod algebra from this finite-total test in the stated bounded-below, p-complete setting. Its Proposition 3.5 and the Section 7.2 discussion are compatible with the source's usage; no Brown-Comenetz conclusion is added.

If X_j had fp-type at most one, the final Lee-Pstragowski height-one classification used in `scope:exact-height` would put it in the ordinary thick closure of the completed standard BP<1> generator. The source identifies that generator as the completed v_2-cofiber of b_p, so it lies in Thick(b_p). This contradicts the empty-set nonmembership. Hence the type-two finite-total test fails and the exact fp-type is two, as frozen.

The two equivalences are the canonical comparisons, not merely existence of abstract isomorphisms. The source `scope:telescopes` proof applies objectwise with E(2)-local Z_j and finite p-primary homotopy. The negative tail of the connective cover is built as the indicated filtered colimit of bounded ranges of finite p-group Eilenberg-Mac Lane pieces, giving the source L_2^f-acyclicity argument. Together with its restricted E(2)-local comparison this proves L_2^f X_j -> L_2 X_j. The source's second localization argument gives L_(T(2)) X_j -> L_(K(2)) X_j under the same hypotheses. None of these steps uses the special source symbol or a global telescope theorem for arbitrary spectra. The original prime range supplies the triangulated comparison bounds.

The primary comparison also respects its limitations. Pstragowski v2 Corollary 6.9 and Appendix B give the triangulated interface, while Remark 6.6 warns against treating the constructed equivalence as symmetric monoidal. The complete canonical source contains the operative comparison argument actually stipulated here. Barkan's stronger tensor-triangulated result is unnecessary, and no unread Barkan proof is used to patch a gap. Hahn-Wilson's multiplicative-form hypotheses and redshift statements do not replace the fixed b_p identification.

## 12. Consequences and exclusions

For I contained in J, inclusion C_I contained in C_J is immediate from the generators. If I is not contained in J, choose j in I minus J. Inclusion would put X_j in C_J, a subcategory of Thick(b_p,X_i:i different from j), contradicting item 3. Thus the asserted map of power sets is an order embedding. The power set of the positive integers has continuum cardinality, yielding continuum many such distinct subcategories.

The class of bounded-below p-complete spectra of fp-type at most two is preserved under the finite operations defining these ordinary thick subcategories, by the source/Mahowald-Rezk fp criterion; all generators lie in it. There is no common lower-connectivity bound imposed on the whole category and no arbitrary infinite sum closure.

If C_N had finitely many thick generators among its objects, each of those objects would use b_p and only finitely many X_i. The union F of these finite supports would give C_N contained in Thick(b_p,X_i:i in F). Taking j outside F contradicts item 3. This concerns this C_N and its own finite generating sets, not the entire fp category.

The proof asserts no explicit numerical threshold, small-prime extension, other height, other BP form, classification of all thick subcategories, finite-generation result for the entire fp category, tensor-ideal statement, or telescope/Picard/duality/K-theory consequence beyond the two frozen canonical comparisons. These exclusions are preserved.

## 13. Review disposition and limits

All new operations needed for the unchanged theorem have been checked: arbitrary W, invariant irreducibles and first-quotient vanishing, the actual operator initialization and digit construction, gluing, two-sided non-coordinate microlocalization, the cubic-root regular-sequence estimate, both sided remainder arguments and adjoint, the full C_fin target quantifier, conjugates and finite towers, uniform-on-shifts relative transfer, exact separable descent, both central/reduction triangles, exact fp-type and both canonical comparisons, and the infinite-family consequences.

**Unresolved necessary corrections: none. Essential uncompleted mathematical verifications: none, under the stipulated source truth. Verdict: PASS at the entire unchanged frozen scope.** The detailed primary/access/isolation limits are evidence limits, not claims that unread material has been verified, and no unused inaccessible or partially read reference is used as favorable evidence. This is not a contribution assessment or an adoption of the parent questions as defects. Parent alone integrates and adopts dispositions and counts.
