# T019S59 — author proof of the unchanged two-prime section target

**Status:** complete author argument, conditional on the stipulated pinned source theorems and on the precisely cited classical primary results below. It has not passed independent proof or contribution gates. The frozen `original-scope.md` is copied byte-for-byte from r59; its historical unresolved status is preserved. Its SHA256 is 22e7466e2699457a0ee39e31f5ac1b982527f1a7b9115b2fa1c3bc7377a73d95.

**Claim.** Let p be any prime, ell any odd prime different from p, k/Q_p any finite extension, and X/k any smooth proper geometrically connected curve of genus at least two. Put Sigma={p,ell}, Delta=pi_1(X_bar k), and Pi_X^Sigma=pi_1(X)/ker(Delta -> Delta^Sigma), retaining the full G_k quotient. Then

    X(k) -> Sect(Pi_X^Sigma -> G_k)/Delta^Sigma

is bijective. Sections are continuous; conjugation is geometric. No good-reduction, rational-point, finite-extension or full-section-lift hypothesis is imposed.

## 1. Field and group conventions

Write K=k(X), K0=bar k(X), and fix a separable closure Ksep containing bar k. Let B be the compositum of all finite Galois extensions of K0 with Sigma-group Galois group. It contains bar k and is Galois over K. Let E_X be the compositum of finite étale geometric covers of X whose Galois closures have Sigma-group group, again with all constants and embeddings. Then Gal(E_X/K)=Pi_X^Sigma, and E_X⊂B. Set G_B=Gal(B/K). These are geometric prime restrictions, not a restriction on the arithmetic quotient G_k.

Finite Sigma-groups are closed under subgroups, quotients, products and extensions. If L/K0 has Sigma-order normal closure and V/L is finite Galois with Sigma-group group, its normal closure over K0 still has Sigma-group group: base change to the normal closure of L, take the finitely many conjugates of V, and use a subgroup of their product followed by an extension. The same argument applies to connected components of finite torsors. Thus towers of p- and ell-power layers, and arbitrary finite Sigma-group covers, remain in B. We never infer Galois-prime control solely from the degree of a non-Galois cover.

The maximal geometric pro-Sigma quotient of any finite section neighborhood Y is the associated open geometric subgroup of Pi_X^Sigma. For this standard open-subgroup property, take any finite Sigma quotient of that open subgroup before completion and intersect its finitely many conjugate kernels. The resulting normal closure has Sigma-group quotient by the same extension/product argument. Therefore all of its Sigma-covers are represented in the original tower.

## 2. Rank-one completion of the restricted tower

Fix any real-valued rank-one norm of K extending |p|=p^(-1), prolong it to Ksep, and work inside its completed field. Put H=completion(E_X) and Omega=completion(bar k)⊂H. We prove

    B ⊂ H

for the specified embeddings, not merely an abstract isomorphism of fields.

The source's local normal form, all-sheet patching, point-transfer lemma, annular-unit estimates, arbitrary-order Jacobian collar construction and horizontal-closure lemma are used at their printed interfaces. The only extra monodromy input at the first root stage is proved in `cyclic-collars.md` from the source construction, Sigma-RNS, and ABBR7.4(2).

Let L be the compositum of those finite Galois Sigma-extensions F/K0 whose horizontal ramification indices divide ell. We first show L⊂H. For such an F, take its Galois cover C -> X_bar k with group Gamma. Choose small branch disks avoiding the fixed H-valued generic point, exactly as in source `03-patching.tex`. The prime-controlled collar lemma gives a finite étale Y -> X_Omega with Sigma-order normal closure and an ell-th root of each branch coordinate on every inverse collar. Over the exterior the pulled-back C-cover is a Gamma-torsor, split on the whole overlap. Glue this to trivial Gamma-torsors over the inner-disk inverse images, choosing Gamma-equivariant trivializations. Disjoint inner disks give no triple-overlap issue.

The resulting finite étale Gamma-torsor on Y algebraizes by the same GAGA argument as the source. A connected component V is Galois over Y with subgroup monodromy H0≤Gamma. Its normal closure over X is a Sigma-cover by §1, and V -> X is finite étale. Proper base-extension invariance descends it from Omega to bar k. Thus its function field embeds into E_X⊂H. The source's point-transfer lemma embeds F in H over K0 at the fixed H-valued point. Since F/K0 is normal and its specified copy is inside the common completed algebraic closure, the image is precisely that copy of F. Hence F⊂H and L⊂H.

Now take an *arbitrary* finite Galois Sigma-extension F/K0, with Galois group Gamma, and its curve C. At a branch point b its inertia order e divides |Gamma|, so the least common multiple m_b of the indices above b is a Sigma-integer, possibly containing arbitrarily large p- and ell-powers. The source's `05-arbitrary-roots.tex` works for every such m_b: choose D_b>v_p(m_b)+1/(p−1) and a_b>2D_b. Its auxiliary curve Z -> P1 is cyclic of degree ell and its upper cover is pulled back from multiplication by m_b on J_Z. The latter is a torsor under J_Z[m_b], an abelian Sigma-group. Therefore the auxiliary connected cover Q -> P1 has Sigma-order normal closure by §1, even though it need not itself be Galois. Its horizontal ramification indices divide ell, exactly as in the source.

Pull it back by T=t_b/beta_b, normalize a component, and form the compositum W for all branch points. The source proves the collar roots on *every* inverse sheet with their actual middle-collar estimates. The normal closure of W/X has Sigma-order, and all its horizontal indices divide ell. Equivariantly patch the Gamma-torsor C x_X W over these collars as in the previous paragraph, yielding a connected finite étale V -> W with subgroup monodromy. Then V/X has Sigma-order normal closure. Since V -> W is étale, the horizontal indices still divide ell; the source's horizontal-closure lemma preserves this after normal closure. Thus bar k(V) embeds in L⊂H. Point transfer embeds F into H, and normality identifies the specified copy.

Every element of B lies in one such finite Galois Sigma-extension. Taking their union proves B⊂H. This deals with the entire geometrically pro-Sigma birational extension, not only the horizontal-degree-ell layer. There is no assertion that all of Ksep lies in H.

For the chosen rank-one valuation, restriction

    D(B/K) -> D(E_X/K)

is consequently an isomorphism of profinite groups. Surjectivity is the usual prolongation-transitivity argument for a Galois extension: lift an automorphism and correct its valuation by an element of Gal(B/E_X). For injectivity, an element of the kernel fixes E_X pointwise and preserves the normalized rank-one norm, hence acts continuously on its completion H and fixes H. As B⊂H, it fixes B. The inverse is continuous by compactness and Hausdorffness.

## 3. Primary quotient localization, with its exact hypotheses

Mochizuki's March 3, 2011 *Comments on a Combinatorial Version of the Section Conjecture and the Main Theorem of Pop–Stix*, (*PTS) and (5), treats an arbitrary complete discrete valuation field of mixed characteristic, a prime set Sigma containing ell≠p, and a proper hyperbolic curve. If the ell-adic cyclotomic image is open, quotient sections have compatible fixed stable vertices or edges in the restricted tower. His May 2, 2011 *Comments on Valuations Associated to Systems of Vertices/Edges and the Main Theorem of Pop–Stix*, (*val) and its full proof (1)–(2), constructs compatible section-fixed valuations of the function fields in that same tower.

The openness assumption holds for our k. If its residue field has q elements, its ell-adic cyclotomic image contains the closed subgroup generated by q. The integer q>1 cannot be an ell-adic root of unity: q^n=1 in Q_ell would be an equality of rational integers. After a finite power it lies in the principal-unit group, where the ell-adic logarithm is nonzero. Its closed Z_ell-span is open there, hence the cyclic closure is open in Z_ell^×.

We use the precise alternatives in the May proof. A compatible system of divisorial vertices, or its finite limit valuation, yields a real-valued rank-one valuation extending the fixed valuation on k. Irrational node rays likewise give such monomial rank-one valuations. If the diverging-value prime ideal has height one, the alternative is a compatible system of horizontal closed points. The rational-ray case is reduced there by blowups to the same alternatives. All constructions are invariant under the section image. Thus the section lies either in a horizontal point decomposition group of the restricted tower or in the decomposition group of a rank-one extension of the p-adic norm. These primary results already provide the restricted localization left open in r59; r59's proposed adaptation of Pop–Stix is unnecessary here.

In the horizontal alternative, let x be the closed point of X. The image of its decomposition group in G_k is G_{k(x)} up to conjugacy. Since it contains a section of all G_k, k(x)=k. In the proper étale tower the horizontal inertia is trivial, so its decomposition group maps isomorphically to G_k, and the section is its point section. In particular X(k) is nonempty.

In the rank-one alternative, §2 lifts the section through the decomposition-group isomorphism to a continuous section G_k -> G_B.

## 4. Pop's exact elementary quotient and rational-point existence

A birational Sigma-section t:G_k -> G_B implies X(k)≠∅ as follows. Put k'=k(mu_p), K'=k'(X). This is a finite Galois constant extension. Since bar k and K0 are unchanged, B is also the maximal geometrically pro-Sigma extension for K'. Restrict t to G_{k'}.

For any profinite group G put G^(0)=G and G^(i+1)=closure([G^(i),G^(i)] (G^(i))^p). Write G'=G/G^(1), G''=G/G^(2). These are Pop's maximal elementary p-abelian and elementary p-metabelian quotients. Every homomorphism respects this series, and a section induces sections of both quotient maps. These are precisely the functorial assertions read in Pop 2007 §2(A).

The fields K'_1=K'(p-th roots of K') and K'_2=K'_1(p-th roots of K'_1) lie in B: their Galois group over K' is pro-p, hence every finite geometric subextension has p-power degree. Consequently N=ker(G_{K'} -> Gal(B/K')) is contained in G_{K'}^(2). A surjective continuous homomorphism carries each closed elementary p-derived subgroup onto the corresponding subgroup of its target, by induction using commutators, p-th powers, and compactness. Hence the elementary p-abelian and elementary p-metabelian quotients of G_{K'} and Gal(B/K') are canonically isomorphic. This establishes the quotient identification, rather than assuming a birational section descends through an arbitrary constant quotient. The analogous constant quotients are the G_{k'} elementary quotients.

Applying the elementary quotient functors to t|G_{k'} yields a section of G_{K'}'' -> G_{k'}'' and its reduction s':G_{k'}' -> G_{K'}'. Thus s' is *liftable* in the exact sense of Pop's Theorem A (MPIM 2007/102). Its hypotheses hold: k'/Q_p is finite, mu_p⊂k', and X/k' is smooth, proper, geometrically integral. The theorem supplies a unique x'∈X(k') whose elementary point section is s'.

This point descends to k. For sigma∈Gal(k'/k), take a lift in G_k and conjugate by its image under t. The subgroup G_{k'} is normal, and t(σ h σ^(-1))=t(σ)t(h)t(σ)^(-1). Passing to the characteristic elementary p-derived quotients shows that the transformed section corresponds to the same restricted section under the natural sigma-semilinear identification. Functoriality of point sections sends x' to sigma(x'). Pop's uniqueness therefore gives sigma(x')=x'. Galois descent gives x∈X(k).

Only existence is required here. We do not claim that the entire birational Sigma-section belongs to the horizontal decomposition group selected by Pop's elementary quotient, nor infer that its fixed field has the full absolute Galois or henselian properties used by the source's different endgame.

## 5. Every section is geometric

Apply §§2–4 to every finite neighborhood Y/k of the original quotient section s. Such Y is smooth proper geometrically connected and has genus at least two by étale Riemann–Hurwitz. By §1 its lifted section is a section of Pi_Y^Sigma. Thus Y(k)≠∅.

Each image of Y(k) in X(k) is nonempty and closed, since Y is proper and k is a local field. The images have the finite intersection property: intersect finitely many open subgroups containing s(G_k) to obtain a common finite neighborhood. Compactness of X(k) gives a common point x.

For completeness this criterion identifies the section, not merely a point. For every finite neighborhood its fiber over x has a k-rational point. A finite collection of pointed fiber compatibility requirements is satisfied by a rational point of a common dominating neighborhood. The fibers are finite, so compactness yields a compatible G_k-fixed point in the inverse limit of all neighborhood fibers. This is the usual section decomposition pro-cover, whose fundamental subgroup is s(G_k). A compatible rational point means its decomposition group is a conjugate of the point-section group at x and is contained in s(G_k). Both map isomorphically onto G_k, so they agree. Hence s is geometrically conjugate to the section of x.

## 6. Injectivity

Mochizuki, *The Local Pro-p Anabelian Geometry of Curves*, Theorem C = Theorem 19.1, states that for every sub-p-adic field K and hyperbolic K-curve the map from K-points to geometrically pro-p section classes is injective. Its notation explicitly retains the full arithmetic G_K. Finite k/Q_p is sub-p-adic. If two k-points have the same section class in Pi_X^Sigma, project to the geometrically pro-p quotient; their pro-p section classes agree. The cited theorem gives equality of the points.

The actual Theorem19.1 proof was read: it uses the diagonal-complement family and pro-p anabelian isomorphism, not the insufficient restriction of the source's all-n Jacobian Kummer test. Its earlier anabelian theorem is credited as a classical input; its entire long proof was not re-audited.

Together §§5–6 prove the unchanged author claim. This does not by itself establish SUBSTANTIAL contribution or campaign acceptance.
