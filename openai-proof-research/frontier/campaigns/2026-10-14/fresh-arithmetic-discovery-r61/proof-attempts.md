# T031C61: two full-target proof attempts

Historical exploratory derivation, superseded by the actual Uchida 1981 corollary read after scope freeze. The full scope in scope.md is retained and is CLASSICAL_PRIMARY_PAID, as explained in primary-disposition.md. Statements below about an unpaid step or an unresolved endpoint describe these two attempted routes only, not the final literature status. None of the supporting reductions below is nominated. Author: Myeongjin Kang; original prose CC BY 4.0.

## 1. What the open theorem already pays

Write P_F=Gal(F^sol/F). For every finite intermediate M/F, F^sol is also M^sol: take a solvable normal closure of M/F and then all conjugates of a finite solvable extension of M. The compositum has solvable Galois group. Thus open subgroups of P_F have the same form over number fields.

An injective endomorphism with open image is already an automorphism by the pinned source031 main theorem (indeed the older isomorphism theorem suffices). Its inducing embedding j:F^sol→F^sol maps F into F. That restriction is an automorphism of the number field F. Extend it to an algebraic closure; the maximal solvable extension is invariant under such an extension. Equivalently apply this to the inverse automorphism of F. Hence j is onto and its induced group map is an automorphism. This is source-paid, not the new target.

## 2. Normalizer route

The following regular Kummer observation is classical and adapts exactly the source's quotient-amplification construction; it is not a new arithmetic estimate.

**No commuting normal factors.** P_K, for any number field K, has no pair of commuting nontrivial closed normal subgroups A,B.

Choose a finite solvable Galois quotient R1 detecting nonidentity elements a∈A,b∈B and containing K(mu_3). Choose a completely split finite prime and an element with valuation one at one prime above it and valuation zero at its other conjugates. The conjugates have independent cube classes by their valuation vectors. Adjoin their cube roots. This gives a further quotient R with kernel V isomorphic to the regular F_3[R1]-module. More precisely the dual Kummer module has a cyclotomic twist, but a twist of the regular representation by a one-dimensional character is isomorphic to the regular representation (rescale the basis indexed by g by the character of g). No splitting of R→R1 is needed.

Let g,h∈R1 be the detected images. Normality gives [b,V]⊂B_R; commutation of A_R and B_R then gives (g−1)(h−1)V=0. But left multiplication by gh−g−h+1 is not zero in F_3[R1] when g,h≠1. If gh≠1, its coefficient at 1 is 1. If gh=1, its coefficient at 1 is 2, still nonzero. This contradicts regularity. Notice that characteristic three avoids the characteristic-two coincident-involution cancellation. This proves the observation.

**Supporting reduction.** If alpha is as in the full target and H=alpha(P_F) has open normalizer N in P_F, then alpha is surjective.

The isomorphism theorem for solvably closed extensions gives center(H)=1 and Out_cont(H)≅Aut(F), a finite group. To see the assertion about the center, an element acting trivially by conjugation and the identity field map both implement the same group automorphism, so uniqueness forces that element to be 1. For the outer group, implementing field automorphisms preserve F, and those fixing F are precisely H.

Conjugation by N acts on H. The inverse image N0 of the inner automorphisms is HC, where C=C_N(H). Both H and C are compact, so HC is closed. Its index in N is finite because Out_cont(H) is finite. A closed finite-index subgroup of a profinite group is open (its complement is a finite union of closed cosets). Thus N0 is open in P_F. H,C are commuting closed normal subgroups of N0, and N0=P_K for a finite intermediate K. The observation forces C=1, since H is nontrivial. Hence H=N0 is open, and section 1 finishes.

**Unpaid step.** Nothing here proves that N is open. A closed subgroup need not have open normalizer. The source normalizer-extension lemma starts with an already open image A and invokes the isomorphism theorem over its finite fixed field. Replacing A by H with an infinite fixed field is outside that theorem's hypotheses. The intrinsic automorphisms of H control N/H but do not enlarge N inside the ambient group. Iterating normalizers supplies no reason that this tower reaches an open subgroup. The full target therefore remains unresolved; the open-normalizer conclusion is not a replacement.

## 3. Character route: an actual forced kernel

Fix an arbitrary rational prime ell. The source's equation (character-class-field), using the actual logarithmic image of units rather than Leopoldt, gives

    r_2(M)+1 ≤ dim_Qell X_ell(M) ≤ [M:Q],
    X_ell(M)=Hom_cont(P_M,Q_ell).

Indeed the local unit space has dimension [M:Q], while the global unit image has rank at most r_1(M)+r_2(M)−1. The upper bound needs no lower bound on the unit image.

Suppose a full-target counterexample alpha has infinite-index image H. Choose an open normal subgroup N of P_F with fixed field L containing F(i), and such that c=[P_F:HN]≥3. Such N exist: the numbers [P_F:HN] are unbounded as N shrinks, since H is closed of infinite index. Put U=alpha^−1(N), let M be its fixed number field, and set

    d=[F:Q],  t=[P_F:N],  h=[P_F:U]=[H:H∩N].

The equality t=ch is the finite coset formula, and [L:Q]=dt, [M:Q]=dh. L is totally imaginary. Pullback along alpha|_U gives

    J: X_ell(L) → X_ell(M).

Consequently

    dim ker J ≥ dt/2+1−dh = dh(c/2−1)+1 > 0.

This is a statement about the actual number-field character spaces associated with a putative counterexample, not an arbitrary profinite example. It shows that group injectivity is compatible only with failure of character injectivity at these levels. In particular the source's Frobenius-generation and final-identification arguments cannot simply drop openness: their required injective pullback is necessarily false for a hypothetical infinite-index image. Increasing the target quotient aggravates this loss.

Take nonzero x in this kernel. It vanishes on H∩N. By the source's Frobenius-detection proposition (i), x(Fr_v) is nonzero at all but finitely many absolute-degree-one primes v of L away from ell. On D_v⊂N the character is unramified and equals x(Fr_v) times the ell-component of the residue exponent. It follows that, for all but finitely many such v,

    the unramified Z_ell projection of H∩N∩D_v is zero.

This holds for every prolongation of v: conjugation by N preserves the character. Thus any nonopen embedding must miss nonzero ell-adic Frobenius exponents at almost every degree-one target prime in this precise sense. Merely saying that injectivity preserves nontrivial tame inertia does not contradict this conclusion: inertia and the unramified quotient are different groups, and ambient decomposition containment has not been established.

**Unpaid step.** An intrinsic characterization strong enough to send source local groups into ambient decomposition groups, with nonzero ell-adic residue exponents at infinitely many degree-one target primes, would contradict the displayed obstruction and prove openness. Uchida's local-correspondence theorem in the source assumes openness before giving cofinite target coverage. Hoshi's actual Lemma 1.3 assumes two groups already of mixed-characteristic local-field type, equal residue characteristic, and a finite-quotient Sylow-surjectivity condition; mere nonzero inertia is insufficient. None of these assumptions has been supplied for alpha(D_v) in the ambient global group.

## 4. Endpoint

The attempts isolate two genuinely missing interfaces: openness of the image normalizer, or sufficient ambient local prime coverage without openness. The character calculation explains exactly why a direct replay of the source proof fails. Neither the calculation nor the normalizer reduction proves or disproves T031C61. No conditional or restricted theorem is offered for campaign acceptance.
