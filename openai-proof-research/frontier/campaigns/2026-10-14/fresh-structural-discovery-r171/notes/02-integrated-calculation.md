# Integrated calculation: exact periods, real translations, and quantitative limits

PREFREEZE feasibility calculations. No theorem is frozen or nominated. These deductions deliberately integrate the stronger actual operations; writing them out does not establish substantial contribution or literature novelty. The fixed tile obtained by replacing the source's final geometry with the primary exact lift is distinguished throughout from the source's literal marked-point tile.

## 1. A period in one column already fails

Keep the source p>200, N=p², alphabet F_p minus zero, and line rule. Let W have every column nonconstant. Fix ONE column n₀ and suppose it has a nonzero integer period M; change its sign to make M positive. The source affine approximation gives H(n,m)=An+Bm+C with B nonzero. Choose m so that H(n₀,m) and H(n₀,m+M) are nonzero. Their equal W-values imply BM=0 modulo p, so p divides M. This argument requires no periods in other columns.

Choose u,v with A+Bu=C+Bv=0 modulo p and set Wtilde(n,m)=W(n,m+un+v). The line rule and nonconstant-column condition survive, and column n₀ still has period M. Its approximation is Bm. The source's full second-digit calculation, using n=n₁+pk along m=n-n₁, proves that W₁(n,m)=Wtilde(n,pm) again has every column nonconstant. Column n₀ now has period M/p. Iterate at that same fixed column. The positive integer M would be divisible by every p-power, impossible.

Thus no individual column has a nonzero period. This is a direct use of the source rescaling proof; the primary full p-adic classification independently supplies the same conclusion. It is not a new strong-aperiodicity mechanism.

## 2. All stabilizers of the common graph vanish, including torsion

Write G=Z² × V and A for ANY common solution of the source system. Let h=((a,b),v) stabilize A. With e=|V|, eh=((ea,eb),0) also stabilizes A. Translation by this element preserves each low input k. Uniqueness of graph points then forces equality of useful functions and active sets at x and x+(ea,eb). Hence decoded column n has period e(b+na). Section 1 implies b+na=0 for every n. The columns n=0 and n=1 alone give a=b=0. Every possible period therefore lies in V.

The finite-coordinate part of H₀ is

    H₀ = C_D × product_i (r_i C_(r_i²) × C_(a_i) × C_(b_i)),
    |H₀| = D product_i r_i a_i b_i,
    |V| = D product_i r_i² a_i b_i,
    D=p⁴.

All prime factors of |V| divide |H₀|. Since V is cyclic, its unique subgroup of order ℓ is in H₀ for every prime ℓ dividing |V|. Any nonzero subgroup of V contains an element of some prime order ℓ, and therefore meets H₀ nontrivially. But a nonzero period in H₀ takes a graph point to a different point in the SAME base fibre, contradicting A ⊕ H₀=G. Thus

    Stab_G(A)={0}.                                             (1)

This uses the high cyclic coordinate C_(r_i²), not a fictitious split C_(r_i)². In a general finite abelian group the subgroup-intersection assertion need not hold. The actual cyclic arithmetic is essential to this short deduction, and already supplied by the source.

## 3. Stacking preserves the trivial stabilizer

Let q be the fresh stacking prime, Fst the source stack, and B any tiling set in G × C_q. The exact fibre argument gives projection injective on B and A=pr(B) a common solution. If h stabilizes B, then pr(h) stabilizes A, so pr(h)=0 by (1). Then h lies in the C_q kernel. A nonzero such shift would give two elements of B over the same projected point. Hence h=0. Under the CRT identification G × C_q = Γ=Z² × C_Q,

    Stab_Γ(B)={0} for EVERY tiling by F.                        (2)

Existence is the source's explicit graph followed by A × {0}. No assertion that every stacked graph has constant height was needed. Its possible height choices do not defeat (2). The stacking construction is already finite and effective; merely replacing its probabilistic existence argument by exhaustive finite search adds no new operation.

## 4. Exact primary lift, rather than a periodic-only decoder

Apply the actual primary quotient theorem to π:Z³→Γ, π(x,y,z)=(x,y,z mod Q), with L=ker π=Q Z e₃. It supplies an integer scale a≥2 and a finite tile E such that, after translating a nonempty tiling set to contain zero, EVERY tiling set is

    C=a π⁻¹(B),                                                (3)

for a Γ-tiling set B of F. Conversely all such lifts tile E. This is the equality of tiling spaces in the primary theorem, proved through the two rigid component types and their L-invariant partition of the grid. The source's own marked-point shape only proves its grid assertion under a full-periodicity hypothesis; (3) concerns the primary replacement E, not an unproved strengthening for that literal source shape.

A period of C lies in a Z³: fix one point of C and subtract it from its translate. Dividing a period by a, (3) gives

    Stab_Z³(C)=a π⁻¹(Stab_Γ(B))=aQ Z e₃.                      (4)

All tilings of E have precisely this same group, not merely rank at most one. The converse inclusion is forced by kernel invariance. This also explains why the exact lift cannot produce a tile with no nonzero periods in Z³: its kernel is deliberately present in every solution.

## 5. Connectivity preserves the full correspondence

Translate E into the integer cube C_l. The primary connected assembly uses c=l³-(l-2)³ shell sites and scale s=3c+6. Its connected residue set S_l has s³ points, tiles only by translates of s Z³, and satisfies pairwise face-contact for su+S_l and sv+S_l whenever distinct u,v belong to C_l. Define

    P=sE ⊕ S_l.

The disjoint copies are each connected and pairwise adjacent, so P is connected. A tiling D ⊕ P=Z³ decomposes into the S_l tiling with centers D ⊕ sE, which is t+s Z³. Dividing by s gives a tiling of E. Thus ALL integer tilings of P, up to a common translation, have the form

    D=t+s a π⁻¹(B).

Put K=sa≥2. Then

    D lies in a coset of K Z³,
    Stab_Z³(D)=KQ Z e₃.                                      (5)

One must carry both the grid-coset property and the period group; existence alone would not support the next calculation. The primary's disjoint replacements, not ad hoc bridges, supply connectedness.

## 6. Generic sampling upgrades the grid constraint to all real translations

Let Ω=P+[0,1]³ and suppose A⊂R³ translates Ω to an almost-everywhere tiling. Because P is nonempty, distinct translation vectors have sup-norm distance at least one; otherwise a fixed constituent unit cube overlaps its translate in positive volume. Thus A is countable.

For almost every θ∈(0,1)³, all points of θ+Z³ have coverage multiplicity one and θ_j avoids all a_j modulo one. The actual primary sampling proof gives

    b_θ(a)_j=ceil(a_j-θ_j),
    {b_θ(a):a∈A} ⊕ P=Z³,                                    (6)

and b_θ is injective. Equality in (6) follows by intersecting each translated voxel union with θ+Z³; each voxel contributes exactly its rounded lattice point.

By (5), for every generic θ and any fixed a,a'∈A,

    b_θ(a)-b_θ(a') ∈ K Z³.                                   (7)

Suppose a_j-a'_j were nonintegral in some coordinate j. As θ_j varies in (0,1), the difference ceil(a_j-θ_j)-ceil(a'_j-θ_j) takes two consecutive integer values, each on an interval of positive length. Take generic θ in each of the two corresponding positive-measure boxes. Both values would have to be multiples of K, impossible because K≥2. Therefore every difference a-a' is integral.

Fix a₀∈A. Then b_θ(a)-b_θ(a₀)=a-a₀ for every generic θ. Formula (7) now gives A-a₀⊂K Z³, and (6) shows A-a₀ itself is an integer tiling set of P. Consequently its real period group equals its integer period group: a real period is the difference of two of its points. Combining with (5) yields

    Stab_R³(A)=KQ Z e₃.                                      (8)

Thus the ordinary integrated construction yields connected unit-cube unions whose every real tiling has one common exact rank-one period lattice and a rigid global grid phase. No invariant-measure argument, periodicity assumption, or claim that arbitrary polycube tilings are integral is used. Sampling ALONE would not preserve periods; it is the grid restriction on EVERY sampled tiling, tested at two sampling phases, that does so. This short arithmetic addition is fully paid here and is not asserted substantial.

## 7. Stronger p-adic structure and active-set ambiguity

The primary classification gives, for any decoded array,

    W(n,m)=c f_p(m-Dn-E) when m-Dn-E≠0,                       (9)

where c∈F_p^× and D,E∈Z_p. At most one integer m per column is excepted. This description is stronger than mere absence of periods.

The source does not force active sets to be singletons. Nevertheless, choose any label independently at each (n,m) from its nonempty active set. Every resulting array satisfies the line rule, since every Cartesian active word is allowed. The two seed witnesses give nonconstancy for each selection.

Change just one selected cell. The two arrays agree elsewhere. Their parameters in (9) must agree, as can be checked without relying on a literal shorthand in the primary uniqueness remark. In one fixed column compare c f_p(m-z) and c′ f_p(m-z′). If z≠z′, a sufficiently small p-adic ball about z avoids z′ and makes the second function constant. The first function takes all p-1 nonzero values on arbitrarily deep subballs approaching z. Since p>2, one subball has a different value and contains infinitely many integers, contradicting agreement outside finitely many cells. Thus z=z′ in every column; a nonsingular residue then gives c=c′. The columns n=0,1 determine E,D. Hence a selection can vary only at a genuine singular cell m=Dn+E. There are at most N such cells in the full strip.

This observation controls the symbol-choice factor, not all high-coordinate or stacking-height freedom. It does not prove uniqueness of tilings, zero entropy of the full tiling space, or unique ergodicity of the full encoding. Auxiliary outputs are constrained through separate permutation tests; their full fibres have not been classified here. Calling the whole tiling space an odometer from (9) would omit those fibres.

## 8. Exact one-column discrepancy, including deep almost-periods

For h∈Z\{0}, let k=v_p(h). For any column of (9), define the asymptotic proportion δ(h) of m with W(n,m+h)≠W(n,m). The at-most-two singular values do not affect density. Integers are equidistributed modulo p^r; the unresolved tails have density at most 2p^(-r), so Haar counting in Z_p gives the ordinary interval density, uniformly in the starting interval after its length tends to infinity.

If v_p(x)<k, f_p(x+h)=f_p(x). Divide the remaining x by p^k and put u=h/p^k, a unit. Of the p residue classes for y:

- p-2 classes have y and y+u both nonzero modulo p. Their first digits differ.
- In the class y=-u modulo p, the digit of y is -u and that of y+u is uniform on F_p^×. The mismatch probability is (p-2)/(p-1).
- In the class y=0 modulo p the same probability occurs with the roles reversed.

Therefore

    δ(h)=p^(-k) [(p-2)/p + 2(p-2)/(p(p-1))]
        =p^(-k) [1-2/(p(p-1))].                             (10)

Multiplication by c and translation by Dn+E leave this unchanged. For p=2 the formula is zero, consistent with the constant one-symbol digit function; the source uses p>200. Finite cyclic checks at small primes test the counting identity, not the full construction.

The factor p^(-k) is unavoidable. For the explicit source graph and horizontal shift h_k=(0,p^k), k≥2, seed useful/high outputs and z are unchanged because the horizontal residues modulo p² are unchanged and x₁ is fixed. At any x where all N ordinary selected labels agree under h_k, all other graph outputs agree as well: each ordinary block and its x₁-rotation are identical. By a union bound the fraction of exceptional x is at most N δ(p^k). Thus the graph has deep almost-periods of inverse-linear density even though it has no exact periods.

## 9. Translating the discrepancy into graph counts

Let |K_low|=product_i r_i, and normalize counting densities on Z² × V by area times |V|. For a pure horizontal h=(a,b)≠0, choose n=0 or 1 with d=b+na≠0. If W(n,L_n(x)+d) differs from W(n,L_n(x)), the two active sets differ, hence the channel functions g_(n,x+h) and g_(n,x) differ at at least one of their r_n inputs. Independence of other low inputs means at least |K_low|/r_n graph points have changed useful output. Two distinct graph points over the same base contribute two points to the symmetric difference. Consequently

    lower-density(A Δ (A+(h,0)))
      ≥ [2|K_low|/(r_n |V|)] δ(d).                          (11)

The density of the decoded discrepancy over large horizontal squares is (10): L_n is onto modulo every p-power and the residual tails are uniformly small. This establishes (11) even if the whole symmetric difference lacks a density. Since p^v_p(d)≤|d|≤|a|+|b| for n∈{0,1}, it gives an explicit positive constant divided by |a|+|b|.

For a finite-coordinate shift v as well, telescope the symmetric difference through e=|V| translates. The discrepancy at ((ea,eb),0) is contained in the union of e translates of the discrepancy at ((a,b),v). Følner boundary errors disappear, giving at least the corresponding lower bound divided by e; the valuation of e is a fixed additional loss. This is a translation-discrepancy bound for EXACT common solutions. It is not a robust decoder for approximate solutions of the finite tiling equations.

For the explicit graph and h_k, the matching upper estimate is

    upper-density(A Δ (A+(h_k,0)))
      ≤ [2|K_low|/|V|] N δ(p^k).                            (12)

Both constants are fixed by the enormous source tile. Statements asserting a scale-independent separation from all nonzero translations would contradict (12). Equations (10)–(12) are elementary consequences of the strongest primary digit structure; they do not by themselves supply substantial quantitative novelty.

## 10. Finite patterns, true costs, and what remains unpaid

The strongest actual finite-pattern construction already admits an arbitrary domino alphabet through decorated two-prime Sudoku. The width is fixed independently of that alphabet, but the alphabet, forbidden-word table, number of input primes, cycle maps, and final tile size are not fixed. It uses B_t={(t,t,a)} in the seeds, so decorations do not have to be constant in a seed region. Both nonconstant arithmetic columns and one common inverse are essential. Replacing them by 'some nonconstant triple' or separate common-solution witnesses would be insufficient.

A naive direct simulation of arbitrary Z² local constraints would instead let a useful output depend on the entire x. Then the ordinary activation offsets move x by h. The source's block inverse works because all sources retain the SAME label j_i(x): L_i(h)=0. Without such an invariant, different source batches use different partitions. A target high output no longer determines one common block, and the inverse calculation cannot be made by the source fibre orderings. Merely adding translated cycle tests does not repair this completeness failure. The two-prime primary works around it by arithmetic addressing with rank-one channel dependencies; it does not prove a local conjugacy of arbitrary full shifts to translation sets.

Removing the one forced period in (8) is a different obstruction. The exact lift gives B=π⁻¹(A), so B+Qe₃=B before any connectivity or real sampling. None of the subsequent invertible rescalings removes that period. Imposing a second exact quotient-lift system with a different forced kernel on the SAME translation set fails: (4) for the first system would forbid the second kernel unless it is parallel. Using independent layers would require a new compatible finite-coordinate encoding, rather than intersection of those exact tiling spaces. No such kernel-eliminating operation is constructed here.

Finally (11) does not bound the defect density of a periodic approximate tiling. Its premise is a true common solution, and the source's global dependence/activation extraction may fail at a sparse set of bad fibres. To obtain a quantitative robust decoder one would need to control how those failures propagate under the p-adic rescaling and through the seed equations. Finite local satisfiability alone gives compactness/existence, not a uniform propagation estimate. The later undecidability construction also forbids an all-input computable radius bound deciding tileability; adding effectivity language to a compactness argument does not evade that obstruction.

The integrated chain closes the exact period/connectedness/real-translation consequences and the digit discrepancy calculation as source/primary compositions. It does not identify a fully paid nonroutine operation for nomination. No conditional bridge, no strong-aperiodic 3D tile, no full tiling-space classification, and no robust finite-defect theorem are submitted. These are precise limits of these calculations, not impossibility or exhaustion claims.
