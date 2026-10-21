# Integrated reduction and precise stopping point

PREFREEZE / no nominee. This is an exploratory research note, not a frozen theorem, full author proof, or self-assigned mathematical grade. The one selected family is the Source161 homomorphism-density construction. The intended scope is the actual old i13 connected biregular-pattern target, unchanged. The regular-triangulation model below is a diagnostic route inside that scope, not a new smaller target.

## What the strongest source composition already supplies

The pinned manuscript's `thm:main` gives a 35-vertex, 66-edge bipartite counterexample. Its point-face incidence complex has 13 points, 22 triangles, 33 pairs, two triangles per pair, and nonconstant point degrees 4,5,6. Its full proof was read: the special six exposure orders and discrete refinement in `prop:complex`; the activation moments, identity coefficient, type pinning and dilution in the kernel section; the transverse determinant calculation and joint-sign averaging; the Lagrangian orbit/planted estimates and complete singular-tail argument; and the symmetric-kernel/finite-host conversion.

These operations are paid at their actual interfaces. In particular, source pinning uses a finite hierarchy of vertex/pair scores distinguishing the desired type map; it is not simply a generic consequence of finite types. The full rank-layer statement is for this specific pattern, all allowed activity subsets, and its own quantitative tail estimates. Neither it nor the discrete refinement conclusion is a theorem for arbitrary triangulations. The source's consequences already provide tensor amplification, finite blowups/injective consequences and the nonforcing interpolation. None is a proposed contribution here.

The strongest compatible classical host reduction is also paid. Coregliano–Razborov, arXiv:2108.06599v2, Lemmas4.1,4.2, Corollary5.1, Lemma5.2 and the full proof of Theorem3.1, give a reweighting/trimming/reweighting chain with a pattern-dependent constant loss and unchanged mean, followed by a tensor-power removal of that constant. The first reweighting preserves the opposite marginal, the trimming produces a positive lower degree bound, and the next exact normalizations are compatible. Contraposition gives arbitrarily small normalized ratios on biregular bigraphon HOSTS when a fixed pattern violates the inequality. It leaves the PATTERN fixed. The completed r127 original already credited this full operation. There is no new host-regularization claim.

Conlon–Lee, arXiv:1809.01259v3, prove the actual dense one-sided-degree theorem, its divisibility extension and its blowup consequence through permutation Hölder symmetrization and a reflection-hypergraph comparison. In Theorem1.2, a right r-regular pattern with |B| >= binomial(|A|,r) has the positive inequality. Its final power alpha=|B|/binomial(|A|,r) is at least one, permitting Jensen in the needed direction. For the source counts it is 22/286; for the 16-point torus diagnostic it is 32/560. Thus this particular sufficient condition does not apply. This observation says nothing about other sufficient conditions for either pattern. The factorial one-sided blowup is a positive operation and is not a deficit-preserving way of changing the old pattern.

The transitive reflection argument was followed in the actual Conlon–Lee arXiv:1611.05784v2 proof: cut Cauchy–Schwarz trees, accumulation of monochromatic mass, symmetrization over edge automorphisms, the chamber/coset embedding, and stack induction giving a percolating sequence. Its hypergraph extension is explicitly stated there. Coregliano arXiv:2205.14703v2 further gives colored orbit comparisons and the degree-multiplicity criterion; its operative Section6 induction, marginal normalization and Jensen proof were read. These are real positive theorems to respect, not obstacles that disappear by naming a new pattern. No claim is made that the diagnostic torus escapes all reflection/left-reflection criteria. No classification of regular triangulations was proved. Hatami's necessary biregularity for a weakly norming graph is one-way; it supplies no converse for all biregular patterns.

## Why the source's identity pinning cannot be reused verbatim

For a bipartite (d,c)-regular pattern F with p and q vertices and m=dp=cq edges, let a type map h have weight

    w(h) = product_u pi[a(u)] product_v nu[b(v)] product_uv lambda[a(u),b(v)].

Assume positive weights on the supported type pairs; zero weights follow by limits. Put z_ab=pi_a^(1/d) nu_b^(1/c) lambda_ab. Then w(h)=product_ab z_ab^n_ab(h), where the nonnegative multiplicities sum to m. The map k_ab collapsing both parts to the one pair (a,b) has w(k_ab)=z_ab^m. Weighted AM–GM gives the exact inequality

    w(h) <= sum_ab (n_ab(h)/m) w(k_ab).

The old i13 pinning score identity is the logarithmic version for the identity type map. It prevents any vertex/pair-weight choice from making that map dominate every collapsed map exponentially. More generally, for finitely many coefficients C(h),

    sum_h |C(h)| w(h) <= (sum_h |C(h)|) sum_ab w(k_ab).

This does not prove that the signed total is nonnegative. It only shows why a weight-only separation of a chosen finite collection from all collapsed weights needs additional structure. Cancellations among all the noncollapsed maps remain possible. The old sign-AVERAGED positivity likewise does not decide fixed signs.

The calculation in note01 goes further for collapsed coefficients without pretending to classify the entire sum. In a connected closed triple complex, its pair-corner medial graph L is connected and 4-regular. At a fixed target corner k the nonempty moment matrix consists of 63 diagonal singleton states of weight1 and 32 two-state blocks with matrix (1/2)[[1,sigma_k theta],[sigma_k theta,1]]. Hence

    C(k) = 63 + 32*2^(-m) sum_{s:E->{0,1}} (sigma_k theta)^|delta_L(s)|.

Every cut has even size. This coefficient is independent of sigma_k and at least 63+64*2^(-m). The tetrahedral enumeration at theta=1/2 gives 1032617/16384 for either sign, matching the formula exactly. This is a route diagnostic, not a new full theorem proposed for review.

At an individual face the three subset differences XOR to zero. A nondegenerate target-face image allows either three signed entries or none; a two-point image allows the two repeated-corner entries or none; a one-point image allows an even number. Thus any local negative product must come through fully signed nondegenerate face images. Determining their globally compatible multiplicities and the resulting whole coefficient is still unpaid. Finite local enumeration does not replace that global derivation.

## The rank-layer transfer has a separate, quantitative failure

Even a negative finite activation coefficient would not justify importing the source limit to a changed pattern. For symmetric D-by-D matrices, D=2r, put b(t)=t(t+1)/2 and let p_xi be the source's signed rank-r mass. For v point variables and f face variables, all point matrices equal with probability q^(-(v-1)b(D)). With all incidences active and sign xi, each face contributes exactly p_xi^(-2) after integrating its center. Nonnegativity therefore gives the exact lower bound

    q^(-(v-1)b(D)) p_xi^(-2f).

Using the actual source mass asymptotic p_xi=(1/2+O_D(q^-1))q^-b(D/2), its field exponent is

    E_D = 2f b(D/2) - (v-1)b(D).

If 3f=dv and d>=6 then f>=2v, so E_D >= (D^2+(v+1)D)/2 >0. Equivalently for chi=v-f/2,

    E_D = ((1-chi)D^2+(v-2chi+1)D)/2.

This exact event defeats a finite half-rank parity-model limit for those changed patterns. It is not a disagreement with the stipulated source: at v=13,f=22 its exponent is (-D^2+10D)/2, negative in the source's dimension range. The source's detailed tail proof legitimately uses its special exposure slack. A regular degree-six torus has no such freedom to dismiss the all-point-collapse event.

The diagnostic code constructs the 16-point periodic triangulation, checks its 32 faces, 48 pairs and degree six, and enumerates Sym_2(F_q) for q=3,5,7. Both signed rank-one layers have mass (q^2-1)/(2q^3); their exact all-collapse contribution already exceeds one. This checks the event formula, not the full torus density or a counterexample.

The problem survives any fixed finite choice of the source activation parameters and type priors. Choose a positive-mass type pair (a,b) and a positive-probability nonempty activation atom (S,xi), probability c. Restrict every point type to a, every face type to b, every incidence atom to this same atom, and all point matrices to coincide in each coordinate of S. The contribution is at least

    pi_a^v nu_b^f c^(3f) product_{j in S}[q^(-(v-1)b(D)) p_xi_j^(-2f)].

At fixed D, finite parameters and d>=6 this diverges as q grows. In particular, fixing signs, solving a finite coefficient problem, and then taking the old large-q limit does not close the target.

## Compatible repairs considered, and what is still missing

Field-dependent thinning or priors can suppress that one event. The AM–GM comparison above shows why this also suppresses the desired finite type-map scale relative to the collapsed weights. But it is not a uniform full-density comparison: the transverse approximation has errors, activity configurations can change scale, and unaccounted proper supports may contribute. No conclusion about all q-dependent choices or every finite q is justified. To use such a repair requires a uniform relative error bound at the shrinking negative-deficit scale and a complete sum over maps and activity supports. Neither is supplied here.

Changing rank changes the exact collapse exponent to

    2f b(D-r) - (v-1)b(D).

For d=6, its leading quadratic term can be nonpositive only if (D-r)/D <= sqrt((v-1)/(2f)) = (1/2)sqrt(1-1/v), requiring rank strictly above half the dimension at a positive fractional distance. At rank below half, two rank-r matrices cannot have a nonsingular difference, by rank subadditivity. At rank above half, the complementary-image step behind the source determinant-parity identity no longer has its half-rank interface. This identifies what a different-rank approach must replace, not an impossibility theorem for it.

Conditioning all point differences to be nonsingular is a global event involving several sampled vertices. It is not, as stated, a nonnegative binary kernel with independent vertex sampling. A new local gadget, code, truncation or conditioning representation could change that conclusion, but its exact density identity and its compatibility with the sign/activation law would need proof. The old positive-semidefinite moment obstruction still rules out simply setting every diagonal moment to zero while keeping the desired off-diagonal moment. The r66 equality-wire and voltage-cover attempts also remain their original old scopes: no negative-preserving untyped regularization is obtained by naming those gadgets again.

A genuine completion would need either (i) a connected biregular pattern and a nonnegative kernel with a complete negative ALL-homomorphism density calculation, including all type maps, all activity subsets and all singular configurations, followed by the already paid finite/symmetric conversion; or (ii) a rigorously deficit-preserving pattern transformation whose compatibility with all of those operations is shown. The two concrete missing interfaces here are global signed coefficient control beyond the collapsed terms, and a stable rank/activation transfer with the changed pattern's singular mass controlled at the same deficit scale. Even closing both would require checking orientation, dilution and finite conversion for the resulting exact statement, not silently inheriting the source's exponents.

No feasibility closure, statement freeze, author-proof nominee, worldwide novelty claim, full-scope impossibility, or search exhaustion is asserted. The original i13 and r66 targets and every old disposition remain unchanged.
