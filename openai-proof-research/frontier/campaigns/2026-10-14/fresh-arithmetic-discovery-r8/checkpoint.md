# R8: isolation obstructs scalar-block multiplicity amplification

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0; original code MIT. Third-party inputs remain private.

**PRE_FREEZE_SCREEN_UNPAID. No candidate frozen; counted=false.** Campaign remains 6/10. Earlier RF/CS/r5/r6/r7 packages were not edited. This is a bounded discovery screen with a proved obstruction to one construction class, not a substantial-result nomination or an impossibility theorem for new unequal-multiplicity pairs.

## 1. Source interfaces actually read

Family 059 at stipulated revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb has two relevant companions. Both complete introductions were read.

- *Ambiently homeomorphic isolated hypersurfaces of multiplicities two and three*: `thm:main` supplies real-coefficient, positively weighted-homogeneous polynomials in one finite ambient dimension N>3 divisible by eight, with isolated critical points and multiplicities 2 and 3. The complete `seeds.tex` and `conclusion.tex` bodies were also read. `topo:right-equivalence` already supplies a homeomorphism phi with f_1=f_2 composed with phi. `topo:arnold-corank` already gives distinct Hessian coranks. `topo:tangent-milnor` already uses a common square to distinguish connectedness of initial-form Milnor fibres.
- *Ambiently homeomorphic isolated hypersurface germs in C4 with multiplicities four and five*: `thm:main` supplies reduced convergent germs with isolated critical points, orders 4 and 5, and ambiently homeomorphic zero sets. Its complete introduction distinguishes its finite-map/lattice proof from the first companion. Its remaining proof was not read in r8. No right-equivalence interface is silently inferred from this introduction.

These are supplied theorem truths, not claims established by r8. The packet retains their exact pinned TeX identities. The complete preprints-tree listing, not the truncated root-tree cache, was used to identify the companions.

## 2. The tempting amplification mechanism and its full obstruction

Right equivalences transport arbitrary holomorphic functions of the scalar values: if f_i=g_i composed with phi_i on separate blocks, then

    H(f_1(x_1),...,f_s(x_s),w)
      = H(g_1(phi_1(x_1)),...,g_s(phi_s(x_s)),w).

This makes products, powers and auxiliary-variable compositions superficially attractive for amplifying multiplicity while retaining topology. The following exact calculation rules out every such isolated scalar-block amplification, not only powers.

**Lemma (scalar-block isolation criterion).** Let s>=1. For each i let f_i:(C^{n_i},0)->(C,0) be a nonzero holomorphic germ with f_i(0)=0, an isolated critical point at 0, and n_i>=2. Let w range over C^q, where q>=0, and let H:(C^{s+q},0)->(C,0) be holomorphic with H(0)=0. Define

    F(x_1,...,x_s,w)=H(f_1(x_1),...,f_s(x_s),w),
    h(w)=H(0,...,0,w).

Assume 0 is a critical point of F. Then F has an isolated critical point at 0 if and only if every a_i=partial H/partial t_i(0) is nonzero and h has an isolated critical point at 0. When q=0, the last condition means the unique point in C^0 and is automatic. In this situation, with ord(0)=infinity,

    ord_0 F = min(ord_0 f_1,...,ord_0 f_s, ord_0 h).

**Proof.** Because every df_i(0)=0, criticality of F at the origin forces d_w H(0)=0. Suppose a_i=0. On the germ

    Z_i = {f_i(x_i)=0, x_j=0 for j!=i, w=0},

the scalar argument of H is identically zero. The x_i-gradient of F is a_i df_i=0. All other x_j-gradients vanish because df_j(0)=0; the w-gradient vanishes by d_w H(0)=0. Thus Z_i is contained in Crit(F). Since f_i is a nonzero nonunit holomorphic germ in n_i>=2 variables, its zero set has dimension n_i-1>=1. This contradicts isolation. Hence every a_i is nonzero.

Shrink the representative so every H_{t_i} remains nonzero. The chain rule gives

    d_{x_i}F=H_{t_i}(f_1,...,f_s,w) df_i(x_i).

Since f_i has an isolated critical point, simultaneous vanishing of all block derivatives now forces every x_i=0. On that locus the remaining equations are dh(w)=0. This proves the exact critical-locus germ identity

    Crit(F)={x_1=...=x_s=0} times Crit(h),

and establishes both directions of the criterion, including q=0.

For the order formula, expand H as h(w)+sum_i a_i t_i plus terms involving t with either at least two t-factors or at least one w-factor. After substitution, every latter term has order greater than m=min_i ord(f_i), since each ord(f_i)>=2. The leading pieces of sum_i a_i f_i lie in disjoint variable blocks and cannot cancel one another. They also cannot cancel a term of h, which depends only on w. Therefore the first surviving degree is min(m,ord h), as asserted. QED.

The dimension restriction n_i>=2 is essential to the necessity argument: a zero fibre of a one-variable nonzero germ is zero-dimensional. No one-variable conclusion is claimed.

## 3. Consequences for the screened route

For any number of disjoint copies of the source 2/3 right-equivalent pair, every scalar-block construction above that remains isolated has orders

    min(2,ord h) and min(3,ord h).

If h has order at least 3 (or q=0), the pair remains 2/3. If h has order 2, both orders become 2. A power H(t)=t^k, k>=2, has H_t(0)=0 and acquires the entire positive-dimensional zero fibre as critical points. Products of block values have the same defect. Mixed higher terms and auxiliary variables do not evade the general criterion. Coordinatewise topological transport alone therefore cannot produce isolated pairs with larger multiplicities.

Allowing nonisolated germs or complete intersections would change the problem. For example, Cartesian products of hypersurface germs have multiplied multiplicity but have higher codimension. By contrast, multiplying defining functions in disjoint blocks adds their orders and produces a nonisolated critical locus along the intersection of their zero fibres. Neither construction supplies an isolated hypersurface replacement. No such weakening is nominated.

The source's actual seed proof explains why a new seed is not merely an unchecked parameter substitution. Its finite valuation relation has positive coefficient sum E. The signed chain weights have a variable-count excess 4E, balanced by 4E squares on one side. Common cubes both enforce order 3 and annihilate the odd character values divisible by 3 in the spectral comparison. Its later tensor construction contains those squares and cubes explicitly. Replacing them with higher powers changes the character identities, variable-count compensation, and integral-form problem. The source theorem does not provide that replacement.

The remaining operation would be to construct isolated germs with controlled unequal higher orders together with compatible integral Seifert forms, or to provide a non-scalar holomorphic coupling whose topology is transported with proof. No such mechanism was found. The lemma neither excludes such constructions nor proves an unbounded-multiplicity theorem. There is no scope freeze or reduced substitute.

## 4. Closest primary proof comparison for the metric detour

The actual full five-page body of Mahdi Teymuri Garakani, *A note on the Zariski multiplicity conjecture*, C. R. Math. 352 (2014), 725–729, DOI 10.1016/j.crma.2014.07.010, was read. Its main theorem uses a generic radial segment and a linear bound for the right-equivalence map to compare orders. The proof supplies the growth comparison through Bernstein polynomial approximation. Its corollary concerns radial Lipschitz control in both directions.

The corresponding Holder calculation adds no substantial operation: if f=g composed with phi, ord f=a, ord g=b, and |phi(tv)|<=C t^alpha on a direction where f's initial form is nonzero, then c t^a<=|g(phi(tv))|<=C' t^(alpha b), forcing alpha b<=a. For the source's 2-to-3 direction this yields alpha<=2/3. This is elementary growth bookkeeping beside the actual primary proof, not a new nomination or a sharp existence theorem. It applies to right equivalence, not every ambient zero-set homeomorphism. The source's constructed weighted-cone map is explicitly distinguished from its separate right-equivalence map, so their metric properties cannot be interchanged.

The general scalar-block lemma above was proved directly by the chain rule and dimension, with no new external singularity-theoretic theorem used. Its role is exclusion of the attempted mechanism, not a claim of worldwide novelty for that elementary lemma.

## 5. History and status

The inherited full campaign/exclusion chain remains controlling. Parent reserves083; 271, 298/300, structural334 and all older developed chains are not reopened. R7's193, r6's068 and r5's048/049 screens remain sealed. Family199 is excluded by the actual structural-r14/finite-field-Tachikawa-r2 FT2 history, not merely lack of acceptance. The old Steinitz097 and hyperbolicity095 developed chains were also located and excluded. Family018's finite-index consequences were already screened in r5.

A focused older/current Markdown search found no developed family059 chain, but this is not positive eligibility clearance or a complete semantic history audit. No complete new mechanism survived, so no final eligibility clearance or target freeze was attempted. Source statements, exact reading extents and primary-operation comparisons have been recorded without claiming full reading of downloaded-but-unread bodies or truncated history output.

No new count, proof PASS, contribution PASS, manuscript, Lean work, nested agents, shared edits, git or publication occurred. The result of this round is the exact scalar-block obstruction and the identified seed-level requirement, with the full isolated-hypersurface ambition left unpaid.
