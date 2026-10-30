# Structural216 independent correctness review — round 1

**Role verdict: full-scope PASS, relative to the stipulated Source340 truth and the explicitly identified primary interfaces.** This verdict concerns the entire unchanged frozen statement and the submitted `AUTHOR-PROOF.md`, including its auxiliary comparison arguments. It is not a verdict on a repaired, narrowed, marked, or renamed result. No essential mathematical obligation remains unresolved in this submission. No contribution grade, acceptance decision, or count is assigned.

The frozen statement has SHA256 `75b55258f022d13db6995649a1ab7d7f29b80066721e560dd01cfb4ca9ddb6e3`; the reviewed proof has SHA256 `eae38f752f868a3d4e7ad601c3d24e41926f8dad8341929b943f6735bbf792ba`. The result is existence on **one** base `Q=S^9×S^{N−1}` for **one** sufficiently large even `N`, with the zero section and three further closed exact smoothly embedded images, each abstractly diffeomorphic to Q, and all six pairs inequivalent under the stipulated uniformly compactly supported Hamiltonian isotopies. Neither an all-N assertion nor a numerical dimension threshold is used.

There is a separate artifact discrepancy: the prompt's standalone verifier hash does not match the actual admitted verifier. The four detached author packet anchors, the statement and proof hashes, and all 55 selected file hashes/modes do match. The actual verifier was inspected, run read-only with all four explicit anchors, and passed; its result was independently checked against the authenticated manifest. This discrepancy is recorded in the outside report and reading/access record, and is not used as a mathematical gate.

## 1. Precise interfaces and the naturality obligation

I read the source's complete operative TeX, not just its introduction or catalogue. Its actual include order is introduction, tubes, morse, obstruction, embedding, transport, with the two figure includes in obstruction and embedding. All 13 canonical blobs, including the PDF, authenticate against the complete pinned tree at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The PDF's authentication is not claimed as semantic reading.

The source's `T_{k,l}` is the component of the standard angular form `−|x|²+|y|²` among C¹ functions on `S^{k+l−1}` with zero regular. The extension `g(ru)=r²h(u)` is C¹ at the origin and smooth away from it for smooth angular h. The stable space T is the diagonal telescope under fixed signature-(1,1) addition. Smooth domain models and this C¹ angular model have the same stable homotopy classes; the source supplies the relative compact-parameter approximation and the contractible defining-function choices. There is a fiber sequence `H^s(*)→T→BG`; gamma classifies the stable spherical fibration of negative domains. The rigid map `i:BO→T` sends a quadratic family to its tube, and `gamma i≃BJ`, because the negative tube retracts to the negative eigensphere bundle. These assertions are stipulated source interfaces, not conclusions audited here.

Actual primary reading confirms the relevant identifications. AIS v2 §3.6 distinguishes spherical domains and Waldhausen partitions, proves their comparison only after stabilization, identifies the rigid map, and states the integral fiber sequence (Theorem 3.30). AACK v2 §4.1 identifies the negative-domain frame construction with stable BG; its extraction has font-map losses, so exact signs/formulas for the new argument are taken from the clear authenticated source and AIS rather than guessed from that extraction. ACGK v3 §4.1 gives the topology on functions linear at infinity, the two quadratic actions, and their stable comparison with partition tubes (Proposition 4.4). Compact families have a common compact perturbation support in that topology.

Most importantly, AIS Proposition 4.4 is an **integral stable-homotopy** assertion: doubling a local generating germ determines a distinguished coset of `[Q,BO]→[Q,T]`, invariant under Hamiltonian isotopy. It is not merely a real torsion class. Its proof uses the bar-construction fibration with fiber `Z×T`, Gauss map to U/O, and the action of `Z×BO≃Omega(U/O)` on lifts. The rank factors are fixed/removed by the conventional stabilizations; they do not give an additional orbit of sphere classes in the argument here.

AIS Remark 4.8 does leave a real obligation: a given ordinary tube generating function is not automatically the specific natural output, nor may membership in its invariant set be substituted for the natural coset. The submitted proof addresses exactly this obligation. It starts with the actual generating germ, performs the actual ACGK small birth, gives an explicit lift of separation, and then compares that partition to its homogeneous infinity data through regular compact partitions. It needs only that the infinity class belongs to the natural coset; it does not claim that the original F is itself the particular AACK-modified natural generating function. The verification of this comparison is in §§5–10 below. Quoting persistence alone would not suffice, and is not what the proof does.

## 2. Integral class and rigid intersection

Put `A=pi_9 H^s(*)`. The supplied source computation is `A_(2)=Z/8⊕(Z/2)^2`, with preceding boundary domain `pi_10 BG=pi_9^S=(Z/2)^3`. Thus the boundary image is killed by 2. Localization of this exact sequence of abelian homotopy groups is exact, so the localized kernel of `j:A→pi_9 T` is precisely the localized boundary image and is also killed by 2.

To obtain an integral element rather than pretend that a localized generator is integral, choose a generator e of the displayed Z/8 summand and write `e=y/s`, with y integral and s odd. Then `y_(2)=s e`; it has order 8 and an odd generator coordinate. Take x=y and a=j(x). Since `2x_(2)` has order 4, it cannot lie in a group killed by 2. Therefore `2a_(2)≠0`. The order of a_(2) divides 8 and is either 4 or 8. Consequently 0,a,2a,3a are distinct **integrally**; an integral equality would persist after localization. No assertion that the integral a has order exactly 4 or 8, no absence of odd-primary components, and no unlocalized finite-generation hypothesis is needed. Exactness before localization gives `gamma_*a=0` integrally.

For the rigid image, if `i_*e` belongs to `ker gamma_*`, then `BJ_*e=0`. The source's injectivity in degree 9 forces e=0, hence `ker gamma_* ∩ im i_*={0}`. The injectivity used here is J in degree 8, namely `pi_9 BO→pi_9 BG`. The source also uses J in degree 9 to sharpen the cardinality bound on the preceding boundary; that sharper cardinality bound is not needed for the author's exponent argument. There is no interchange of these two J uses.

As a primary corroboration, I read Rognes arXiv:1403.5998v1 §3, including Theorem 3.3 and the degree-10 entry. Its stated exclusion of irregular-prime torsion does not affect the 2-local entry. The input for this review remains the stipulated source calculation, not an independent reconstruction of Rognes's original computation, Bott, Adams, or stable stems.

## 3. One finite stage, one base, all constants

Each of 0,a,2a,3a is represented on a finite diagonal stage. A map from a compact sphere into the mapping telescope has bounded height, and a finite initial telescope retracts to its last stage. There are only four maps, so a common later stage suffices. Further stabilization gives a common m≥20; set N=2m only after this choice. For 0 use the fixed quadratic representative. The three nonzero maps can all be localized by the source lemma's actual degree-one-collapse and relative-smoothing proof. That proof depends on having a based sphere class, not on which nonzero element was first chosen in the source. Thus its use for 2a and 3a is valid.

Use the intersection of the finitely many pole neighborhoods, then smaller common neighborhoods U0, so every angular family is exactly the same standard quadratic form there. For the common height theta, `delta0=min_{S^9\U0}|d theta|>0`. Compactness of the three angular parameter families yields common c>0, C, C1 satisfying

`c|w|≤|grad g_j,b(w)|≤C|w|`, and `|d_w d_b g_j,b(w)|≤C1|w|`.

Choose K with `K delta0>C1/c`, choose Lambda so `R=Lambda exp(K theta)` has minimum exceeding both C and the maximum inner gradient of every smooth extension G_j, and finally choose common T greater than `1,Rmax/c,D_beta Rmax/c`. This is the source's order of choices; enlarging a later cutoff does not invalidate an earlier condition. The finite min/max operations preserve strict inequalities. The zero section need not be replaced by the embedded realization of the zero class: its constant quadratic generating family can be used on this same base and at this same fiber stage for the invariant computation.

Any later stabilization used in comparing stable partition models adds generating variables over this already fixed Q. It does not change Q or require a second N. The proof uses stable equivalences only on compact parameter families and therefore can choose finitely many common additional variables. It makes no unjustified finite-stage equivalence claim.

## 4. Smooth realization, regularity, embedding, and primitive

The global functions are

`F_j(b,v,w)=G_j,b(w)−R(b) beta(|w|/T)<v,w>`.

The radial factors are constant near the origin, so their apparent dependence on |w| causes no nonsmoothness there. G_j is smooth everywhere; at infinity F_j equals g_j. The inner and outer estimates imply that all fiber critical points are precisely the solutions of `grad g_j,b(w)=R(b)v` in `1<|w|<T`. There are no unseen critical points in either cutoff transition. The explicit parametrization

`(b,u) ↦ (b,grad g_j,b(u)/|grad g_j,b(u)|, R(b)u/|grad g_j,b(u)|)`

is smooth and has smooth inverse u=w/|w|. It proves the asserted abstract diffeomorphism of the whole critical locus with Q, not merely a homotopy equivalence or a fiberwise count.

The full critical equation is regular: v-perpendicular variations span v-perp through `−R delta v`, and the radial variation delta w=w supplies Rv. This is a Morse-family condition on the total gradient map, and does not assume individual fiber Hessians are invertible. The generating-map lemma in the source then supplies immersion: a vector killed by its differential would be in the kernel of the transpose of the surjective critical-equation matrix, hence zero.

For two points with equal generated cotangent images, the base (b,v) first agrees. Equality of the sphere momenta implies `w−w'=t v`. Their entire straight segment has norm at most R/c. Integrating the common mixed derivative bound, including across zero where `d_b g` is C¹, gives `|d_b g(w)−d_b g(w')|≤(C1/c)R|t|`. Off U0 the base-momentum difference is therefore bounded below by `R|t|(K delta0−C1/c)>0` if t≠0. On U0 the quadratic equation already has a unique solution. This proves global injectivity; compactness then upgrades the immersion to an embedding. It also proves closedness, because the parameter manifold is compact without boundary.

With lambda=p dq, the pullback is exactly `Gamma_F^*lambda=d(F|Crit F)` on the entire critical manifold. No chartwise primitive gluing is needed. On Crit F, Euler gives `<grad g,w>=2g`, and thus `F=g−R<v,w>=−g`. Since Gamma_F is a diffeomorphism onto its image, `f_j=−g_j,b(w)` is a globally defined smooth primitive on L_j. For L0 use zero. The dimension and vanishing of the pullback of d lambda give the Lagrangian property with the frozen sign convention.

These are applications of the source's full embedded-realization proposition and proof to the three selected angular families. Source regular-band, h-cobordism, core-straightening and Hamiltonian-transport operations were also read completely and retained as stipulated truth; none is silently replaced by a general closed exact Lagrangian h-principle.

## 5. Gauss nullhomotopies and the actual unmarked invariant

The Legendrian lift is `(q,p,f_j(q,p))` in `J^1 Q` with contact form `dz−lambda`. It is closed and embedded because L_j is. The actual F_j, restricted to a neighborhood of its regular critical locus, is a local generating function in ACGK Definition 2.1. ACGK Theorem 2.4 and Proposition 2.6, read in §2.1, give precisely the stable homotopy between the tangent and vertical Lagrangian distributions. AIS §2.4 explains that this is the appropriate Gauss nullhomotopy, independent of a globally chosen tangent trivialization; §4.2 describes the change-of-nullhomotopy action. There is no extra moderate-tangency hypothesis in AIS Proposition 4.4. In particular the proof does not try to deduce the Gauss-map nullhomotopy merely from its being zero on homotopy groups of a product of spheres.

The coset is attached to an embedded image over the ambient fixed base Q. Changing the nullhomotopy amounts to a stable real bundle over L; via its cotangent projection homotopy equivalence this yields a class over Q and acts by the rigid map. This is explicitly the mechanism in AIS §4.2. It is not a quotient by arbitrary diffeomorphisms of Q or of the chosen parametrization. The source's parametrization itself preserves the b-coordinate; alternatively its spherical gradient-direction maps have degree ±1, yielding the needed projection equivalence in this case. No marking is part of the natural-coset output.

For the stipulated Hamiltonian convention, Cartan's formula is `L_X lambda=d(lambda(X)−H)`. Hence a Hamiltonian path lifts along L by adding its action primitive to z. The compact Lagrangian trace and bounded primitive values permit a contact cutoff in z, giving one compact support neighborhood if needed. At the endpoint the transported primitive and the chosen f_k differ by a constant, since L_k is connected; translating that constant does not alter the coset. Further, `pi∘Phi_t|L_j` is a homotopy from the initial projection to the final projection composed with Phi_1. Thus forgetting markings in the Hamiltonian statement does not introduce an uncontrolled pullback of the invariant. These facts agree with, rather than strengthen, the precise ambient-isotopy assertion of AIS Proposition 4.4.

## 6. Exact small birth, radial cutoff, and separation isotopy

Write q_tau=1/4+tau. The central birth is `d_tau(t)=q_tau t^3−4tau t`. Its two critical points are ±r_tau with

`r_tau²=4tau/(3q_tau)=16tau/(3(1+4tau))`, and `s(tau)=8tau r_tau/3>0`.

For `0<tau≤1/12`, r_tau≤1/sqrt(3), so both lie strictly in the prescribed central cubic region. The second derivatives are `6q_tau (±r_tau)`, nonzero, and the critical values are opposite (the positive critical point has value −s). Outside |t|≤1 the derivative is `3/4−tau+q_tau D0'(t)>0`; there are no other critical points. The odd D0 with the prescribed tails is a legitimate smooth choice in the ACGK construction. Positive dilation by kappa=s/s0 gives exactly `d_s(t)=kappa d_tau0(t/kappa)`, preserving nondegeneracy and rescaling the two values to ±s. Its E_s=d_s−t has compact support in |t|≤2kappa and norm kappa times a fixed finite norm. Both are uniformly bounded on every stipulated compact s interval.

For `H_s=F+t+alpha_A E_s`, the annular derivative estimate is

`|d_w H_s|≥c A−C_alpha ||E_s||_infty/A>0`.

Inside |w|≤A the function is the direct sum F+d_s; outside |w|≥2A its t derivative is 1. Thus the critical locus is exactly `Crit F×Crit d_s`. Near that locus the full differential is the regular F-gradient block and the nonzero d_s'' block, so it is again a regular generating family. Its covectors equal those of L and its primitive values are f±s.

At s=s0 this is **exactly** ACGK (3.8) with extension g'=F and cutoff alpha_A. ACGK Lemma 3.11 allows an arbitrary smooth extension of the generating germ; its cutoff need only equal one near the prescribed critical locus, have proper support, and avoid unwanted critical points. F is already global and has no additional generated component, so the large radial cutoff satisfies these hypotheses. Taking it larger only preserves that fact. Thus the identification with the small natural double is substantive and valid, not a replacement by a merely similar birth.

Since the cotangent projection of the Legendrian lift is the embedded L, it has no Reeb chords. Its ±s translates remain disjoint for every s>0. On a compact interval with s≥s0>0, their union has a compact isotopy trace. Contact isotopy extension, or cutoffs of ±the Reeb field near the two disjoint copies, provides a smooth isotopy supported in one compact neighborhood. H_s is an explicit lift of that same separation isotopy in the linear-at-infinity category, with one A and common support for E_s. At S>max|f|, zero separates the two critical-value sets. AIS's doubling interface therefore identifies its regular partition with a representative of the natural coset. No uniqueness theorem for arbitrary global generating families is invoked.

## 7. F_u, critical-value bounds, and the order of parameters

Set `G_epsilon= rho_epsilon(r) g`, with rho smooth, nonnegative, nondecreasing, zero near zero and one for r≥epsilon. It is smooth everywhere. At r>0 with rho>0, a critical point must have zero angular derivative. Angular zero-level regularity then gives h≠0, and its radial derivative `(2r rho+r² rho')h` is nonzero. Points in the zero plateau have value zero (including its flat boundary). Thus all critical values of G_epsilon are zero, though it can have highly degenerate critical sets. Uniform homogeneity gives the asserted O(epsilon²) value error and O(epsilon) first-derivative error, also uniformly over the compact base and compact smooth parameter families.

For `F_u=(1−u)F+uG_epsilon`, choose one ball outside which all functions equal g. No critical point lies outside it. On the ball the value bound `max(|F|,|g|)` bounds every |F_u| uniformly for all u and every sufficiently small epsilon, since 0≤rho≤1. Consequently M can be fixed first, then S>M, and then the common A satisfying the annular inequality. The final epsilon can be chosen after the later homotopies without invalidating S or A. No bound on the Hessians of G_epsilon uniform as epsilon→0 is needed.

For the fixed-S double built from F_u, possible fiber critical values are F_u±S, all nonzero. The annular estimate is unchanged because F_u=g there. This proves fiberwise regularity of the zero set even when F_u is not a Morse family. The proof claims only a regular partition homotopy at this stage, which is exactly what the invariant comparison requires. It does not infer immersed or embedded intermediate Lagrangians from these possibly singular critical loci.

At u=1 one can decrease s to s0 because all G_epsilon critical values are zero, and then increase tau to 1/12 through positive birth parameters. All auxiliary parameter intervals are compact, so one enlarged A works for their union. Multiplying the function by 3 preserves the signed zero domain. The positive change w=z/sqrt(3) gives `3g(w)=g(z)` and merely changes the radius of the smoothing and radial cutoff. The resulting normalized D has D=t³−t on |t|≤1, D=3t for |t|≥2, D'>0 outside |t|≤1, and D'≥−1. Thus the coefficient 3 in the subsequent formulas is correct. Concatenated homotopies may be reparametrized with stationary endpoint collars; no endpoint differentiability problem is used.

## 8. Full radial Euler test

The smooth nonnegative nondecreasing a can be chosen zero on a small initial interval and equal to r² beyond a large radius, with a≥2 wherever alpha_A=0, by taking A>2 and starting its increase inside the alpha plateau. Put

`B=(1−u)alpha_A+u`, `C=3−4B+u a`, and `P=g+B D+[3(1−B)+u a]t`.

For |t|>1, both terms in `P_t=B D'+3(1−B)+u a` are nonnegative and their sum is strictly positive. If B=0, necessarily u=0 and alpha_A=0, and P_t=3. At w=0, B=1 and a=0, so P=D; its zeros are 0,±1 and their derivatives are −1,2,2. These cover the cases in which division by B, r, or t would be illegitimate.

For r>0, B>0, |t|≤1, write `P=g+B t³+C t`. If t=0, a fiber critical point would require grad g=0 off the origin, impossible. Otherwise `P_t=0` gives C<0 and `t²=−C/(3B)`. At a zero critical point, Euler's identity and the radial component of the gradient give

`0=(rB'−2B)t²+rC'−2C = rC'−rB'C/(3B)−4C/3`.

The signs are `B'≤0`, `C'=−4B'+u a'≥−4B'`, and `C/B≥−4`. Therefore

`rC'−rB'C/(3B)−4C/3 ≥ −(8/3)rB'−4C/3 >0`.

The last strict sign uses C<0; it remains strict if B'=0. There is no unjustified Hessian, radial monotonicity, or gradient injectivity hypothesis on g.

At the u=1 endpoint, interpolating D to t³−t does not change |t|≤1, while exterior t derivatives remain positive. With B=1, C=a−1, the same contradiction is `r a'−4(a−1)/3>0` whenever a potential critical point forces a<1. This applies throughout the convex interpolation of a with r²: both are nonnegative and nondecreasing, with common value zero at the origin. The endpoint is exactly `g+t(r²+t²−1)`.

Replacing g by G_epsilon preserves this entire argument. Outside r<epsilon the formulas are identical. On a fixed small r neighborhood, the zeros of every member are confined near t=0,±1, and the t derivatives have a uniform nonzero margin. This follows from the displayed D model, from a(r)→0 and r²→0, and from g=O(r²); it is uniform over the compact collection of homotopy parameters. A sufficiently small epsilon therefore retains smooth regular zero sets throughout. This treats the degenerate plateau of G_epsilon as well as the origin; it is not an assertion that G_epsilon has isolated Morse critical points.

## 9. Infinity normalization really yields compact families of partitions

During the first radial homotopy, for large r one has alpha_A=0, a=r², and

`P_t=u D'+3(1−u)+u r² ≥ 3+u(r²−4)≥1`.

The later D interpolation has derivative at least −1, hence derivative of the endpoint family at least r²−1; the a interpolation is already a=r² on this exterior. For fixed w, these functions tend to ±infinity with t, so there is a unique exterior zero t=k(q,parameters,w). The implicit-function theorem gives a jointly smooth graph in the smoothed construction.

Take one R valid for every parameter and a cutoff chi supported in this graph region, zero at r≤R and one at r≥2R. The change `t=t'+chi k` is a genuine fiber diffeomorphism, with inverse obtained by subtraction. Its normalized zero set is exactly t'=0 for r≥2R. On r≤2R, every zero height is uniformly bounded: for |t|≥2, D and all its interpolations have the sign of t and magnitude at least 3|t|, while g and a are uniformly bounded on this w-ball. In particular the same height bound works as the cubic coefficient tends to zero at the u=0 endpoint. k on the transition annulus is uniformly bounded by compactness. Hence the normalized boundaries coincide with the standard hyperplane outside **one compact set in (w,t')**, not just outside a cylinder without height control.

This is the required topology for a compact family of partitions. Coorientation is unchanged by the coordinate diffeomorphism. Normal collars give defining functions with the same sign on both complementary regions and positive normal derivative; convex combinations of such functions retain these properties. Using the standard function t' outside the compact set and the source's relative defining-function construction gives a smooth family in the usual partition model. A compactly supported normal vector field extends its regular boundary homotopy if an ambient isotopy is desired. No critical points away from level zero need be excluded.

There are two distinct issues here, and the submission treats both. First, the parameter-dependent translations can be unbounded, particularly at u=0; they are used to define normalized partitions, not claimed to compactify as ambient diffeomorphisms. Second, the original class must agree with that normalization. At u=0, k=−g/3, and chi can start strictly outside supp alpha_A. Substitution then gives exactly

`3t'+(1−chi)g+alpha_A(D(t')−3t')`.

Where alpha_A is nonzero, chi is zero, so there is no suppressed D-argument shift. Dividing by 3 produces precisely ACGK Proposition 3.25's admissible flattening of the g-term outside the perturbation support. Its continuation from no cutoff has t derivative one wherever it changes the zero graph. ACGK §4.1 Proposition 4.4 also explicitly describes this flattening in the stable partition equivalence. Thus this step preserves the original ACGK class; the proof does not infer preservation from an arbitrary nonproper isotopy.

## 10. Stereographic sign, axes, and smooth stable class

At the endpoint, `P*=g+t(r²+t²−1)`. On the large-r exterior its graph satisfies

`|k|≤C r²/(r²−1)` and `|d_w k|≤(|grad g|+2r|k|)/(r²+3k²−1)=O(r^−1)`.

The same estimates are uniform over the compact base and the relevant parameters. Consider `G(w,a,b)=g(w)+2ab`. Its block gradient vanishes only at the total origin, so the restriction to the sphere has regular zero level. At e=(0,1,0) its positive b-normal is fixed and nonzero. The stereographic formulas in the proof give

`G(w_s,a_s,b_s)=4(1+rho²)^−2 [g(w)+t(rho²−1)]`.

Both the factor 4 and its positive sign are correct. This identifies signed domains and coorientations, not just zero sets. The form 2ab has signature (1,1), so it is exactly a fixed permitted hyperbolic stabilization. Any fixed positive scaling or coordinate permutation is harmless stably; for an orientation-reversing permutation one may include a reflection of a spare quadratic coordinate, which fixes that quadratic function and makes the combined linear change lie in the identity component. There is no parameter-dependent rigid bundle hidden in this coordinate operation.

The C¹ issue is real but addressed. The homogeneous direct sum is generally only C¹ on w=0. In the finite stereographic chart the zero-set axis points occur at w=0,t=0,±1. They are precisely the locations controlled by the uniform nonzero t derivative and replaced by the smooth G_epsilon construction. They are not omitted by saying the homogeneous function is smooth off its **total** origin.

Near e write x=w_s and y=b_s, with `a=sqrt(1−|x|²−y²)`. The C¹ implicit-function theorem gives `y=phi(x)`, with `phi=O(|x|²)` and `d phi=O(|x|)`, uniformly. The submitted radial cap cutoff makes this graph zero on a smaller cap. Its C¹ error tends to zero with cap size: the derivative of the cutoff costs O(1/delta), multiplied by phi=O(delta²). Every interpolating graph is regular because y−phi has y derivative one.

For precision, the graph comparison asserted in the submission also holds in the stereographic chart. For any of these small graphs, letting s=|x|, one has

`w=x/(1−a)=x(2/s²+O(1))`, and `t=y/(1−a)=O(1)`.

The derivative of the radial inversion has invertible leading part `2s^−2(I−2 uu^T)` and bounded error, uniformly. Equivalently the angular direction is unchanged and the radial derivative is `−2/s²+O(1)`. Thus for a sufficiently small cap the surface is a graph in the original exterior w-chart as claimed. Both cap normalization and exterior normalization agree with the original boundary on an interior collar and become height zero sufficiently far out. Interpolating their heights therefore compares them through regular graphs with common compact support. This is a verification of the submission's stated graph/cap argument from its stated O(s²), O(s) estimates, not an additional compactification theorem or a repair of the translation.

Finally the source's relative C¹-to-smooth comparison applies on the compact angular sphere to the whole compact parameter family. Near the finite chart axis points use G_epsilon; near e use the standard cap; on the remaining compact region the data are smooth. The perturbations are C¹-small in common coordinate charts, preserve the uniform angular gradient margin, and can be made relative to the fixed cap and endpoint data. Convex interpolation of the angular defining functions keeps that margin. Thus the resulting object is the precise **smooth stable tube class** of g⊕2ab, hence of g. It is not merely a topological tube, a C⁰ isotopy, or equality of real characteristic classes. Compactness supplies uniform radii and a common finite stabilization, also for extra compact parameter families with the stated uniform bounds.

The succinct normal-collar and cap-to-exterior passages above are legitimate applications of the quantitative estimates and the paid relative smoothing operation. They leave no essential mathematical bridge unproved in the submitted proof.

## 11. Natural coset, free classes, and all six pairs

Combining the actual small-germ birth, its explicit separation lift, the zero-regular F_u interpolation, the compact partition homotopy and the smooth stereographic identification gives, integrally,

`natural(L)=[g:Q→T]+i_*[Q,BO]`.

It suffices that the specific doubled representative is this g-class; AIS supplies the ambiguity under all other Gauss nullhomotopies. This closes the precise issue raised by Remark 4.8. For F_j the infinity data are independent of v, so the class is `pr_1^*(j a)`. For the zero section a constant quadratic family yields the zero representative of the rigid coset. Primitive constants do not change it.

If a Hamiltonian isotopy carries L_j to L_k as images, AIS gives equality of these cosets on the same Q. Restriction to the fixed slice `s(b)=(b,v0)` gives `(j−k)a` in the rigid image in degree 9. This subtraction is legitimate: T is the connected stable grouplike homotopy-commutative H-space under direct sum, with the rigid action given by addition; AIS §3.6 and the compatible stable monoid models are the relevant interface. Connected H-spaces are simple, so the pi_1 action on higher homotopy groups is trivial. Likewise BO has the usual additive stable-bundle model. Hence free sphere classes do not introduce further orbits, and the common quadratic pole germs identify the based representatives. There is no replacement of equality over Q by equality after a self-map of the parameter sphere.

For any distinct j,k in {0,1,2,3}, gamma_*((j−k)a)=0. The trivial intersection in §2 forces `(j−k)a=0`, contradicting the order ≥4 of a_(2), since `1≤|j−k|≤3`. This proves every nonzero/nonzero pair and every zero/nonzero pair. Reversing the initial sphere convention changes the common a to −a and changes none of these conclusions. An arbitrary independent re-marking of an image cannot change the natural coset over the fixed ambient base. No orientation, spin structure, Floer grading, real regulator or local coefficient choice is being smuggled into the invariant.

## 12. Auxiliary assertions, scope, and limits of the verdict

The proof's uniformity assertions are used only on compact families with the stated smooth/angular and gradient bounds. Every cutoff has a constant neighborhood of the locus that it must preserve; all annular transitions have the displayed lower gradient estimate; the only degenerate intermediate objects are used as regular zero-level partitions. The positive coefficient rescalings, graph normalizations, defining-function interpolation, direct-sum stabilization, C¹ smoothing and H-space restrictions have all been checked above. The source's Morse, regular-band, h-cobordism, core-straightening and small-step transport mechanisms are paid source truths, fully read and accounted for, not competing proofs of the new pairwise step.

I also read the admitted author derivation notes. The common-endpoint difference function discussed there is indeed Morse–Bott along the diagonal when both generating parametrizations are diffeomorphisms onto the same embedded image: its Hessian kernel consists exactly of pairs representing one tangent vector of that image. Keeping only b as a parameter would omit a momentum equation, exactly as those notes warn. This abandoned route is not used to claim pairwise inequivalence. The prefreeze notes' informal localized-generator wording and earlier birth normalization were explicitly superseded in the actual frozen-proof submission by the integral lift and the exact ACGK birth reviewed above. No author-note assertion of closure or source-reading coverage was treated as a premise.

This review does not independently validate upstream truth, prove an unquoted original theorem from Waldhausen/Igusa/Giroux, or assert formal coverage. The pinned `lean/docs/340.md` endpoint was independently requested and returned HTTP 404. The source and cited primary interfaces are exactly the assumptions at the frozen scope. No contribution review, parent result, peer activity, excluded history body, or source-family successor was read. Actual semantic ranges, the one recovered tool truncation, primary-version limitations, and incidental editorial exposure are given in `READING-ACCESS.md` and the private read log.

**Final role verdict: full-scope correctness PASS for the unchanged frozen statement and submitted proof, relative to the stipulated interfaces.** There is no essential unresolved mathematical obligation to return for repair. The standalone verifier-anchor mismatch is an evidence limitation only and is reported without altering author bytes.
