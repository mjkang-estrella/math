# Integrated calculation: simultaneous norms and signed permutation lattices

**PREFREEZE / no nominee.** This is a sustained reduction and comparison, not a frozen substantial theorem or an independent grade. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true. The calculation identifies what the source and classical operations already pay. No project-novelty or new-to-literature claim is made.

## 1. Working objects, with all norm equations retained

Let k be a number field. Let F/k be a finite separable extension of degree m>=3, P its normal closure, and L/k a quadratic extension with P intersection L=k. Put E=FL, G=Gal(P/k), X=Hom_k(F,P), Gamma=G x <c>, c^2=1. The action of G on X is transitive. No restriction on ramification, real places, dyadic places or local factorization is imposed.

Write

    W=Res_F/k(Res1_E/F Gm), U=Res1_L/k Gm,
    T=ker(N_E/L:W -> U).

Over a separable closure the dual norm map is the primitive diagonal inclusion

    Z_sign -> Z[X] tensor sign, 1 -> sum_{x in X} e_x.

Hence T is a connected torus, of dimension m-1, with character lattice

    M=J_X tensor sign, J_X=Z[X]/Z1.

The action of c on M is -1. All uses of quotient lattices here retain their integral structure; replacing them with a rational representation or just their mod2 reduction before testing cyclic splitting can lose information.

For h in F*, d in L* with N_F/k(h)=N_L/k(d), consider the FULL equations

    N_E/F(a)=h,  N_E/L(a)=d,  a in E*.

The corresponding solution variety X_(h,d) is geometrically nonempty: write the coordinates as a_i^+,a_i^-; choose the a_i^+ with product d^+ and set a_i^-=h_i/a_i^+. The remaining product equation follows from the compatibility. Quotients of two solutions lie in T. Thus it is a T-torsor, with all norm equations exact.

In fact these equations represent every T-torsor over k. Let Q be the kernel of N_F/k(h)/N_L/k(d) on Res_F/k Gm x Res_L/k Gm. The same coordinate calculation gives an exact sequence of tori

    1 -> T -> Res_E/k Gm -> Q -> 1.

Hilbert90 gives H1(k,Res_E/k Gm)=0, so Q(k) -> H1(k,T) is surjective. Thus a statement about all compatible pairs is not being silently weakened to a special subset of torsors. At each completion the analogous statement holds, including split etale factors. Weak approximation means simultaneous approximation to prescribed solutions in any finite collection of completions, not integral or strong approximation outside a set.

## 2. Actual source and primary interfaces

The number-field source foundations.tex599–855 contains, in full, cyclic detection (lem:foundations-cyclic-detection), the central sign extension proof (lem:foundations-sign-extension), and the symmetric norm-torus lemma (lem:norm-torus). Its exact case is G=S_m on m letters, for every m>=3. The m=4 argument retains the integral condition (1+r)d_r=0 before deducing the fixed-coordinate equality modulo2. The source has already paid this case; a mod2 calculation that forgets that condition cannot be offered as its gap.

The function-field companion04-norm-tori.tex was read in full. It reproduces the lattice proof and gives the exact compatible-pair/torsor construction just used, as well as its global-function-field duality references. It is a comparator, not a characteristic-two replacement claim. No new function-field theorem is proposed here.

For a finite splitting group Delta acting on a lattice N, write

    K(Delta,N)=ker[H2(Delta,N) -> product_(C cyclic in Delta) H2(C,N)].

The source's cyclic detection identifies this with Sha_omega^2(k,N). Number-field torus duality gives the exact sequence

    0 -> A(T) -> K(Gamma,M)^dual -> Sha^1(k,T) -> 0,

where A(T) is the defect of weak approximation and Sha^1 is the group of everywhere locally trivial torsors. In particular K=0 gives both desired properties. For a fixed arithmetic realization, the subgroup Sha^2(k,M) is the kernel of restriction to all actual decomposition groups, not just cyclic subgroups; its dual is Sha^1(k,T). This distinction is essential when K is nonzero.

Actual primary reading includes Sansuc1981 printed13,57–60,65–72, visually from the scanned volume. These include the torus pairing and proof8.3–8.4, the full theorem8.5 proof, the full weak-approximation proof8.12, corollary8.14,9.4–9.5 and their proofs, and proposition9.8 and its proof. The earlier class-formation/Poitou–Tate foundations and all intermediate lemmas are not claimed freshly read in full. The source interface itself is stipulated.

Pollio–Rapinchuk2013 section5, Proposition15 and Lemma16 were read in full, including the restriction/Shapiro proof; Demarche–Wei's7January2013 version, Theorem1 and Lemmas3–4 with their proofs, were read in full. They prove vanishing for PRODUCT-of-norms tori. Their character sequence is

    0 -> Z -> Z[G1/H1] directsum Z[G2/H2] -> N -> 0.

Our sequence is instead

    0 -> Z_sign -> Z[X] tensor sign -> M -> 0.

These are different integral lattices (even their ranks differ). Their product-of-norms theorem cannot simply be relabelled as simultaneous prescribed norms. But their actual proofs show that permutation splitting, Shapiro, cyclic detection, and restriction arguments are established operations. This is a compatibility comparison, not an assertion that a theorem-title mismatch proves contribution.

## 3. The source's central-sign map is a full cohomology calculation here

Set Q_X=M/2M=F2[X]/F2 1. The source constructs an injective map

    H2(Gamma,M) -> H1(G,Q_X).

It is surjective for this direct-product action, by an explicit standard construction. For a normalized1-cocycle b:G->M/2M, form the subgroup

    E_b={ (a,(g,c^epsilon)) in (1/2 M) semidirect Gamma :
                      a mod M = b(g)/2 in (1/2 M)/M }.

The congruence is preserved under multiplication: c acts trivially modulo2 and b(gh)=b(g)+g b(h). The kernel over Gamma is precisely M. A lift (0,c) conjugates the lift (b_g/2,g) to (-b_g/2,g); its translation difference reduces to b(g) modulo2. Thus the source's map sends this extension to b. Coboundary changes give equivalent extensions (conjugate by a half-integral translation, with an integral correction). Together with the source's injectivity this gives

    H2(Gamma,M) = H1(G,Q_X).

This is a cochain/universal-property completion of the stated source operation. It is not a new nonroutine theorem. In particular this group is killed by2. Equivalently, conjugation by the central element c acts trivially on group cohomology, whereas its coefficient action is -1, so twice any class is zero.

For future exact calculations one must retain cyclic restrictions. Let r=(g,c^epsilon), n=ord(r), and let

    N_r=1+r+...+r^(n-1) acting integrally on M.

Choose any integral lift b_g of b(g). In E_b the n-th power of (b_g/2,r) is N_r b_g/2. Therefore the cyclic restriction vanishes exactly when

    N_r b_g lies in 2 N_r M.

The vector is already in2M by the cocycle condition. The issue is membership in twice the INTEGRAL norm image, not just divisibility by2 in M. Replacing b_g by b_g+2a changes the half norm by N_r a. Coboundary changes preserve the extension class and this criterion. This supplies a precise finite reduction for any transitive G; recording that reduction is not itself a substantial discovery.

## 4. The arbitrary odd-degree case is already paid

Let H be the stabilizer of x0 in X, so [G:H]=m. As an H-lattice,

    J_X -> Z[X minus {x0}], [a] -> (a_x-a_x0)_(x != x0)

is an integral isomorphism. Its inverse uses representative a_x0=0. It commutes with H and with the sign action. Thus M restricted to H x C2 is a direct sum of induced rank-one sign lattices, one for each H-orbit in X minus{x0}.

Such a signed permutation lattice has zero cyclic kernel. Here is an algebraic verification rather than a tacit rationality assertion. A summand is induced from K x C2 with coefficient Z_sign. Shapiro and the central-sign calculation identify its H2 with

    H2(K x C2,Z_sign)=H1(K,F2)=Hom(K,F2).

If a character chi is nonzero, pick h in K with chi(h)=1. Its order d is even. Restrict to the cyclic subgroup generated by (h,1), on which Z_sign is trivial. A lift in the half-integral model has d-th power d/2 modulo dZ, a nonzero element of H2(C_d,Z)=Z/d. Restriction followed by evaluation on the fixed coset is the Shapiro component; hence a globally cyclically trivial class must have chi=0. This applies to each summand. It agrees with the geometric fact that a restriction of a quadratic norm-one torus is rational.

If alpha belongs to K(Gamma,M), its restriction to H x C2 is still cyclically trivial, hence zero. The usual restriction–corestriction identity then gives m alpha=0. Section3 gives2 alpha=0. For odd m, Bezout gives alpha=0. Thus all locally soluble simultaneous-norm torsors in section1 have a rational point and weak approximation, for arbitrary odd m and arbitrary transitive G with the specified disjoint L.

This is stronger in its group parameter than the source's odd S_m case, but the entire operation is signed permutation splitting, Shapiro, cyclic detection and transfer. No new obstruction-removal construction remains. It must not be nominated on the strength of hypothesis removal alone. This calculation says nothing about rationality of T itself, effective heights, uniform integral models, strong approximation or an algorithm to find the global point.

## 5. The regular-action even-degree reduction

Now suppose F/k is Galois, so X=G with the regular action. This is a comparison subcase, not a substitute frozen target. The regular F2-module V=F2[G] has no positive-degree cohomology, by Shapiro from the trivial subgroup. Consequently the boundary of

    0 -> F2 -> V -> Q_G -> 0

gives H1(G,Q_G)=H2(G,F2). Combining with section3 identifies H2(Gamma,M) with H2(G,F2). One must still compute the CYCLIC restrictions in Gamma; it would be wrong to equate the whole groups with the arithmetic obstruction.

Fix g of order d. Its cycles in the regular action all have length d.

* For r=(g,1), any invariant class in J_G has a genuinely g-invariant integral representative: if gu-u=a1, summing coordinates gives a=0. Such representatives are constant on each cycle. The norm of a coordinate vector is the indicator of that cycle, so the norm map surjects onto the invariants. Hence H2(<r>,M)=0.

* For r=(g,c) and d odd, r has order2d and r^d acts as -1. Its invariant lattice is zero, so H2(<r>,M)=0 again.

* For r=(g,c) and d even, r has order d. On each cycle let v_j be the alternating vector(1,-1,1,-1,...). The norm image is the lattice generated by the v_j. The invariant lattice additionally contains the class w with coordinates(1,0,1,0,...) on every cycle, for which2w=sum_j v_j modulo the diagonal. Every invariant class has this form: the equation u+g u=a1 forces the same pair sum a in all cycles, and its parity is the only extra possibility. Thus M^r/N_r M has order2.

Choose an integral representative of b(g) in Z[G]. Let t_j be its alternating sum on the j-th g-cycle. The norm N_r b_g is sum_j t_j v_j. The mod2 cocycle identity N_g b(g)=0 in Q_G forces all t_j to have the same parity. The half norm belongs to N_r M exactly when that common parity is zero. Therefore the cyclic restriction is detected by the common cycle-sum parity.

For the connecting class eta in H2(G,F2), restriction to <g> is represented by exactly this parity. Indeed choose lifts of b(g^i) in V and sum the connecting factor sets on(g^i,g); the terms telescope to N_g b(g), which is the common scalar times the diagonal. For even d, this scalar is the class in H2(C_d,F2)=F2. For odd d the latter group is zero. We obtain the precise regular-action comparison

    K(G x C2, J_G tensor sign)
       = ker[ H2(G,F2) -> product_(C cyclic in G) H2(C,F2) ].

All steps are Shapiro, the integral cyclic norm formula and the source central-sign operation. This is not a nominated nonroutine operation or a general new-to-literature claim.

## 6. Why blanket vanishing cannot be inferred

There are nonzero cyclically split central2-extensions. A useful diagnostic is the finite quaternion GROUP Q8, unrelated to the division-algebra/orthogonal completion family of r123. Its abelianization is C2 x C2. Consider the connecting homomorphism

    delta:Hom(Q8,F2) -> H2(Q8,F2)

from0->F2->Z/4->F2->0. It is injective: every homomorphism Q8->Z/4 factors through the exponent2 abelianization and has image in{0,2}, so its reduction modulo2 is zero. Thus delta has a2-dimensional image.

Every such class restricts trivially to every cyclic subgroup. A cyclic subgroup of order4 permits any character to F2 to lift to Z/4. The only subgroup of order2 is generated by -1, and every character of Q8 kills -1. Naturality of the connecting map proves cyclic triviality. Hence the regular-action cyclic kernel contains(F2)^2. This is an exact proof of nonvanishing, not a failed naive route being mistaken for an obstruction.

A small normalized bar-complex diagnostic independently finds dim H2(Q8,F2)=2 and cyclic-kernel dimension2. It also finds zero cyclic kernel for C2,C3,C4,C6,C8,C2xC2 and D8. The script uses exact binary row elimination on cocycle equations and restriction-to-cycle sums, checks its finite multiplication tables, and has a30-second bound. These finite checks are ancillary; the nonzero lower bound above is proved without them. No general classification or mathematical review gate is supplied by this diagnostic.

If a number-field realization has Galois group Q8 and an independent quadratic L, the exact duality sequence says that at least one of weak approximation for T and the Hasse principle for its torsors fails. It does NOT identify which, absent the actual decomposition groups. No explicit number-field realization or explicit insoluble compatible norm pair is constructed here. No such counterexample is nominated. In particular cyclic detection does not permit us to declare Sha^1=(F2)^2 without checking every decomposition group.

## 7. A second exact reduction of prescribed norms

The same compatible-pair problem has an elementary useful reformulation, which explains why a product-of-norms theorem is not automatically the right theorem. Suppose local solutions exist. By the classical quadratic Hasse norm theorem, choose a0 in E* with N_E/F(a0)=h. Put

    delta=d/N_E/L(a0) in L*,  N_L/k(delta)=1.

Choose z in L* with delta=z/c(z) by Hilbert90. Every norm-one correction a/a0 is y/c(y), y in E*, again by Hilbert90 for E/F. Its norm to L equals delta precisely when

    N_E/L(y)=z t for some t in k*.

Indeed equality of the quotients by c says N_E/L(y)/z is fixed by c, hence lies in k*. Conversely that identity supplies the required correction. Locally the same equivalence holds over etale products. Thus the remaining existence question is a PROJECTIVE norm class of z modulo k* N_E/L(E*), not an ordinary product-of-norms equation in independent variables over k.

For approximation one cannot discard the local y's or their scalar choices merely because a global equality of norm groups is known. The T-torsor calculation and vanishing in section4 already pay that simultaneous approximation in odd degree; the reformulation does not introduce an extra unpaid approximation bridge. Likewise it does not prove vanishing in arbitrary even degree: section6 shows that the general obstruction can be nonzero.

The invoked classical quadratic Hasse norm/Hilbert90 inputs are identified, not claimed newly proved. Their complete original transitive literature was not freshly read. This section is a comparison calculation after the primary reads, not the foundation of a nominated author proof.

## 8. What remains and what does not

The source completely pays the S_m case, including even degrees and its m=4 integral condition. Standard composition pays all odd-degree disjoint cases above. For regular G the remaining cyclic kernel is exactly the classical group-cohomology restriction kernel, with a concrete nonzero pattern for Q8. General transitive G reduces to the explicit integral norm-image condition in section3. Actual arithmetic failures, when that kernel is nonzero, require the actual decomposition-group restrictions, not a rename of the kernel.

No further nonroutine arithmetic operation after these reductions has been isolated. A new full-scope nominee would need a specified new construction or classification beyond this paid composition, together with actual overlap and primary comparisons. An uncomputed general even-degree kernel, an unspecified realization with convenient decomposition groups, or explicit torsor equations without a complete obstruction computation are not proposed as findings. The record therefore stays PREFREEZE/no nominee. It makes no exhaustion claim about norm tori, and no claim that every neighboring theorem is impossible.

All old frozen scopes and dispositions remain immutable. In particular no all-depth/all-degree r80 target, closed r122 metric result, r123 completion calculation, T360S147/H138/T185R144 disposition, or other supplied full target is replaced by these calculations. No independent correctness, contribution, acceptance or count is assigned. Parent alone integrates, reviews and counts.
