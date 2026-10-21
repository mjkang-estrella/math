# Global finite descent: strongest integrated reduction and its limit

PREFREEZE / no nominee. This is a research derivation, not a frozen new theorem, an author-proof submission, a conjectural advance or an independent mathematical grade. The pinned source and its operative proofs are stipulated true. The formulas below state credited inputs and consequences to fix the exact scope of the attempted composition.

## 1. The arithmetic objects and the full scope investigated

Let K be a number field and C/K a smooth proper geometrically connected curve of genus at least two. Sec(C/K) means continuous splittings of the FULL arithmetic étale fundamental exact sequence, modulo conjugation by its FULL geometric kernel Δ. We impose no rational base point, no good reduction hypothesis, no birational lifting, no quotient-prime restriction and no rank condition.

Write

    C(A_K)_bullet = product_{v finite} C(K_v)
                   × product_{v real} π_0(C(K_v)),
    D(C) = C(A_K)_bullet^{f-cov}.

Complex factors are omitted. This is essential for disconnected torsors, even though a connected curve itself has a singleton complex component factor. Survival means that for each finite K-group-scheme torsor T→C there is a global twist admitting an adelic lift. Arbitrary finite group schemes, not only constant groups with geometrically connected total space, are retained. Stoll's March2017 erratum explicitly repairs a false component/stabilizer argument; we use the corrected full finite-cover descent formalism. Finite abelian descent and finite geometrically abelian descent are not silently identified when C(K) is empty (BKL2.5–2.7).

The research question was whether the stipulated local section theorem, supplemented by all available finite-descent and period-map operations actually read, forces global rational-point sections. No full theorem was frozen: no proof-feasible new step emerged.

## 2. Both existence and uniqueness of global interpolation are paid

Source019, section08 Proposition localization-image, already proves

    loc(Sec(C/K)) = D(C).

Indeed its local theorem classifies sections at every finite place, and the real section theorem supplies the real component. Properness makes the tuple adelic. Harari–Stix's Theorem2.1, with U=1 and omitted set empty, gives the two directions between global interpolation and finite-torsor survival.

The actual Harari–Stix proof gives more than a label. For each finite geometric quotient, survival supplies a global nonabelian H^1 class with the prescribed local evaluations. Its fibre of globally possible classes is finite. After splitting the finite coefficient group over a finite extension, a locally trivial cocycle is trivial on a dense union of decomposition subgroups by Chebotarev; the remaining classes lie in a finite H^1 of a finite group. Nonempty finite sets of lifts over all quotients have a compatible inverse limit. Finite sets of conjugators have an inverse limit as well. A preliminary interpolating homomorphism is made a section: its composite with G_K preserves conjugacy classes on a dense set, hence everywhere; it is injective, and the elementary Jordan subgroup-counting argument forces surjectivity in every finite quotient. These are actual §§1–2 operations, not a new compatibility bridge.

There is also a stronger PRIMARY input than the pinned global chapter explicitly uses. Porowski, arXiv2312.08005v1, Theorems1.1/1.2 and6.5, proves density-one local-global conjugacy, indeed the finite-covering property for sections. BKL, arXiv2305.09462v2, Theorems2.3/2.7, combines this with Harari–Stix to obtain

    Sec(C/K)^Sel  --loc-->  D(C)     bijectively.

Under stipulated Source019 every global section is Selmer, so the same is a bijection from Sec(C/K). At ANY set Ω of finite places of Dirichlet density one, localization into product_{v∈Ω} C(K_v) is injective. This is a routine composition of the actual sources. It is NOT an r121 contribution, and injectivity must not be listed as unpaid.

Porowski's stronger property must also be carried through: if s,s_1,…,s_m are global sections and at every v in a density-one Ω the localization of s agrees with that of SOME s_i (the index may depend on v), then s equals one of the s_i globally. His proof passes through the abelian finite-covering estimate, inducts through solvable geometric quotients, splits quasi-sections in finite-index neighbourhoods, and uses trivial geometric centralizers to descend equality from a finite constant extension. Compactness then passes through all characteristic neighbourhoods. Reading merely the injectivity theorem would miss this stronger finite-list operation.

## 3. The strongest local finite set already has global representations behind it

Assume now that K contains no CM subfield. Betts–Stix, arXiv2204.13674v1 TheoremsA/B, gives finite sets

    L_v(C) = loc_v(Sec(C/K)) = pr_v D(C) ⊂ C(K_v)

for EVERY finite v. There is no condition of good reduction, v∤2, or unramified K_v/Q_p. Their proof deals with these cases; they are not proposed improvements.

At a chosen v|p take the Kodaira–Parshin abelian-by-finite family

    X_q → C'_q → C.

The relative H^0 and H^1 local systems give representations A,V of π_1(C), with their algebra and symplectic-module structures. Restriction along s gives ONE pair (A_s,V_s) of G_K-representations. At every place u its restriction is isomorphic to the cohomology of the fibre above x_u(s), including its algebra and polarization. Thus the local points already admit simultaneous global interpolation. This is Betts–Stix7.2/7.1, not a separately owed realization step.

The pair is S-good for suitable finite S: unramified, pure and integral of the specified weights outside S, de Rham at p, with Hodge–Tate weights in {0,1}. The stronger adelic LV locus is contained in the S-good local locus by6.4. Their6.5 selects q and proves the local locus finite using the principal trichotomy; the full-monodromy period map and dimension bounds handle two branches, and the chosen Kodaira–Parshin family rules out the third. Its final analytic operation, Corollary5.10, is explicit: on a closed analytic disk U, the period map has Zariski-dense image in the appropriate Grassmannian, while the relevant representations place its image in a proper algebraic subset. The inverse image is a proper closed ANALYTIC subspace of a one-dimensional disk, hence finite. Compactness covers C(K_v) by finitely many disks.

Consequently source019 + the full available reduction gives a global section set bijective to a descent locus with finite coordinate projections, and with Porowski's finite-covering property. The new local theorem removes the qualifier Selmer; it does not make these already-primary conclusions new mathematics.

## 4. Run the construction on the entire section-neighbourhood tower

Fix s and let U⊂Δ range through open characteristic subgroups. The subgroup Π_U=U s(G_K) is open in π_1(C), projects onto G_K, and corresponds to a finite étale geometrically connected cover C_U/K with a lifted section s_U. It is proper and has

    2g(C_U)−2 = [Δ:U](2g(C)−2)>0.

The base field is STILL K. Thus if K has no CM subfield, the same condition holds at every stage; no illicit extension of that condition to arbitrary new fields is needed. At every finite v, source019 determines a point x_{U,v}∈C_U(K_v). These points commute with transition maps: pushforward of the section of x_{U',v} is s_{U,v}, and local section injectivity identifies its image with x_{U,v}.

This actually gives compatible local points on the whole pro-cover. It is not merely unrelated nonempty local solution sets. Betts–Stix also makes the set L_v(C_U) of localizations of ALL global sections on each C_U finite. The image

    E_{U,v} = image(L_v(C_U) → C(K_v))

lies in L_v(C) and contains x_v(s). As U decreases these images decrease. A directed decreasing collection of subsets of a fixed finite set stabilizes: for each element absent from the intersection choose a stage excluding it, then take a common refinement of the finitely many stages. So the images downstairs stabilize, independently for each v.

This exhausts the natural finite-set/compactness operation; it does NOT supply C_U(K)≠∅. In fact x_v(s) was already a persistent member before applying finiteness. Stabilization of the projected image downstairs is not stabilization of covers, of global twists, of arithmetic fields of points, or of global rational lifts. The stages selected for different v need not coincide. The tower already has compatible local points, so producing those points again is not progress toward a rational point.

For comparison the global endgame is fully paid IF every C_U has a K-point. Images of C_U(K) in C(K) then have the finite intersection property and lie in the finite set C(K) (Faltings). They share a point a. For the fixed a, finite fibres above a have compatible K-points after common refinement, hence an inverse-limit K-point. Equivalently every characteristic neighbourhood of s contains a conjugate of s_a, and Porowski3.1/Stix's section-neighbourhood criterion gives s=s_a. This is a credited endgame, not a proof that the required rational points exist.

## 5. Even the strongest topological/finite-list data do not force finiteness formally

Here is a diagnostic, NOT an arithmetic counterexample or an impossibility theorem. Let S={0,1}^N with its compact product topology, and r_n:S→{0,1}^n be the prefix map. Every r_n has finite image; the full localization map is injective and remains injective on ANY infinite subset of indices, hence on any density-one subset.

It also satisfies the precise finite-list rigidity analogous to Porowski. If x differs from each of x_1,…,x_m, choose N larger than all their first positions of difference. For every n≥N, r_n(x) differs from every r_n(x_i). Thus a finite list cannot cover x on a density-one set unless x is one of that list. Nevertheless S is infinite, even uncountable. Its finite-level inverse systems are nonempty, compatible and surjective.

This model respects finite coordinate images, compact inverse limits, density-one uniqueness and finite-list covering rigidity SIMULTANEOUSLY. It shows exactly why these abstract properties alone do not finish the proposed argument. It does not model the curve's Galois representations, purity, period maps or all arithmetic constraints, and therefore cannot rule out a genuinely arithmetic additional argument. No such argument was constructed here.

## 6. What finite support actually means, and why analytic dimension zero is different

For a fixed section s it is enough to find a finite K-subscheme Z_s⊂C such that

    x_v(s) ∈ Z_s(K_v)  for all v in some density-one set Ω_s.

Z_s and Ω_s may depend on s; a bound uniform in all sections is not needed. Since loc(s)∈D(C)⊂C(A_K)_bullet^{f-ab}, Stoll8.2 immediately makes the entire modified tuple diagonal at a point a∈Z_s(K). Porowski then identifies s=s_a. Alternatively Stix Corollary5 gives the same conclusion using the rational points on neighbourhood fibres. The broader finite-list operation therefore does not need to be reinvented.

For clarity, Stoll's actual proof passes to a finite extension embedding C in its Jacobian, applies the finite-scheme theorem3.11 there, and descends. The key estimate is3.4: for a finite-level Selmer class whose multiple m has order n after killing a uniformly bounded cohomological kernel, the density of completely split places with trivial localization is at most 1/(n[K_N:K]). For finitely many differences from points of Z, choose n>#Z and a common division level. Their vanishing sets cannot cover all split places. Thus a candidate Selmer element is torsion away from a point of Z; one local equality and injectivity on torsion finish. This argument REQUIRES a fixed finite algebraic list to form those global differences. The place-dependent analytic sets L_v do not provide it.

At one place, a finite Kv-analytic locus may have points transcendental over K. The elementary diagnostic f(T)=T−α with α∈K_v transcendental over K has a one-point analytic zero locus, but the map K[T]→K_v, T↦α, is injective; its scheme-theoretic image over K is dense in A^1. On a K-curve the analogous nonalgebraic Kv-point has generic image. This is only a warning about the inference from analytic dimension zero, not a claim that a Betts–Stix period locus contains such a point.

Even algebraicity separately at every v does not provide one finite K-subscheme. The union of algebraic points used at varying places can be infinite. A fixed degree bound by itself also need not give a finite set: the smooth projective genus-two model of y²=x⁵−x admits infinitely many points of degree at most two by taking x∈Q; its five finite roots are distinct, and the hyperelliptic double cover has genus two. This is not a family of counterexamples to finite descent, merely an explicit reason not to replace finite support by a degree-only assertion.

A common bound on degree AND absolute logarithmic height in a fixed projective embedding would give finite support by Northcott, hence the rest would again be paid. For an algebraic coordinate of degree≤D and height≤H, the primitive minimal polynomial has Mahler measure≤exp(DH), so each coefficient is bounded by 2^D exp(DH). There are finitely many such integral polynomials and finitely many roots; apply this to projective coordinate ratios. But the source and primary period arguments read give neither bound for the local candidates. This observation is not a nominated uniform/effective height target and does not alter H73 or any old height statement.

## 7. The sharper Chabauty composition also stops at this same operation

BKL v2 Lemma2.19 maps a finite-descent tuple, through its global section, into every appropriate refined Chabauty–Kim locus. Its proof is the functorial map from the full geometric fundamental group to the chosen pro-unipotent quotient; local Kummer maps commute with restriction. Corollary2.20 then proves: if those local loci equal the rational/integral points for a density-one set of auxiliary primes, the finite-descent tuple is diagonal. Theorem2.21 records the number-field version. These are actual operative proofs read before this note.

Thus imposing all these p-adic constraints does not leave an unpaid section-to-Kim compatibility, missing twist choice or finite-support-to-point theorem. What is unavailable here is a derivation of algebraic finite support from the finite period-map loci WITHOUT assuming the desired Kim equality or a finite-support conjecture.

Betts2508.19947v1 makes the same distinction explicit in introductory Conjectures1.1/1.2: finite subschemes independent of p are stronger than finite p-adic obstruction loci. Its TheoremA proves a rank-zero quadratic case. We read that statement, not its operative proof, and use it only to limit our claims about what a theorem title promises. We neither import it as a general result nor select its once-punctured elliptic direction. No general support result is inferred from an abstract or from that special case.

## 8. Outcome and unchanged older scopes

The full integrated construction now includes compatible global twists, full local point-theoreticity, global section/finite-descent BIJECTION, density-one injectivity, finite-list rigidity, global period representations, all finite-place local finiteness and compatible local points through every section neighbourhood. These are paid, including the newer Porowski/BKL operations absent from the pinned chapter's explicit final conclusion.

No proof-feasible nonroutine operation remains established by this round beyond those inputs. The attempted additional implication to finite K-support has NOT been proved. This is an honest limit of the construction, not a renamed new gap, a substantial partial result, an impossibility theorem, an exhaustion claim or a worldwide-priority claim. No theorem is frozen and no supporting/full nominee is submitted.

Actual r59 original scope and proof attempts, plus r60 full candidate-proof, were read. Their all-prime two-prime quotient-section target stays unchanged and is not retried. The global full-group construction here does not restrict that target or claim a new proof of it. The supplied exclusions prevent full reading of later overlapping affine-section archives; those remain uncleared. All other old scopes and dispositions supplied in the brief remain immutable, including H73, T360S147, H138/T185R144 and the other named full/technical/failed targets. Parent alone may integrate/review/count.

Source/primary/transitive reading is selective: complete relevant source07/08 and exterior companion sections; selected Betts–Stix proof interfaces and final assembly, not all Hodge-theoretic foundations; substantial actual Harari–Stix, Stoll, Stix, Porowski and BKL operative proof reads as itemized in READING.md. No fresh complete proof audit of stipulated inputs was attempted.
