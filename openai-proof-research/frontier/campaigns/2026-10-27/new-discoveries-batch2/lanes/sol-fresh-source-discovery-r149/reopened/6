# Author proof for the immutable statement T054L136

This is a discovery author proof, conditional on the task's stipulated truth of SOURCE054 and its operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The statement is exactly FROZEN.md, SHA256 cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77. No claim of independent correctness, substantial contribution, acceptance, or count is made. This document is not a manuscript or local release.

## 1. Conventions and the source operations being used

All varieties and fields are over C. Cohomological lattices of surfaces mean integral cohomology modulo torsion. T(S) is NS(S)^perp with its cup-product form. The cubic lattice T(X) has the opposite polarization after the usual shift from weight two to weight four; write T(S)[-] for that shifted, sign-reversed polarized Hodge lattice. Absolute discriminants are used when signatures differ. A finite-order automorphism means a nonidentity automorphism of finite order, with no assertion about infinite-order automorphisms.

For a collection S of K3 surfaces, define u(F) to be1 exactly when the MRC quotient of a smooth projective model of F is birational to a member of S. On a finite etale algebra, u is the sum over field factors, with coefficient1 per orbit, not the extension degree. The divisorial cocycle c_u has SOURCE054's sign convention: valuations present on the target and absent on the source contribute positively. A blowup contributes u of its center. The MRC and cocycle arguments in pre:mrc-fibration and pre:cocycle do not require Picard rank one.

The source's gw:blowup and gw:blocks give more than a rational Hodge decomposition: a blowup of a rationally connected fourfold along a surface adds its entire integral transcendental lattice as one separately identified scalar operator block. Along weak factorization those whole blocks can be matched and cancelled; a proper summand of a surface block cannot be substituted. We use these results as stipulated, including their genus-zero reconstruction operations. The rank21 assumption first enters the classification of a surviving center in gw:k3-center, not the whole-block result. Section4 below replaces that classification at rank20.

The geometric part of the source is a uniform vanishing theorem for c_u. Section2 below proves the precise extension of that operation needed here. Its proof retains the marked covers, embedded subfields, relative MMP order, and endpoint corrections of the source; it does not infer an extension merely from the final rank-one theorem.

## 2. A version of the source test controlled by divisor squares

For a projective K3 surface S let

    mu(S) = min { D^2 : D in NS(S), D^2>0 }.

The set is nonempty since S is projective. Consider any collection S satisfying all three conditions:

(a) NS(S) has no nonzero isotropic vector;
(b) mu(S)>2B;
(c) S has no nonidentity finite-order automorphism.

We prove that there is a single integer B0, independent of the collection and its discriminants, such that for B>=B0 the source's conclusion sf:vanishing holds with this test collection.

### 2.1 Pencils and bounded MRC bases

Resolve a dominant rational map S --> C by point blowups pi:Y->S, and then take Stein factorization. Since q(S)=0, the connected base is P1. Let F be a smooth connected general fiber and C0 its image divisor class on S. The moving pencil has no fixed component; distinct general members have no common component, so C0^2>=0. Its class is nonzero. Condition(a) gives C0^2>0, and hence C0^2>2B. In the orthogonal total-transform exceptional basis,

    F=pi^*C0-sum m_i E_i,    K_Y=sum E_i,    m_i>=0,
    C0^2=sum m_i^2,          2g(F)-2=sum m_i.

Consequently 2g(F)-2>=sqrt(C0^2)>sqrt(2B). This also applies to each normalized geometric general fiber component of an arbitrary map to a curve, by Stein factorization. This replaces the sole use of C0=nL in bd:pencil.

If a smooth projective surface Y in a bounded family is birational to S, its minimal-model map mu:Y->S is a succession of point blowdowns. For a chosen very ample divisor A on Y, write A=mu^*D-sum a_i E_i. The pushforward D is ample, since its square increases and all curve intersections stay positive at each contraction. Thus

    2B < D^2 = A^2+sum a_i^2 <= A^2+(A.K_Y)^2.

After finite stratification the right side is uniformly bounded. This replaces the use of D=nL in bd:surface-degree.

For a bounded collection of threefolds whose MRC bases are K3 surfaces, the remainder of bd:bounded-mrc produces a bounded collection of smooth birational models of those bases without using rank one: degrees of free rational curves are uniformly bounded on the uniruled locus; a fiber of the one-dimensional MRC fibration is the image of such a curve; its Hilbert point belongs to one of finitely many Hilbert schemes of polynomials en+1. The corresponding two-dimensional fiber components are birational to the K3 bases. Their bounded models therefore satisfy the preceding inequality. This is the actual source Hilbert-space argument, not an assumption of boundedness for arbitrary MRC maps.

### 2.2 Marked covers and geometric generic fibers

The four exclusions in bd:exclusions continue to hold with sufficiently large B. For curve covers of degree e<=N unramified off r marked points of a genus-h curve, Riemann--Hurwitz gives

    2g-2 <= e(2h-2)+(e-1)r.

For a bounded marked surface pair, a general hyperplane pencil has bounded genus and bounded intersections with the boundary. Pulling it to any such cover bounds the genera of normalized components, uniformly in the cover. Section2.1 excludes the cover from being a test K3. For surface fields mapping to a curve with these bounded geometric fiber covers, the same pencil argument applies after Stein factorization; the genus of the base curve is irrelevant.

For a threefold mapping to a curve with bounded uniruled geometric surface fibers, suppose its MRC base were a test K3 S. If the map to the curve were nonconstant on a general MRC fiber, a geometric surface fiber would dominate S generically finitely, contradicting non-uniruledness of S. Otherwise the map descends to a pencil on S. A geometric surface fiber dominates its curve fiber; pullback of one-forms bounds that curve's genus by the irregularity of a bounded smooth surface model. This again contradicts Section2.1 for large B. All these bounds persist after extension of algebraically closed fields. No boundedness of the total space over the curve has been assumed.

### 2.3 Automorphisms and the surface correction

The adapted small-orbit assertion is as follows: a surface field with a nonidentity finite-order C-automorphism is not counted by u. Indeed, on a test K3 its birational automorphism extends to a regular automorphism of the same finite order. In particular a degree-two extension of C(x,y) is not counted; the degree-one field is rational. We do NOT use the source's stronger assertion for arbitrary C-automorphisms.

Here is the full list of downstream automorphism uses in the source's operative surface/subfield proof. In sl:small-orbits they are quadratic k-automorphisms. In sl:conic-h each nonsplit component field L/K has its quadratic involution; L can have high degree over the original base field. In sl:w-def and sf:candidate, complementing a choice of one component in each of three singular fibers is an order-two equivariant map of the eight-element orientation set. An orbit fixed by complementation has a nonidentity order-two field automorphism and is not counted. Other orbits pair up with equal u-values, making one half of their total an integer. All these uses survive condition(c). The Geiser/Bertini involutions in the two-ray surface classification are operations on del Pezzo surfaces, not forbidden automorphisms of test K3 surfaces; that classification is unchanged.

Keep exactly the source's finite class sets for del Pezzo degrees5 and6 (of sizes5 and3), its conic correction (one half of the orientation-set test when there are three singular fibers, zero otherwise), and its vertical valuation function v. The source's actual Galois-set identities in sl:pencil-sets and sl:surface-identity therefore prove the same generic surface-link identity. No replacement by rational permutation representations or Gassmann equivalence is needed. In a nontrivial conic two-ray link, positivity of the common del Pezzo degree gives r=8-K_W^2<=7. Identical conic structures, whose discriminant can be larger, are handled by the structured-isomorphism case, not incorrectly forced into this inequality.

### 2.4 Uniform diagrams and embedded subfields

First choose the ordinary fourfold Sarkisov diagrams of bd:diagrams. Those diagrams, with their contraction morphisms and bad loci, are supplied independently of u. Their central discrepancy bounds, log-Fano boundedness, and contraction-model boundedness are stipulated source operations. Use bd:choice-order to choose one rational c with 0<c<1/4 from the ordinary diagrams' full visible ramification supports. Only then use the auxiliary threefold log diagrams with discrepancy lower bound1-c and the bounded extraction of places with log discrepancy<=1. Thus the choice of c cannot depend on a K3, a factorization length, or the auxiliary diagrams that it is used to bound.

For a conic node with base field L of transcendence degree3 and quaternion class alpha, an eligible k is an EMBEDDED surface subfield of L whose smooth projective generic curve is geometrically integral of genus zero, and for which the ramification set Delta_k has degree r_k<=7. Retain the candidate

    sigma_k = u(Delta_k) + (1/2)u(P_k) if r_k=3,
    sigma_k = u(Delta_k) otherwise.

Residues, residue double covers, and their visible support are formed over the original fields. In a bounded marked diagram Y->S, sf:residue-bound first uses the two consecutive residue maps with composite zero to make each residue cover unramified away from component intersections, then purity to obtain an etale open. Deleting the diagram's bounded bad locus produces finite etale sets of degrees r_k,2r_k, and8. Every field factor consequently has degree<=14 and bounded branch locus. Section2.2 excludes its being a test K3. Over a curve, base-change THESE original covers and supports to the algebraic closure of the curve field, even if the Brauer residues then become zero. The same genus bound excludes every factor. Thus sf:residue-bound holds in precisely both forms used by the source.

The source's first-departure proof sf:unique can now be applied without a changed premise: run the auxiliary c-boundary log path comparing eligible presentations. If a nonzero candidate had another eligible embedded surface field, its first departure from the original surface field would occur in a bounded marked diagram; the preceding paragraph would force that candidate to vanish. It is the embedded field, not merely its abstract isomorphism class, that is unique. A zero candidate cannot coexist with a nonzero one from a different eligible field.

The endpoint argument sf:conic-end is also retained in its full scope. For an arbitrary eligible embedded k at an ordinary endpoint, the source runs the relative negative program first over the conic base and then over the common base Q. It uses the same c, full visible boundary, and discrepancy<=1 extractions in a bounded terminalization. Either there is a first departure, to which the preceding argument applies, or the final endpoint itself gives the bounded marked diagram. Thus sigma_k=0. This does not assume that k contains C(Q); when an inclusion is required for a geometric generic diagram, it is obtained in the source's departure/endpoint construction, not imposed on the arbitrary initial k. The parallel surface endpoint argument sl:low-base/sf:surface-end uses exactly the four exclusions of Section2.2.

Define s=0 on bases of dimension<=1, the source del Pezzo correction w on bases of dimension2, and the unique nonzero sigma on conic bases of dimension3 (or zero if there is none). It is intrinsic by the preceding paragraphs. In a link with common base Q, the source vertical identity gives

    c_u(link)-Delta v = H_Q.

If dim Q<=1, the exclusions give H_Q=0 and both endpoint s-values zero. If dim Q=3, the conic fields and classes identify, so H_Q=Delta s=0. If dim Q=2, the source two-ray calculation gives the horizontal contribution Delta w. On a del Pezzo side h_Q=0 and s=w; on a conic side h_Q=-u(Delta_k) and s=w-h_Q. Thus H_Q=Delta s, including zero candidates. Structured-isomorphism links also give zero by the identification of their actual fields and corrections. Therefore every link satisfies

    c_u(link)=Delta(v+s).

On Mori spaces over points, v=s=0. Summing a finite factorization proves c_u=0 between any two terminal Q-factorial rationally connected fourfold Mori spaces over points.

There are only finitely many types of bounded families in this construction, as supplied in bd:choice-order and sf:residue-bound. Let C be the maximum of all bounds A^2+(A.K)^2 for their bounded surface models and all squares max(0,2G-2)^2 for the fiber-genus bounds above. Enlarge C for all fixed bounded cover degrees used in the del Pezzo/class constructions. Choose any integer B0>=2 with 2B0>=C. Then mu>2B and the strict pencil inequality give every required exclusion for B>=B0. This establishes the claimed uniform test extension. It is an existential choice, with no effectivity claim.

## 3. Uniform local obstructions for all complements of one T

Put N_a=<2a> perpendicular <-2(a+1)> and D=4a(a+1). Its determinant is -D. Since a^2<a(a+1)<(a+1)^2, D is not a square. Any rational binary form with determinant -D is anisotropic: a nonzero isotropic vector would give a basis with matrix [[0,m],[m,b]] over Q and hence determinant -m^2.

Let N be any even lattice of signature(1,1), determinant -D, with the same finite discriminant quadratic form as N_a. We show that N has no vector of norm2n for1<=n<=B under the frozen local hypotheses. We need only an odd-prime local argument, not an assertion that all these lattices are globally isometric.

Take a prime p supplied for n. In either case v_p(D)=1 because a and a+1 are coprime. Over Z_p a rank-two integral lattice with determinant valuation1 diagonalizes as <u> perpendicular <pv>, where u,v are units. Its p-primary discriminant group has order p and its pairing on a generator is1/(pv) modulo Z_p, up to a square unit from the generator. Thus the finite discriminant form determines the squareclass of v in Z_p^*. The determinant squareclass then determines u. For odd p a unit is a square in Z_p exactly when its residue is a square, so N tensor Z_p is isometric to N_a tensor Z_p. This proves the needed local equivalence directly; it makes no use of a global class-number-one assertion.

If v_p(a)=1, reducing the norm equation for N_a modulo p and dividing by2 gives -y^2=n, impossible when (-n/p)=-1. If v_p(a+1)=1, it gives x^2=n, impossible when (n/p)=-1. Therefore every such N has mu(N)>2B and is anisotropic.

If two K3 surfaces have isometric integral polarized transcendental Hodge lattices, their Neron--Severi lattices have the same signature and discriminant quadratic form: NS and T are primitive perpendicular sublattices of the even unimodular K3 lattice, and the gluing identifies their discriminant forms with opposite signs. This operation is explicit in Huybrechts, Chapter14, Proposition0.2 and its proof. Consequently the exclusions just proved apply to EVERY K3 with the prescribed T once one such surface has N_a. The determinant alone would not give this local conclusion; the finite discriminant FORM is essential.

## 4. Centers and finite-order automorphisms at rank20

### 4.1 Classification of every surface center in the full class

Let Z be a smooth projective surface with p_g=1 and rank T(Z)=20, whose absolute discriminant is D, nonsquare and greater than1. Pass to its minimal model Z0; this preserves T. Since p_g>0, its Kodaira dimension is nonnegative and K_Z0^2>=0. Noether's formula and Hodge theory give

    b2(Z0)=22-8q(Z0)-K_Z0^2,
    rho(Z0)=2-8q(Z0)-K_Z0^2 >=1.

Hence q=0, and K^2 is either0 or1. If K^2=1, then rho=1. In the torsion-free Neron--Severi lattice the canonical class is a nonzero integer multiple m of its generator L; 1=m^2 L^2 forces m=+/-1 and L^2=1. Poincare duality makes H^2/torsion unimodular, while NS is primitive, so |disc T|=|disc NS|=1, a contradiction.

Thus K^2=0 and rho=2. If kappa=1, the elliptic fibration has a nonzero fiber class of square zero. Its primitive saturation f in NS can be completed to a basis f,e, yielding determinant -(f.e)^2; its absolute discriminant is a square, again impossible. If kappa=0, the classification of minimal complex surfaces with p_g=1,q=0 gives a K3 surface. It has rho=2. This proves the claim without discarding any isometry class of center or replacing T by a rational summand.

### 4.2 Excluding finite-order automorphisms uniformly

Let S be any K3 with rho=2, End_Hdg(T(S)_Q)=Q, |disc NS|=D>4, and no divisor of positive square2. Suppose g is a nonidentity finite-order automorphism. On T_Q, g is a rational scalar preserving the form, hence +/-id. On NS_R of signature(1,1), it fixes an ample class averaged over its finite cyclic group. The orthogonal negative line has action +/-1. Therefore g^2 acts trivially on all H^2. Faithfulness of the cohomological action of K3 automorphisms implies g^2=1.

For completeness, the invariant and anti-invariant lattices L_+,L_- of an involution in a unimodular integral lattice are primitive and have 2-elementary discriminant groups. Indeed, extend any homomorphism L_+->Z to the whole lattice (primitivity makes the quotient free), represent it by a vector z using unimodularity, and project to L_+ tensor Q. That projection is (z+gz)/2. Thus twice every vector of L_+^* lies in L_+. The same argument applies to L_-. This proves the 2-elementary assertion used below.

If g is symplectic, it acts as +id on T and fixes an ample vector in NS. Nontriviality forces its anti-invariant lattice to have rank1, negative sign, and even form. The only negative even rank-one lattice with 2-elementary discriminant is <-2>. Its generator delta is an integral (1,1)-class with delta^2=-2. Riemann--Roch implies delta or -delta is effective. But g exchanges these two classes, impossible for an automorphism preserving the effective cone (intersect with an ample divisor). Hence g cannot be symplectic.

Otherwise g acts as -id on T. Its invariant lattice is contained in NS and has rank1 or2. Rank1 is positive and even; 2-elementarity forces <2>, contrary to the hypothesis. Rank2 is the whole NS, whose 2-elementary discriminant group has at most two generators, so its order is at most4, contrary to D>4. This proves the assertion. It does not assume that NS has trivial orthogonal group or that S has no infinite-order automorphisms.

The classification of rank-two K3 automorphisms in Galluzzi--Lombardo--Peters, Sections2.6 and3, and the involution discriminant analysis in Hassett--Tschinkel, Section4, are compatible primary reductions. In particular a derived partner need not share the automorphism group of the original K3; Section3 is what makes this argument valid for every center.

## 5. The cubic and its entire K3 class

Let a satisfy the frozen arithmetic hypotheses and X have the frozen exact lattice A_a. Set d=2a. Then d>6, d=2 mod6, and d is divisible by neither4 nor9 nor an odd prime congruent to2 mod3. The span K=<H,sigma> is primitive in A(X) and in H^4(X,Z), and has discriminant d. Thus X belongs to the admissible Hassett divisor C_d.

Use the associated polarized K3 interface of SOURCE054, cubics.tex, namely Hassett's integral Hodge isometry between K^perp and the sign-reversed primitive cohomology of a degree-d K3 (S0,h). The same admissibility implies an untwisted categorical K3 by BLMPNS, Corollary29.7 (with the deformation/moduli proof in Sections32--33). These are existing operations and are not claimed as additions here.

The vector t maps to a primitive algebraic class t' in h^perp with square -2(a+1). Hence NS(S0) contains N_a=<h,t'>. Its transcendental Hodge lattice is exactly T(X) with the weight/sign adjustment, so it has rank20 and NS has rank2. Since H^4(X,Z) is unimodular and A(X) is primitive,

    |disc T(S0)| = |disc T(X)| = det A_a = 4a(a+1)=D.

The even unimodular K3 gluing gives |disc NS(S0)|=D. The contained rank-two lattice N_a also has absolute discriminant D, so the index is1. Therefore NS(S0)=N_a, with no unexamined overlattice.

Let S be the collection of ALL projective K3 surfaces with T(S)[-] integrally polarized-Hodge-isometric to T(X). Every one has rho=2, discriminant form as in Section3, End_Hdg(T_Q)=Q, and D>4. Section3 gives anisotropy and mu>2B; Section4.2 gives absence of finite-order automorphisms. Thus this entire collection satisfies the uniform test of Section2.

Assume X rational. Weak factorization of a birational map P4 --> X takes place among rationally connected smooth projective fourfolds. The source whole-block theorem matches integral complete surface blocks. Since h^{3,1}(X)=1 and T(X) is a simple transcendental Hodge structure, its final transcendental lattice is one whole block, with net multiplicity1 in its exact integral polarized Hodge-isometry class. Simplicity also follows directly from End_Hdg(T_Q)=Q. Any surface center in this class has p_g=1, rank T=20, and discriminant D; Section4.1 makes it birational to a member of S. Conversely any center counted by u is birational to such a K3 and has exactly that whole lattice. Point and curve centers are uncounted. The source blowup sign and MRC invariance therefore give

    c_u(P4 --> X)=1.

Both P4 and X are smooth Fano fourfolds of Picard rank one, hence terminal Q-factorial rationally connected Mori spaces over points. Section2 gives c_u(P4 --> X)=0 for B>=B0. This contradiction proves irrationality. The categorical assertion was already established by the admissible label and BLMPNS. There is no specialization of irrationality from a very general point of C_d in this argument.

## 6. Existence, dimension, and generic endomorphisms

The lattice A_a is integral because a=1 mod3. H has square3 and its orthogonal complement in A_a is generated by v=3sigma-H and t, with squares6a and2(a+1) and zero pairing. In particular H is a distinguished element in the sense of Yang--Yu. Its characteristic parity can also be checked directly: a is odd and1 mod3, so (2a+1)/3 is odd; x^2 congruent x.H mod2 for each basis vector.

For a vector xH+y sigma+z t, completing the square gives

    3(x+y/3)^2+(2a/3)y^2+2(a+1)z^2.

If y or z is nonzero this is greater than2 since a>3; otherwise its least nonzero value is3. Thus A_a is positive definite and has no norm2 vector. Its discriminant group needs at most rank(A_a)=3 generators, so rank+length<=6<20. Yang--Yu, Theorem5.1 and its actual primitive-embedding/gluing proof (Propositions5.3,5.9, Corollary5.5), now imply that C_(A_a,H) is nonempty, irreducible, closed algebraic, and has codimension2. Its dimension is18. This is a stronger already-paid reduction than trying to construct a new period map. The root/long-root condition also agrees with Laza's period-image theorem since H^perp has minimum greater than6.

At a very general period in the orthogonal complement of A_a, there are no further rational (2,2) vectors: their orthogonality loci are a countable set of proper hyperplane sections of the type-IV domain. Thus A(X)=A_a. Also a non-scalar rational operator on T_Q cannot preserve every Hodge structure in this domain. If it did, every period line in its open quadric would be an eigenline; an open subset of a nondegenerate quadric spanning T_C cannot be contained in the finite union of proper eigenspaces, so the operator would be scalar. There are only countably many rational operators. Their Hodge loci, after passage to a level cover, are algebraic by the standard algebraicity theorem for Hodge loci applied to End(T); each is proper by the preceding observation. This proves End_Hdg(T_Q)=Q outside a countable union of proper closed algebraic subsets. This generic-Hodge operation is classical, not a new contribution.

Distinct a have distinct determinants4a(a+1). If two of these irreducible18-dimensional loci coincided, a point very general for both would have its exact algebraic lattice isometric to both A_a, contradicting the determinants. They are therefore pairwise distinct.

## 7. Infinitely many parameters with all local obstructions

Fix B>=2. For each1<=n<=B that is not three times a square, choose a distinct prime p_n>B with

    p_n=1 mod3,    (-n/p_n)=-1.

Such primes exist. The imaginary quadratic character attached to Q(sqrt(-n)) differs from that attached to Q(sqrt(-3)) precisely because n is not three times a square. The two distinct nontrivial quadratic characters are independent as homomorphisms on the units modulo a common conductor. There is therefore a reduced residue class where the latter character is+1 and the former is-1. Dirichlet's theorem provides infinitely many primes in that class, and primes away from the conductors with the latter character+1 satisfy p=1 mod3. Choose them successively to be distinct. This treats the compatibility exception explicitly; assuming independent signs for n=3m^2 would be false.

Let P be the product of these p_n. Choose a prime q greater than B and every p_n, with q=5 mod12. Then (3/q)=-1. Choose a prime ell, also larger than all these numbers, in the simultaneous residue class

    ell=1 mod3,    P ell=q-1 mod q^2.

Since P is coprime to3q and q-1 is a unit modulo q, these congruences determine a reduced residue class modulo3q^2. Dirichlet again supplies infinitely many ell. Put a=P ell. All prime divisors of a are1 mod3, a is odd, and a>max(B,3). Each p_n divides a exactly once. Also v_q(a+1)=1. For n not three times a square the prime p_n gives condition(i). For n=3m^2<=B, q>B implies q does not divide m, so (n/q)=(3/q)=-1 and condition(ii) holds. Thus all n are excluded simultaneously, and infinitely many ell give infinitely many distinct a.

The durable finite calculations for B=2,5,10,20 verify the modular conditions for sample a and illustrate the exception. They neither prove Dirichlet's theorem nor estimate B0. The proof above completes every quantifier of FROZEN.md.

## 8. Strongest-reduction comparison and limits

The source pays the genus-zero whole-block splitting, uniform marked Sarkisov diagrams, all surface-link Galois-set identities, the intrinsic embedded-subfield correction, and the categorical/Hodge interfaces. Classical operations pay the surface classification formulas, unimodular gluing, finite-order K3 lattice theory, Dirichlet/CRT, and the existence/dimension of lattice-polarized cubic loci. In particular merely deleting End_Hdg=Q from the source's rank21 criterion is already paid by the standard Picard-one automorphism result and is not this candidate.

What this proof assembles beyond the source's stated rank21 scope is a rank20 whole-center test with nonsquare discriminant, the finite-order-only automorphism interface, and local norm exclusions that survive passage to every Neron--Severi complement of the same integral transcendental lattice. The lattice class need not be unique. The source's degree bound alone cannot be applied to a Picard-two surface by replacing its degree with the determinant; a small square in another complement would break that shortcut. Section3 supplies the simultaneous obstruction and Section7 makes it compatible with cubic admissibility. Whether these compatible operations amount to substantial contribution is deliberately left for separate review. No operation is labelled substantial merely because the final statement is stronger.

The proof retains the exact hypotheses A(X)=A_a and End_Hdg(T_Q)=Q. It does not settle all specializations of the closed loci, effective thresholds, rational points over a specified field, or uniform marking/cycle denominators. It does not reopen r58, r118, r135, or the immutable analytic/structural targets. Original primary reading limits, including the unavailable Hassett association proof and unexpanded general boundedness foundations, are in private/READING.md. Source statements and complete operative sections were read; those source operations were stipulated, not audited.

## 9. Additional compatibility calculation (after proof draft)

Every rank-two primitive labelling K' of A_a containing H has a basis H,u, since H is primitive. Write u=xH+y sigma+z t. Directly,

    det K' = 3u^2-(H.u)^2 = 2a y^2+6(a+1)z^2 >=2a.

The inequality uses (y,z)!=(0,0). Thus these exact rank-three lattices do not secretly carry an arbitrarily small additional Hassett labelling while a grows. This checks a possible compatibility failure with familiar small-discriminant constructions, without claiming to classify all rational cubic constructions. The categorical K3 S' need not equal the Hodge-associated polarized S0; the proof uses S0 only to identify the finite discriminant form, and tests every K3 with the exact whole T. No equality between those two choices of K3 is assumed.
