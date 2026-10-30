# Arithmetic136 / T054L136: independent first-round correctness review

Verdict: **NEEDS_REPAIR** for the entire unchanged frozen statement and unchanged author proof. This is a completed adverse proof review, not a proof that the frozen theorem is false. No substantial-contribution, acceptance, priority, or counting determination is made.

The frozen statement has SHA256 `cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77`; the proof has SHA256 `6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446`. Line numbers below refer to that exact 192-line `notes/author-proof.md`. All operative upstream proofs at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I check new deductions and applicability, not upstream truth.

## 1. Decisive error, its location, and P1

At proof §3, line 99, the reduction at a prime dividing `a+1` has the wrong sign. The norm equation is

    a x² − (a+1)y² = n.

At an odd prime dividing `a`, it becomes `−y²=n`; at an odd prime dividing `a+1`, it becomes **`−x²=n`**, not `x²=n`. In either case the relevant nonresidue obstruction is `(-n/p)=-1`. Alternative (i) supplies that sign. Alternative (ii) supplies `(n/p)=-1`; this suffices when `p≡1 mod4`, but when `p≡3 mod4` it implies `(-n/p)=+1`. In that case the displayed modular equation has a nonzero solution. Indeed, because its derivative with respect to x is a unit, setting y=0 lifts it to a solution of the norm equation over Z_p. The erroneous local obstruction is therefore not merely inconclusive modulo p: the proposed prime is locally soluble.

The odd-prime discriminant-form transport in line 97 is sound, but transports this solubility too. It cannot repair the sign. Consequently the assertion in lines 95–101 that **every** such complement has `mu>2B` is not established. The unconditional version stated there is false; §2 below gives an exact genus counterexample. The failed conclusion is used explicitly in line 140 to apply condition (b) of §2, and hence in line 146 for `c_u=0`. The whole-block evaluation `c_u=1` does not supply the missing small-norm exclusion. Thus the universal irrationality conclusion for every allowed a and every exact-lattice X, and the corresponding “hence irrational” conclusion for very general members, have an unclosed essential premise.

**Disposition of supplied parent P1:** its sign objection is correct. For B=3, a=133, the witnesses stated in P1 do satisfy the frozen arithmetic hypotheses, and `−8²≡3 mod67` verifies local solubility at that witness. However, this particular n=3 cannot be represented by a lattice in the specified genus for a different reason. Since a≡1 mod3, a+1≡2 mod3, the form divided by 2 is `x²+y²` modulo 3. This binary unimodular form is anisotropic over F_3: if its value is 0 modulo 3 then both coordinates are divisible by 3. Iteration shows that any nonzero represented value has even 3-adic valuation. Therefore n=3m², whose 3-adic valuation is odd, is excluded over Z_3 for every m. This remains true for every complement in the genus: at 3 both lattices are unimodular of rank two with the same determinant squareclass, so they are Z_3-isometric. Equivalently use the general genus statement in Huybrechts, Chapter 14, p.280.

That 3-adic observation is a new review derivation, not a passage of the unchanged author proof. It explains why the parent's bounded n=3 illustration is not a global counterexample, but it does not dispose of P1 for the entire frozen alternative (ii). The n=2 example below makes the remaining problem concrete. No restriction to p≡1 mod4, constructed a-subfamily, or weakened theorem is substituted for the frozen scope.

The author diagnostic repeats the error: `notes/local-calculation.py`, the `possible=...` line, uses positive squares on the `a+1` side. Its samples choose q≡5 mod12, so q≡1 mod4 and the positive and negative square sets coincide. Those samples do not exercise the defective branch. I read that program without running it: its output path points into the read-only author root. Independent diagnostic code and receipts are confined to this review's private directory.

## 2. A genuine counterexample to the all-complements norm lemma

This section proves a finite mathematical example, not an asymptotic assertion or a counterexample to an unspecified B0.

Take

    B=4,
    a=18961=67·283,
    a+1=18962=2·19·499,
    a(a+1)=359538482,
    D=4a(a+1)=1438153928.

All displayed factors are prime; 67 and 283 are 1 modulo 3, and a is odd and greater than 4. For n=1,4, use p=67 in (i): `(-1/67)=(-4/67)=-1`. For n=2,3, use p=19 in (ii): `(2/19)=(3/19)=-1`. All indicated valuations are exactly one. Thus every frozen arithmetic condition for B=4 holds, including the formerly exceptional n=3. The prime 19 is 3 modulo 4.

Let

    N_a = <2a> ⊥ <-2(a+1)>,
    N'  = <4>  ⊥ <-a(a+1)>.

The latter is even, has signature (1,1), determinant −D, and contains a vector of norm 4. I now prove that it has the same finite discriminant quadratic form as N_a by proving local isometry everywhere.

At an odd prime not dividing D both are unimodular binary lattices with the same determinant; nonsingular binary forms over F_p are classified by dimension and determinant squareclass, and diagonalization/Hensel lifting gives Z_p-isometry. At the four odd primes dividing D, namely 19,67,283,499, the determinant has valuation one and every prime is 3 modulo 8. Hence `(-2/p)=+1`. The unit line of N_a is −2 modulo p: use −2(a+1) when p divides a, and 2a when p divides a+1. The unit line of N' is 4. The ratio 4/(−2)=−2 is a square modulo p and therefore a square in Z_p. Matching the unit lines and the equal determinant squareclasses matches the p-modular lines as well. This gives isometry at these primes, by precisely the valid Jordan argument of author line 97.

At p=2 there is an explicit integral change of basis. Put

    k=(3a−1)/2=28441≡1 mod8,
    s∈Z_2^*,   s²=k.

Such s exists by the square criterion for 2-adic units. In the diagonal coordinates of N_a set

    v=(2/s,1/s),
    u=s(1,0)−a v=(-(a+1)/(2s),−a/s).

Both vectors are integral over Z_2, their determinant is −1, and direct calculation gives

    v²=4,   (v,u)=0,   u²=−a(a+1).

They are a Z_2-basis identifying N_a with N'. At the real place both signatures are (1,1). Thus the lattices have the same genus and hence the same finite discriminant quadratic form. In particular **N' satisfies every premise of the lattice assertion in §3 and has mu(N')≤4≤2B**. This is an exact counterexample to that assertion, beyond a residual-set illustration.

There is also no obstruction from the requirement that complements actually occur for a fixed integral transcendental Hodge lattice. Choose an exact-lattice X with this a and End_Hdg(T_Q)=Q using the independently checked Yang–Yu/generic-period argument below. Its Hodge-associated K3 S0 has NS=N_a by the valid index calculation of author §5. Let T=T(S0). The opposite discriminant forms of T and N' glue, by Huybrechts 14.0.2, to an even unimodular lattice of signature (3,19), hence the K3 lattice. Both inclusions are primitive. Give this lattice the Hodge line already carried by T. Surjectivity of the K3 period map (Huybrechts 7.4.1) realizes it by a complex K3 S1. Since T_Q has no rational (1,1) classes, the integral (1,1) lattice is exactly N'. It contains a positive-square class, so S1 is projective. Thus S1 has the same exact integral transcendental Hodge lattice and the same End_Hdg=Q, while mu(S1)≤4. This is a failure for an actual eligible K3 complement at B=4, not merely a formal discriminant group.

The example does **not** show that such an X is rational, and does **not** show that B=4 exceeds the unknown B0. Further bounded diagnostics found a=76513 satisfying the frozen conditions through B=36 with the same kind of norm-4 genus companion; those are not used to infer an arbitrarily large sequence. The unchanged proof supplies no argument that defective cases disappear above some B0 or that the requisite minimum grows uniformly with B. Raising an unspecified threshold without such an argument does not validate it. I have not proved that no full-scope repair can exist; I have proved that the submitted unchanged argument requires one.

## 3. Valid lattice transport, anisotropy, and rank-20 surface classification

For p odd with v_p(D)=1 an integral binary form diagonalizes as `<u>⊥<pv>` with u,v units. The order-p discriminant pairing takes value 1/(pv) on a generator, up to a unit square. An isomorphism of finite quadratic forms thus fixes the unit squareclass of v; equality of determinant squareclasses fixes that of u. Square units lift from F_p to Z_p. This proves the needed local equivalence without any global isometry or class-number-one assertion. At primes where the valuation is not one the submitted argument makes no such simplified claim. The counterexample explicitly checks p=2 rather than assuming that odd-prime data suffice.

NS and T are primitive orthogonal sublattices of the even unimodular K3 lattice. The quotient by their direct sum is the graph of an anti-isometry of their finite quadratic forms. Thus exact integral isometry of T, not merely a rational Hodge equivalence or equality of determinants, transfers the whole discriminant form of NS. Huybrechts 14.0.2 proves this with isotropic gluing subgroups. The order and signature give |det NS|=D, but only the form gives the local constraints. This part of §3 is correct for ALL K3 complements, and does not remove the bad sign.

Since a²<a(a+1)<(a+1)², D=4a(a+1) is nonsquare. A binary rational form of determinant −D with a nonzero isotropic vector has a basis with matrix `[[0,m],[m,b]]` and determinant −m², impossible. Therefore anisotropy really holds in every complement, independently of the norm error.

For a smooth projective surface center with p_g=1 and rank T=20, pass to its minimal model; neither p_g nor integral T changes under point blowups. The source's surface-classification operations give kappa≥0 and K²≥0. Noether plus Euler characteristic gives

    c2=24−12q−K²=2−4q+b2,
    b2=22−8q−K²,
    rho=2−8q−K²≥1.

It follows that q=0 and K² is 0 or 1. If K²=1, rho=1 and K=mL in NS modulo torsion; `1=m²L²` forces |m|=1 and L²=1. Poincare duality on H² modulo torsion and primitivity of NS identify the orders of the discriminant groups of NS and T; thus |det T|=1, contrary to D>1. This does not require the surface's entire H² lattice to be even.

If K²=0, general type is excluded on the minimal surface (the same classification input used explicitly by Source054). Kappa=1 supplies a nonzero isotropic fiber divisor. In the rank-two NS its primitive saturation f can be completed to a basis, giving determinant `−(f·e)²`. This contradicts nonsquare D. At kappa=0 the conditions p_g=1,q=0 leave a K3, rather than an abelian, Enriques, or bielliptic surface. Hence author §4.1 correctly classifies **every** whole center of this exact T-class, including all minimal-model isometry classes. Kulikov's rank-22 argument supplies related numerical operations, not the rank-20 conclusion by itself; the new two cases above were checked directly.

## 4. Finite-order automorphisms and the actual uses downstream

Author §4.2 is correct under its stated assumptions. A finite-order g acts by ±1 on T_Q because End_Hdg(T_Q)=Q and g preserves a nondegenerate form. Averaging an ample class gives an invariant positive vector in NS_R. Its negative one-dimensional orthogonal has action ±1. Therefore g² fixes H²_Q, hence H²_Z, and faithfulness makes g²=1. Finite-order faithfulness already suffices here; Huybrechts 15.1.6 and 15.2.1 were read with their proofs.

For an involution on an integral unimodular lattice, its invariant and anti-invariant sublattices are primitive. Extend an integral functional on either sublattice to the full lattice and represent it by unimodularity. Projection is `(z±gz)/2`, so twice every dual vector belongs to the sublattice. Its discriminant group is 2-elementary. In the symplectic case nontriviality would force a rank-one negative anti-invariant lattice, necessarily `<−2>`. Its generator is an integral (1,1) class, one of whose signs is effective by K3 Riemann–Roch. Exchanging its signs cannot preserve effective classes and an ample intersection. In the non-symplectic case the invariant lattice has rank one or two inside NS. Rank one would be `<2>`, excluded. Rank two equals all of NS by primitivity and would have discriminant group of order at most 4, excluded by D>4.

In fact the no-square-2 premise survives the error independently: for n=1 alternative (ii) is impossible since `(1/p)=1`; therefore a prime in (i) exists and the valid local argument excludes norm 2 in every complement. Thus this failure does not force abandonment of the finite-order-automorphism conclusion. Infinite-order automorphisms are neither excluded nor needed.

I checked every automorphism use in the complete `surface-links.tex` and `subfields.tex`, not just their opening rank-one conventions. The replacements are valid as follows:

- `sl:small-orbits` tests fields of degree one or two over C(x,y); quadratic extensions have involutions.
- `sl:conic-h` uses the quadratic involution of L/K for a nonsplit component cover. L can have larger degree over the surface base; the automorphism is still of order two over C.
- `sl:w-def` and `sf:candidate` complement all three choices in the orientation set. This is a fixed-point-free equivariant involution. An invariant transitive orbit gives a nonidentity order-two automorphism of its field. Otherwise orbits occur in isomorphic pairs, giving the even test sum.
- Geiser and Bertini involutions act on the del Pezzo middle surface; they are not automorphisms of a test K3. The weakened K3 assertion does not interfere with them.

The broader preliminary lemma `pre:small-orbits` excludes arbitrary nonidentity automorphisms for the source's original collection. Its full generality must not be imported. All operative downstream calls above need only finite order. The author's limited replacement respects that distinction. Hassett–Tschinkel's derived-partner example warns correctly that automorphism groups are not transported by derived equivalence; the submitted proof instead uses the common T and local lattice data, which is the appropriate interface.

## 5. Uniform test extension, with its premise kept explicit

Subject to (a) anisotropy, (b) mu>2B, and (c) no nonidentity finite-order automorphism, I find the extension in author §2 follows from the stipulated source operations. This is a conditional conclusion; it does not certify that the arithmetic collection satisfies (b).

For a resolved pencil on a K3, images of distinct general fibers have no common components, so their nonzero divisor class C0 has C0²≥0, then >0 by (a). The orthogonal total-transform exceptional basis gives `C0²=Σm_i²` and adjunction gives `2g−2=Σm_i`. Nonnegative multiplicities imply `2g−2≥sqrt(C0²)>sqrt(2B)`. Stein factorization gives base P1 because q=0 and handles each normalized geometric fiber component. This replaces exactly the original use of C0=nL in `bd:pencil`.

For a bounded smooth birational model Y of S, its minimal-model morphism contracts points. If A is very ample, its pushforward D remains ample: square increases and curve intersections remain positive at each contraction. With the total-transform exceptional basis, `D²=A²+Σa_i²≤A²+(A·K_Y)²`. Assumption (b) bounds this below by 2B. Finite stratification bounds the right side independently of S. No determinant is substituted for a divisor square.

The rest of `bd:bounded-mrc` is unchanged. Free rational curves occur in finitely many bounded-degree map spaces after the noetherian open-locus argument; for a threefold with two-dimensional non-uniruled MRC base the images of general such curves are complete P1 fibers. Their Hilbert polynomials are en+1 with e bounded. Their normal bundles are O², so the fiber family lies in a two-dimensional Hilbert component birational to the base. Bounded models of those components reduce to the preceding surface inequality. This step does not use Picard rank one or bound arbitrary MRC maps.

Each of `bd:exclusions` (i)–(iv) survives separately. Bounded varieties use the preceding argument. Degree-e covers of bounded marked curves satisfy `2g−2≤e(2h−2)+(e−1)r`. Hyperplane pencils on bounded marked surfaces pull back to normalized components with uniformly bounded genera; the marked boundary bounds branch locations, not merely cover degree. A surface over an arbitrary curve uses the same geometric fiber-genus bound and Stein factorization, without a genus bound on the parameter curve. Finally a threefold with bounded uniruled geometric surface fibers cannot have a test K3 as MRC base: if the curve parameter varies on the MRC fibers, a geometric surface fiber dominates the K3 generically finitely, contradicting non-uniruledness; otherwise it descends to a pencil, whose genus is bounded by the irregularity of a bounded smooth surface model. These operations survive algebraically closed base extension; they do not assume boundedness of the total space over the curve.

The choices have the correct order. `bd:diagrams` first supplies ordinary fourfold diagrams with maps, field identifications, bad loci, and full visible ramification supports, independently of u. `bd:choice-order` fixes a rational c with 0<c<1/4 from those ordinary conic-base families. Rank one is used for the generic contraction over F=C(Q), not for a K3 test NS and not asserted after algebraic closure. With that fixed c, one uses the log threefold diagrams with lower discrepancy bound 1−c and the terminalization families extracting discrepancy≤1 places. Finally maximize the finitely many bounded surface-square and fiber-genus bounds and choose B0 with 2B0 at least this maximum. The strict inequality mu>2B and the strict pencil inequality work even at equality 2B0=C. No constant depends on a, discriminant, test collection, factorization length, or the arbitrary common resolving start. This establishes the required existential, possibly ineffective, order of constants **if (b) holds**.

## 6. Galois sets, embedded fields, and the endpoint argument

The generic surface calculation retains actual finite sets and orbit fields, with coefficient one per orbit. Over a surface common base, the rationally connected complex base is rational, so k=C(x,y). The generic surfaces have rank one (del Pezzo) or relatively rank one (conic) over k; these are ranks of the link surfaces and do not constrain test K3 Picard rank.

For degrees 5 and 6, the pencil sets have sizes 5 and 3. For the degree-6 exceptional comparison, the source first isolates the irreducible reduced rational representation of a transitive triple, then identifies its kernel and its C3 or S3 quotient action. A transitive triple action of either quotient is unique up to conjugacy, so this really gives isomorphic Galois sets; it does not rely on general Gassmann equivalence. In the (9,4) extraction case, the eight orientations are the four stars and their four complementary triangles, giving E disjoint-union E equivariantly. The other two-ray cases identify exceptional or pencil sets or invoke small orbits. Changing u as in §2 changes none of these finite sets or field identities. Lin–Shinder–Zimmermann's actual Definition 5.2/Proposition 5.5 proof was read as a companion, but the source's additional conic orientation argument, also read, is the operation being applied.

For nontrivial conic two-ray moves, the middle del Pezzo has positive degree D_W, so `r=8−D_W≤7`. Structured-isomorphism links are treated separately and require no such bound. The nonsplit component fields have quadratic involutions, giving `h_Q=−u(Delta)`. The correction is `u(Delta)+1_{r=3}u(P)/2`, a nonnegative integer under the finite-order test.

An eligible k is an embedded surface subfield of the fixed threefold field L, with L/k geometrically integral genus zero and original ramification degree≤7. Its quadratic residues and orientation covers are formed over the original fields. In `sf:residue-bound`, the two consecutive residue maps have composite zero; away from boundary intersections, a residue's secondary valuations are even, and purity gives the etale open. Deleting the bounded branch/nonfinite/intersection/bad loci gives etale covers of degrees r,2r,8. Every field factor has degree≤14. On a geometric generic diagram over a curve, the ORIGINAL supports and covers are base-changed, rather than recomputing ramification after constants kill residues. The generalized pencil bound from §5 excludes the field factors. This uses no new boundedness of an unmarked Brauer class.

The common-start boundary is the full visible ramification, with coefficient c. A genus-zero presentation has `deg(K+cD)=−2+cr<0`; its relative log program therefore ends with the same embedded base field k, not a finite extension. Comparing two such programs, a link over a surface common base preserves the embedded field. At the first departure it has common base of dimension≤1, where the bounded marked diagram would force the nonzero original candidate to be zero. If that common base is a curve, its field inclusion in k is supplied by that incoming endpoint. Thus `sf:unique` applies to ANY second eligible field, even one with zero candidate.

For an arbitrary eligible k at an ordinary conic endpoint over Q, it is essential not to assume C(Q)⊂k. The source's `sf:conic-end` starts on a common smooth model and runs the negative program first over the conic base T. On the geometric generic fiber over Q,

    K_Y*+cD_* = b*(K_T+cD_T)+E,  E exceptional and b-nef,
    E≤0,
    coeff_F(E)=a(F,T,cD_T)−1+c epsilon_F.

Thus every surviving extracted valuation has log discrepancy≤1 (≤1−c when marked). The stipulated bounded terminalization controls this surviving model and its subsequent non-extracting diagrams, rather than the arbitrary resolution. Anti-ampleness downstairs gives non-pseudoeffectivity upstairs, permitting the second negative program over Q. Compare its bounded endpoint with the output over k in the absolute log geography. Either a first departure produces a different curve/point common base Q' with the necessary inclusion in k, or the final bounded endpoint itself has surface field k and its map to Q supplies the inclusion. In both cases the candidate is zero. The author's summary retains these alternatives and the correct order; it is not an unsupported claim that arbitrary k already lies over Q.

The surface-base endpoint uses the bounded finite etale Picard-class schemes of degrees 5 and 3 and the same marked-cover exclusion. With these conditional vanishing results, define s exactly as the source. The common-base cases 0/1, 3, and 2 respectively give H_Q=0=Delta s, identified conic fields/classes, and `H_Q=Delta(w−h_Q)=Delta s`. The latter includes zero candidates. Structured isomorphisms identify all data. Consequently `c_u=Delta(v+s)` on each link, and v=s=0 on endpoints over points. This conditional argument covers the whole test collection; the specific failure is its missing arithmetic premise (b).

## 7. Cubic/K3 interface and the c_u=1 evaluation

All prime divisors of a are 1 mod3, so a≡1 mod3. With a odd, `d=2a>6` is 2 mod6 and divisible by neither 4,9, nor any odd prime 2 mod3. The span K=<H,sigma> is a primitive direct summand of the exact A(X)=A_a, and A(X) is primitive in H⁴; hence K is primitive in H⁴. Its determinant is 2a. The stipulated source interface `cub:associated` supplies an integral Hodge isometry K^perp≅h^perp with the sign/Tate adjustment for an untwisted degree-d polarized K3 S0. I do not replace this with a rational isometry. Hassett's original proof was not independently retrieved; its precise interface is stipulated and was read in `cubics.tex`.

The vector t lies primitively in K^perp and maps to a primitive algebraic class t' perpendicular to h, of square −2(a+1). There are exactly two rational algebraic classes on S0: h and t', because the rational algebraic part of K^perp is Q t under the exact-lattice assumption. Their orthogonal is the integral T(X), so rank T(S0)=20. Unimodularity and primitivity give |det T(X)|=det A_a=4a(a+1), and K3 gluing gives the same determinant for NS(S0). The contained rank-two N_a has precisely that determinant, so the index is one. No unexamined overlattice or rational-to-integral promotion remains in this argument.

BLMPNS Corollary 29.7 is an every-cubic assertion. Its proof through Proposition 33.1, Lemma 33.2, and the Section 32 deformation/moduli operations was checked. A hyperbolic-plane pairing supplies the universal family and trivial Brauer class; the target is the ordinary derived category of a smooth projective K3. This categorical K3 need not be S0. The author uses S0 to identify the NS discriminant form and subsequently tests every K3 with the fixed integral T; no equality of partners or inherited equality of automorphism groups is required.

For the irrationality implication, the source's `gw:blowup` and `gw:blocks` are stated for arbitrary connected smooth centers in rationally connected fourfolds and have no rank-21 requirement. Their proofs retain the whole integral surface block and separate scalar projector; these are stipulated operations. Rank 21 first enters `gw:k3-center`. Replacing that lemma by the directly verified rank-20 classification is legitimate. In a hypothetical rational factorization from P4, each nonzero whole block has nonzero off-diagonal Hodge part, so h^{3,1}=1 leaves one complete final block. Net additions minus removals of its exact integral polarized Hodge-isometry class is one. All and only centers counted by u have that class, by the classification and birational invariance; point and curve centers contribute zero. The source cocycle sign then gives c_u=1. The Fano/Picard-one endpoint hypotheses of the conditional vanishing argument hold for X and P4. The gap is exactly the missing mu bound when attempting the second evaluation, not the first evaluation or center matching.

## 8. Locus, genericity, determinants, and arithmetic infinitude

For any permitted a>3, the Gram matrix is integral. Since a≡1 mod6, (2a+1)/3 is odd. H has square 3, is characteristic, and its perpendicular in A_a has basis 3sigma−H,t with squares 6a and 2(a+1). Thus H is distinguished in precisely Yang–Yu Definition 4.3. Completing the square gives

    3(x+y/3)² + (2a/3)y² + 2(a+1)z².

It is positive for every nonzero vector, and exceeds 2 when y or z is nonzero; otherwise the least nonzero value is 3. The rank is 3 and discriminant length≤3, so r+ell≤6≤20. These are exactly the hypotheses of Yang–Yu Theorem 5.1. The proof's embedding via gluing to the cubic odd unimodular lattice, distinguished-vector parity, complement isometries and discriminant-form compatibility, and orientation adjustment through a hyperbolic summand were read in Propositions 5.3 and 5.9. The resulting primitive-embedding locus is nonempty, irreducible, closed algebraic **inside the smooth cubic moduli space**, and has codimension 2, hence dimension 18. Yang–Yu's definitions agree with the frozen primitive embedding carrying H to h_X². No external embedding assertion is being inferred just from a positive determinant. The minimum of H^perp is >6, excluding both roots of square 2 and long roots of square 6 in Laza's period-image condition. The embedding and root obligations are therefore met.

For the very general point, the rank-20 perpendicular has signature (18,2) in cubic convention and period domain of dimension 18. Extra rational Hodge classes impose proper rational hyperplanes. On the complementary variation, a fixed nonscalar rational operator preserving the Hodge structure must have the period line as an eigenline; the nondegenerate irreducible period quadric spans its ambient space and cannot be contained in finitely many proper eigenspaces. This proves properness. The source's CDK/finite-level-cover operation applies equally to this rank-20 variation and its endomorphism variation: integral multiples of rational tensors give algebraic Hodge loci, locally finite at fixed data; countably many such loci and their finite images give countably many proper closed algebraic exceptional subsets. Saturation of the primitive A_a gives exact A(X)=A_a outside the extra-class loci. Thus the precise algebraic meaning of “very general” and End_Hdg(T_Q)=Q is justified. These facts alone do not establish irrationality after the failed application of §3.

The determinant 4a(a+1) is strictly increasing for positive a. If two irreducible dimension-18 loci coincided, a point outside both countable exceptional unions would have its exact algebraic lattice isometric to both, contradicting their determinants. This proves pairwise distinction of the loci. The further labelling calculation in author §9 is also correct: a basis H,u with u=xH+y sigma+z t gives determinant `2a y²+6(a+1)z²≥2a`; no small additional primitive labelling is concealed. This auxiliary fact does not bound small squares in another K3 complement.

For each fixed integer B≥2, the arithmetic construction in §7 really gives infinitely many a satisfying the unchanged arithmetic conditions. If n is not 3 times a square, the two nontrivial quadratic characters for −n and −3 are distinct and hence independent over F2. Choose a reduced residue class with signs (−1,+1) for those characters. Dirichlet gives infinitely many primes p_n>B in that class, with p_n≡1 mod3; choose the finitely many p_n successively distinct. If n=3m², those characters coincide and this procedure would fail. The exception is explicitly separated, correctly.

Let P be their product, choose q≡5 mod12 larger than B and the p_n, and choose primes ell, larger again, with `ell≡1 mod3` and `P ell≡q−1 mod q²`. CRT gives a reduced class modulo 3q²: P is invertible there, and q−1 is a unit modulo q. Dirichlet yields infinitely many such ell. Then a=P ell is odd, all prime factors are 1 mod3, v_{p_n}(a)=1, and v_q(a+1)=1 because a+1≡q modq². For n=3m²≤B, q∤m and `(n/q)=(3/q)=-1`. Thus every required n has a frozen witness. Distinct ell give distinct a, with no dependence on an effective B0 and no GRH assumption. Moreover q≡1 mod4 makes the norm obstruction correct for this constructed branch. This validates infinitude, but cannot validate the universal assertion over all allowed a.

The original-history selections were checked against their exact original bytes. The i05 §3 selection explicitly discusses the −3 character exception. The r34 §5 selection actually concerns a golden-ratio/Lucas norm obstruction and the negative-of-a-square sign at primes 3 mod4; it is not a K3 theorem or a direct −3-character argument. No derivative synopsis was substituted for either body. No other history is needed for this correctness verdict, and old r58/r118/r135 scopes were not reopened.

## 9. Disposition of the full frozen quantifiers

1. **One uniform existential ineffective B0, every B≥B0:** the conditional geometric test establishes the order and uniformity of such a threshold for collections satisfying (a)–(c). The arithmetic implication supplying (b) for every allowed a is false as an unconditional lemma and unproved in the required asymptotic scope. Thus the frozen theorem's threshold conclusion is not proved.
2. **Every allowed a, every exact-lattice X with End_Hdg=Q, every K3 center sharing integral T:** the integral and classification interfaces are valid; the all-complements mu assertion fails as above, so the universal irrationality proof fails. No change to the permitted family has been made.
3. **Both arithmetic alternatives, including p≡3 mod4 in (ii):** (i) works, (ii) has the sign error. The −3 exception has the separate 3-adic disposition above and does not fix n=2.
4. **Untwisted geometric K3 category for every such X:** supported by the admissible label and the stipulated associated-K3 interface plus the actual every-cubic BLMPNS result.
5. **Nonempty irreducible closed algebraic dimension-18 locus for each allowed a:** supported by the checked Yang–Yu hypotheses and proofs.
6. **Exact lattice and End_Hdg=Q for very general members, in the algebraic exceptional-set sense:** supported. Their asserted irrationality still depends on the failed universal proof.
7. **Infinitely many parameters for every B≥2 and pairwise distinct loci:** supported by the exact Dirichlet/CRT construction and determinant/generic-lattice argument. This final existence assertion is not a claim of irrationality for B below B0.

The review is therefore NEEDS_REPAIR, not PASS. A repair must establish the needed universal large-B control under the *unchanged* hypotheses or supply a different valid argument for the unchanged conclusion. Replacing (n/p) by (−n/p), imposing p≡1 mod4, or using only the constructed q-subfamily changes the problem. No such edit, replacement theorem, or author modification was performed. The precise reading and isolation limits are recorded in `private/READING.md`; artifact identities and finite diagnostics authenticate only their stated finite objects.
