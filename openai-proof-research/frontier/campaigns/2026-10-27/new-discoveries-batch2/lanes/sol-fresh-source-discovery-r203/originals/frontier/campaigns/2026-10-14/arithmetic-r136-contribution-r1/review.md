# Arithmetic136 / T054L136: first-round contribution review, conditional on correctness

**Full-scope contribution verdict: INCOMPLETE.** This is a contribution assessment of the entire unchanged frozen statement, not a correctness verdict, acceptance decision, or count. No result for an older scope is graded here. The arithmetic alternative (ii) is retained exactly as frozen; the quantifiers include every allowed parameter, every cubic with the stated exact algebraic lattice and scalar Hodge endomorphisms, and every relevant K3 complement. The existential uniform B0, dimension-18 closed loci, and infinite-parameter conclusions are included.

The strongest compatible composition pays the geometric mechanism, rank-20 surface classification, finite-order automorphism test, discriminant transport, locus construction, and parameter construction, **provided an additional uniform all-complement small-norm exclusion is supplied**. That additional exclusion is not established for the full frozen arithmetic hypotheses. I cannot exhibit an actually closed nonroutine residual in the author proof, so SUBSTANTIAL is not justified. I also cannot give the required complete compatible derivation at the unchanged full scope, so TECHNICAL is not justified. Assuming correctness of the desired theorem does not supply the missing derivation or establish its contribution.

The obstruction is more specific than an unsuccessful literature search or a difference in Picard rank. Parent P1 identifies the sign issue in the proposed arithmetic input. Reading the relevant primary and stipulated proofs gives a partial 3-adic repair, but also gives an explicit same-discriminant-form small-vector example at a finite allowed parameter. This example tests the proposed intermediate lemma; it does not decide the frozen theorem with unknown B0.

## 1. Fixed inputs and status of dependencies

The reviewed statement has SHA256 `cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77`; the unchanged author proof has SHA256 `6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446`. The supplied author FINAL, MANIFEST, and REPORT hashes matched their exact files. Those checks identify bytes, not mathematical premises.

The operative upstream revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its proofs are stipulated true. I read the actual Source054 main and all seven operative includes: introduction, preliminaries, gw, bounds, surface-links, subfields, and cubics. I do not audit the truth of those proofs. The review checks whether their constructions and hypotheses compose in the rank-20 setting. Each copied source body was independently matched, by Git blob hashing, against the authenticated complete preprint tree. The main is the canonical 2,667-byte `build/paper.tex`, blob `5d69745bf1d4119d2f52311ace3f76022e116411`, SHA256 `8d461dfc8efafcc13f4d1432d5d3748e6cd15aa095ccc02bd12671b4b2791c62`.

The original primary files used below were independently retrieved at their pinned arXiv versions or their primary published/author-hosted URLs. All ten downloads were byte-identical to the allowed author fixtures. Their complete URLs, sizes, hashes, and the actual reading ranges are recorded privately. Primary acquisition is not a claim to have read every page or every transitive dependency. In particular, my bounded attempt to retrieve Hassett's original association proof timed out. The associated-K3 input used below is Source054's stipulated `cub:associated` interface, not a newly verified external Hassett proof. The categorical input is separately checked in the actual BLMPNS proof.

## 2. The strongest compatible all-at-once composition

Here is a precise extra interface that would suffice. Set

    N_a = <2a> perpendicular <-2(a+1)>,     D_a = 4a(a+1).

For an even hyperbolic rank-two lattice M, let mu(M) be its least positive norm. Let E(B,a) mean:

    Every even lattice M of signature (1,1) with q_M isomorphic to q_{N_a}
    has no vector of norm 2n for 1 <= n <= B.

It would also suffice to prove the corresponding exclusion for every projective K3 surface with integral transcendental Hodge lattice isometric to the one arising from the particular X; that weaker formulation must still cover *all* such complements, uniformly in every allowed X and a. Neither the existence of one favorable associated surface nor genericity in a locus is enough.

The following reconstruction is conditional on E(B,a), or on that fully quantified K3-specific substitute. It identifies what the prior operations already pay in combination, rather than charging each source separately for the entire theorem.

### 2.1 Lattices, associated K3 surfaces, and all complements

The arithmetic prime-divisor condition gives a congruent to 1 modulo 3. Since a is odd, `(2a+1)/3` is an odd integer. The lattice A_a is positive definite, H has square 3 and is characteristic, and

    det A_a = 4a(a+1) = D_a.

The rank-two primitive sublattice K=<H,sigma> has determinant 2a. Its admissibility is immediate from a being odd, prime to 3, and having no prime factor congruent to 2 modulo 3: 2a is greater than 6, congruent to 2 modulo 6, divisible by neither 4 nor 9 nor an odd prime congruent to 2 modulo 3. K is primitive in A_a and hence in the full integral Hodge lattice of a cubic with A(X)=A_a.

Apply the stipulated associated-K3 interface to this K. It gives a degree-2a polarized K3 surface (S,h), with the integral isometry between K-perpendicular and h-perpendicular, including the sign reversal. The vector t maps to a vector t' of square -2(a+1), perpendicular to h. The algebraic rank is two because the cubic transcendental rank is 20. Thus <h,t'> is N_a inside NS(S). The full transcendental lattice has determinant D_a: primitive complements in the unimodular integral middle cohomology of the cubic have the same discriminant order. The K3 lattice is also unimodular. Therefore |det NS(S)|=D_a=|det N_a|, and the index-square formula makes this inclusion index one. This pays NS(S)=N_a; no uniqueness of a rank-two genus is asserted.

For every other projective K3 S' with T(S') integrally Hodge-isometric to T(S), unimodular gluing gives q_NS(S')=-q_T(S'), hence q_NS(S')=q_Na, and NS(S') has signature (1,1). E(B,a) therefore gives mu(NS(S'))>2B for every complement. The determinant D_a is nonsquare because a(a+1) lies strictly between a^2 and (a+1)^2. A rational isotropic line in an indefinite binary lattice would make minus its determinant a rational square. Thus all these NS lattices are anisotropic over Q. Scalar End_Hdg(T_Q) transports under the same Hodge isometries.

The classical genus theorem, read in Huybrechts chapter 14, says signature and discriminant quadratic form determine the genus. At a relevant odd p with v_p(D_a)=1 this can also be seen directly: a local diagonalization has a unit line and a p-times-unit line. The p-primary discriminant form fixes the second unit square class and the determinant fixes the first. This is a local equivalence statement, sufficient to transport a genuine local norm obstruction to every M. It is not an assertion of global lattice isometry.

### 2.2 Rank-20 pg=1 centers require only classical surface operations

The whole-block argument in Source054 produces surfaces with the entire integral transcendental block, not a rank-20 sub-Hodge structure of an otherwise arbitrary surface. Thus their pg is one and their transcendental rank is exactly 20. Blow down exceptional curves; T and its discriminant do not change. The minimal surface cannot be ruled since pg=1. For a minimal surface Z of nonnegative Kodaira dimension, Noether's formula and Hodge decomposition give

    b2(Z) = 22 - 8q(Z) - K_Z^2,
    rho(Z) = 2 - 8q(Z) - K_Z^2.

Since rho>=1 and K^2>=0, q=0 and K^2 is 0 or 1. This is the same numerical calculation actually used in Kulikov's lemma, without invoking his unrelated conjectural decomposition claims.

If K^2=1, then rho=1. The canonical class has square one, so it generates the rank-one Neron-Severi lattice on the torsion-free cohomology. The latter cohomology has unimodular intersection pairing, so the transcendental discriminant has absolute value one, contradicting D_a>1. If K^2=0 and Kodaira dimension is one, the elliptic fibration supplies a nonzero isotropic divisor in the rank-two NS lattice. Its discriminant has negative square absolute value, contradicting the nonsquare D_a. The remaining pg=1, q=0, Kodaira-dimension-zero case is a K3 surface with rho=2. This classification applies to every center in the whole-block comparison; it is not a claim about generic centers.

### 2.3 Only finite-order automorphisms need be excluded

Take any such K3 with scalar End_Hdg(T_Q), anisotropic rank-two NS, and mu>2B with B>=2. For a finite-order automorphism g, averaging an ample class supplies an invariant positive vector in NS_R. Its action on this hyperbolic plane is either the identity or the reflection fixing that positive line. On T_Q it is a rational scalar preserving the pairing, hence +1 or -1. Consequently g^2 acts trivially on H^2. Faithfulness of the K3 cohomological representation (Huybrechts chapter 15, proof read) implies g is an involution if it is nontrivial.

For an involution on a unimodular lattice, its primitive plus and minus eigensublattices have 2-elementary discriminant groups. One direct proof uses the projections (z+gz)/2 and (z-gz)/2 and primitivity: twice any dual vector belongs to the corresponding eigensublattice; unimodular gluing supplies the dual-vector representatives. This elementary calculation avoids needing the full classification of 2-elementary K3 lattices.

If g is symplectic, it is identity on T, so a nontrivial anti-invariant lattice is a negative rank-one even lattice in NS. Being 2-elementary forces it to be <-2>. Riemann-Roch makes one of its roots effective; g cannot send that effective class to its negative. If g is antisymplectic, its invariant lattice lies in NS and contains the averaged ample class. In rank one it must be <2>, contradicting mu>2B. In rank two it is all NS; a rank-two 2-elementary group has order at most four, whereas D_a>4. Thus there is no nonidentity finite-order automorphism. Infinite-order automorphisms are not excluded or needed.

This is compatible with the actual GLP and Hassett–Tschinkel operations read below. It does not claim that all automorphisms of a Picard-rank-two K3 are trivial.

### 2.4 Whole blocks and the birational invariant survive the rank change

Source054 `gw:blowup` and `gw:blocks` work with integral transcendental summands of whole surface centers. The scalar Hodge endomorphism condition isolates the corresponding operator factor; the proof cancels whole saturated integral blocks. It is not a cancellation of arbitrary rational subpieces or a requirement that the block have rank 21. The rank-21 restriction in its named K3-center and net-center consequences is discharged here by 2.2 and 2.3. Because h^{3,1}(X)=1, the resulting net contribution of the block in a hypothetical rational parametrization is one.

Choose the birational surface test u to be one exactly on surfaces birational to K3 surfaces satisfying the anisotropy, large-minimum, and finite-order-automorphism conditions, and zero otherwise; extend it to threefolds through their MRC surface bases as in the source. All K3 centers with the target integral T are in this test collection by 2.1–2.3. Products and projective bundles have the same MRC base. A prime exceptional divisor with a residue field contributes once, not its degree. This preserves the blowup formula and cocycle convention used to get the nonzero net center.

The source's preliminary small-orbit statement is phrased for arbitrary automorphisms. Its actual subsequent uses require only finite ones: a quadratic extension between a test surface field and a rational surface field, a quadratic extension of surface function fields at marked covers, and the complementary-orientation involution in the three-singular-fiber conic calculation. In the marked-cover case it is the degree-two step L/K that matters; the absolute degree of L over the diagram base may be larger. A finite-order birational automorphism of a K3 surface acts on its minimal model, so the preceding exclusion applies. There is no hidden need to exclude an arbitrary infinite-order K3 automorphism at these uses.

### 2.5 Uniform boundedness and pencils are simultaneous, not separate gaps

The source's rank-one polarization degree can be replaced throughout its relevant bounds by a lower bound for positive squares in anisotropic NS. If a moving divisor C gives a pencil on a K3, then C^2>=0. It is nonzero, so anisotropy makes C^2>0, and E gives C^2>2B. Resolving its base points, write the fiber as F=pi*C-sum m_i E_i in the total-transform exceptional basis. Then

    sum m_i^2=C^2,       2g(F)-2=sum m_i >= sqrt(C^2)>sqrt(2B).

This reproduces the genus bound in `bd:pencil` without assuming Picard rank one or a specific polarization class. After Stein factorization, a K3 pencil has rational base because q=0. The operations apply to every K3 in the chosen test collection.

For a bounded smooth projective surface, push an ample divisor to its K3 minimal model. The identity used in `bd:bounded-mrc` bounds the positive square of that pushforward by A^2+(A.K)^2, uniformly in the bounded family. Large mu excludes the K3. For bounded threefolds with two-dimensional non-uniruled MRC bases, the source has already paid the stronger reduction to bounded surfaces: bounded free rational curves, finitely many relevant Hilbert schemes after noetherian stratification, and their two-dimensional components yield bounded models of the bases. It is unnecessary to invent a separate rank-20 MRC theorem.

Together with the pencil bound, these operations give the four exclusions in `bd:exclusions`: bounded varieties of dimension at most three; bounded-degree marked covers unramified away from the specified boundary; bounded geometric fibers of surfaces over curves; and bounded uniruled surface fibers of threefolds over curves. Riemann-Hurwitz controls the first curve-cover genus. In the last case, a generically finite map from a uniruled surface to a K3 is impossible; otherwise the map descends to a pencil, whose genus is bounded by the irregularity of the bounded fiber and contradicts the preceding growing lower bound. These arguments are compatible and are used together, including their specified covers and boundary strata.

The constant is uniform. Source054 first produces the ordinary bounded fourfold diagram families, independently of u, a, X, or factorization length. It chooses a rational coefficient 0<c<1/4 from all visible ramification over the dimension-at-most-one bases of those ordinary conic ends. Only then does it invoke the epsilon=1-c log threefold bounds and the discrepancy-at-most-one terminalizations. Take the maximum of the finitely many resulting square, genus, and cover thresholds, and choose B0 large enough that 2B0 and sqrt(2B0) exceed them. This is existential and does not purport to compute B0. The ordering avoids choosing bounds that depend on the very test class they are meant to exclude.

### 2.6 Surface links, marked covers, and embedded fields close the vanishing mechanism

In `surface-links`, the vertical contributions cancel in the cocycle, leaving the horizontal term minus the difference of the node correction. Bases of dimensions zero and one vanish by the combined exclusions, while dimension three is a generic-conic isomorphism case. For a surface base the actual Galois sets in the two-dimensional link calculation matter: the degree-five/six pencil sets have cardinalities five/three, and a conic with three singular fibers has eight complementary orientations. The finite involutions above make the half-weighted orientation contribution integral. The source's two-ray identities then give the correction. The bound r=8-K^2<=7 is used on the nontrivial transition to which it applies; structured isomorphisms are handled without an artificial restriction on r. The published LSZ proof supplies the corresponding actual-center/link operations; one does not replace them with mere degrees of closed points or unproved permutation-set cancellations.

In `subfields`, an eligible k is an embedded surface field k subset L, with L a geometrically integral genus-zero curve field over k. Its correction is u of the discriminant, plus half u of the orientation cover when r=3. The source retains the original covers and supports before extending constants. The residue relation and purity bound their branch supports; the cover degrees needed are at most fourteen. Its first-departure argument makes candidates independent of the eligible embedded field: distinct candidates meet a common lower-dimensional base, where the previously obtained exclusions apply, including candidates whose correction is zero. If that base is a curve, the required inclusion of its function field arises at the departure; it need not hold for the original arbitrary eligible k.

At conic ends, one cannot simply assume k contains the designated base field. The actual proof runs the relative MMP first over the surface model and then over the original low-dimensional base. Only discrepancy-at-most-one extractions survive; the bounded terminalization has already been obtained. Either a first departure gives the lower-base exclusion or the final bounded endpoint does. Thus the node correction is intrinsic and the cocycle is a difference of the total vertical-plus-node correction. At the point endpoints both corrections vanish. The same cocycle that the whole-block argument made nonzero must therefore vanish.

This contradiction proves irrationality for **every** exact-A cubic with scalar End, conditional on the all-complement exclusion. Nothing in 2.1–2.6 specializes X to a very general cubic or chooses just one K3 complement. The strongest source composition already contains the marked-cover, bounded-MRC, surface-link, and embedded-subfield operations required after the finite-order-only restriction. Naming those interfaces separately is not evidence of a new unclosed geometric operation.

## 3. Locus and categorical conclusions are paid separately at their full scope

Yang–Yu's actual Theorem 5.1 and its embedding, gluing, and orbit proofs (Propositions 5.3, 5.8, 5.9 and the assembly) apply to A_a. The rank plus the length of its discriminant group is at most six, hence at most twenty. The distinguished square-three vector is characteristic. For a vector xH+y sigma+zt,

    norm = 3(x+y/3)^2 + (2a/3)y^2 + 2(a+1)z^2.

A nonzero vector has norm at least three: if z is nonzero its last term exceeds three; if y is nonzero its second term exceeds three since the allowed a is greater than three and congruent to one modulo three; if both vanish its norm is 3x^2. There is no norm-two vector. Also H-perpendicular inside A has basis 3sigma-H,t with squares 6a,2(a+1). These verify the relevant cubic-lattice exclusions. The primary theorem gives the full primitive-embedding locus as a nonempty irreducible closed algebraic subvariety of codimension rank(A)-1=2, hence dimension eighteen. Its gluing/orbit proof is why the locus is irreducible, not merely why one period component exists.

Outside the countable additional integral Hodge hyperplanes, A(X) is exactly A_a. For each nonscalar rational endomorphism of the residual rational lattice, its Hodge-preserving periods are confined to proper eigenspace conditions on the period quadric; they cannot contain an open subset of that quadric. Countably many rational endomorphisms, together with algebraicity of Hodge loci, give End_Hdg(T_Q)=Q very generally. This is the source's standard generic-endomorphism operation in the residual rank twenty. Thus, with the conditional irrationality interface in Section 2, the entire very-general conclusion follows; no claim is made for every member of the closed locus.

The categorical K3 conclusion is not inferred by confusing a Hodge-associated K3 with a Fourier–Mukai partner. BLMPNS Corollary 29.7 states the untwisted geometric criterion for every cubic on the admissible divisors, and Sections 32–33 prove the requisite deformation/moduli and untwisting operations. The label 2a meets this criterion. Hence every X in the exact-A assertion has the untwisted category, independently of E(B,a). The proof does not require that the categorical K3 be the particular associated S used to identify N_a. The original Hassett association retrieval failure remains disclosed; it is covered only by the stipulated Source054 association interface.

For distinct a the determinants D_a differ strictly. If two irreducible codimension-two loci were equal, a very general point of the common locus would have both of the exact, different-determinant algebraic lattices, impossible. Hence the entire dimension-eighteen loci, not just selected points, are pairwise distinct.

## 4. Infinite parameters and actual project overlaps

For any fixed B>=2, and each n<=B that is not 3 times a square, the quadratic character of -n is distinct from that of -3. On a common cyclotomic modulus there is consequently a unit residue class with (-3/p)=+1 and (-n/p)=-1. Dirichlet supplies an odd prime p_n congruent to one modulo three in that class. Choose all these primes distinct and larger than B. Let P be their product. Choose a further prime q>B with q congruent to 5 modulo 12, avoiding P. Then (3/q)=-1 and q congruent to one modulo four.

By CRT choose primes ell congruent to one modulo three and satisfying P ell=q-1 modulo q^2. The residue modulo 3q^2 is a unit, so Dirichlet gives infinitely many such ell; omit the finitely many dividing P. Put a=P ell, taking ell large enough. All its prime divisors are one modulo three; each p_n divides a exactly once. Also a+1 is q modulo q^2. Thus (i) holds at p_n for all the selected n, while for n=3m^2<=B, (n/q)=(3/q)=-1 and (ii) holds at q. This proves the entire frozen infinite-parameter existence statement, for every B>=2, with distinct a. No GRH, density theorem, or uniform effectivity is used.

These parameters in fact have witnesses of the stronger, sign-corrected kind because q is one modulo four. That verifies the construction's own obstruction route; it does **not** justify replacing the frozen set of allowed parameters by this subfamily.

The two actual original project sections supplied as navigation were read directly and matched to their recorded identities. The section of `i05-joint-artin.md` already analyzes quadratic-character compatibility and the exceptional -3 character. The section of the original Arithmetic34 reduction obstruction already uses the negative-square/nonresidue mechanism and its dependence on primes modulo four. They pay the elementary character/CRT ingredients and prevent presenting the -3 split as new to this project. They do not themselves prove the present K3 theorem. I make no grade, count, or revised disposition for either older scope. The old Chow scopes were not opened: the frozen target makes no Chow assertion, and no claim of novelty clearance is based on ignoring or summarizing them.

Likewise the actual Lin–Shinder unboundedness construction does not alone answer this target. Its proof, including the dimension-four elliptic-surface cases, was read. An elliptic pg=1 rank-20 center has an isotropic fiber and is ruled out here by the nonsquare discriminant as above. Combining that paper's center invariants with the stronger Source054 operations yields the composition in Section 2, not an independent unproved assertion that every unbounded family is the desired K3 family.

## 5. P1, a partial repair, and a stronger finite diagnostic

P1 is an open supplied mathematical objection, not an independent review result. The correct norm equation in N_a is

    a x^2 - (a+1)y^2 = n.

At an odd p dividing a, this becomes -y^2=n, so (i) is a valid obstruction. At an odd p dividing a+1 it becomes -x^2=n. The needed symbol is therefore (-n/p)=-1. The frozen (ii) gives this when p is one modulo four; when p is three modulo four it gives (-n/p)=+1 instead. The valuation-one assumption pays local genus transport but cannot reverse this sign. This is why a proof of a bound for one diagonal lattice, even if repaired there, still has to be transported to every complement using a genuine local obstruction.

There is an additional compatible local operation that must not be omitted. Since a is one modulo three, the half-norm over Z_3 reduces to x^2+y^2. This is anisotropic over F_3. Dividing out the minimum 3-adic valuation of x,y shows that every nonzero represented n has even v_3(n). Thus every n with odd v_3(n), including all 3m^2, is already excluded at three in N_a, and by genus equivalence in every M with the same discriminant form. In particular P1's illustration at a=133,n=3 tests the sign mistake at 67 but does not demonstrate failure of the full local obstruction after combination with the prime three.

That partial repair is not enough. Here is an exact finite example testing the proposed all-lattice conclusion, not merely a search for residues. Take B=20 and a=469=7*67, with a+1=470=2*5*47. All prime divisors of a are one modulo three, and a>20. The following witnesses verify the *unchanged* arithmetic hypotheses for every n from 1 through 20 (each indicated valuation is one):

| n | witness | n | witness |
|---:|:---|---:|:---|
|1|7 (i)|11|7 (i)|
|2|7 (i)|12|5 (ii)|
|3|5 (ii)|13|5 (ii)|
|4|7 (i)|14|67 (i)|
|5|47 (ii)|15|7 (i)|
|6|67 (i)|16|7 (i)|
|7|5 (ii)|17|67 (i)|
|8|7 (i)|18|7 (i)|
|9|7 (i)|19|67 (i)|
|10|67 (i)|20|47 (ii)|

Let

    N=<938> perpendicular <-940>,
    M=<10> perpendicular <-88172>.

Both are even of signature (1,1), and both have determinant -881720=-8*5*7*47*67. M has a vector of norm 10, so mu(M)<=10<40. The following is a complete discriminant-quadratic-form certificate, not an inference from equal determinants. Values are in Q/2Z. At the odd primes use the indicated generators of the order-p groups and send the N generator to s times the M generator:

| p | q_N(generator) | q_M(generator) | s |
|---:|---:|---:|---:|
|5|-188/5|2/5|1|
|7|134/7|-12596/7|3|
|47|-20/47|-1876/47|18|
|67|14/67|-1316/67|14|

In each row s is a unit and the numerator difference `u_N-s^2 u_M` is divisible by 2p. On the 2-primary group Z/2 plus Z/4, the diagonal values for N are 469/2 and -235/4; those for M are 5/2 and -22043/4. Their differences are 232 and 5452, respectively, both in 2Z, so the identity on those generators works. Primary summands for different primes are orthogonal. These maps exhaust the discriminant groups and prove q_N=q_M. The genus theorem then also makes M and N locally isometric at every prime. At n=5 the frozen witness is the prime 47, which is three modulo four; the 3-adic repair does not apply.

This diagnostic is relevant to actual complements, not just an arbitrary nonrealizable discriminant form. Given any associated K3 S0 with NS=N and T=T(S0), glue M and T along the anti-isometry q_M=-q_T. The resulting even unimodular lattice has signature (3,19), hence is the K3 lattice; both summands are primitive. Put the same period line from T into it. The classical surjectivity of the K3 period map gives a marked K3 S. Since T_Q has no nonzero rational (1,1) vector, its NS is precisely M; primitivity removes any possible saturation index. The positive-square vector in M makes S projective. Its integral transcendental Hodge lattice is T. This is the ordinary discriminant gluing plus period operation, with the book's period-surjectivity proof and projectivity criterion explicitly consulted, not a claim to have re-proved the full global Torelli theorem. If T of S0 has scalar endomorphisms, the new S has that property too.

The certificate disproves the author's auxiliary assertion E(20,469) as stated in Section 3, including its intended all-complement consequence. It does not prove that N itself globally represents 10, that any cubic is rational, or that the frozen theorem is false. Most importantly, a finite B=20 example cannot refute a theorem whose B0 is unspecified. I do not infer arbitrarily large such examples from a bounded search. Nor do I infer that every possible test-class argument must demand exactly mu>2B: another proof might use a different uniformly growing bound or a different invariant. No such full-scope substitute was established here or found closed in the unchanged author proof.

## 6. Contribution conclusion at the full quantifiers

The new-to-project statement is a rank-three cubic-lattice / rank-twenty transcendental specialization with explicit arithmetic parameters and eighteen-dimensional loci. That description is not a demonstrated new-to-literature theorem. Source054's final rank-21 theorem cannot simply be cited with its rank changed, but its *operative proofs*, combined with the classical rank-20 classification, finite-involution argument, genus transport, Yang–Yu construction, BLMPNS criterion, and elementary CRT argument, already provide the full mechanism once the uniform small-norm interface is true. Page count, complicated notation, and having to read several sources do not supply a residual contribution.

A full TECHNICAL payment would have to finish the missing interface for every parameter allowed by both unchanged alternatives, with one threshold B0 independent of a and X and with every relevant K3 complement included, or exhibit a different complete proof dispensing with that interface. Proving it just for the CRT subfamily, replacing (ii) by (-n/p)=-1, adding p congruent to one modulo four, or relying on a generic member does not meet that requirement. The conditional reconstruction here explicitly exposes this condition; it is not asserted to be an unconditional derivation of T054L136.

A SUBSTANTIAL assessment would have to identify an operation not already paid by the combined sources, explain why those compositions fail to supply it, and point to where the author actually closes it. The remaining full-arithmetic step is not presently such a closed operation. The unchanged Section 3 calculation does not close it; Section 7 verifies a stronger subfamily. I cannot turn an unresolved verification into evidence of mathematical novelty. The strongest justified full-scope contribution verdict is therefore **INCOMPLETE**, conditional on correctness, leaving correctness itself to the separate review.

No exhaustiveness, priority, acceptance, or counting claim is made. Literature-search limits cannot prove novelty.
