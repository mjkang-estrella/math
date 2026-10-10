# Independent audit of i02 Hodge construction, R2

Date: 2026-10-08. **Verdict: the finite quotient calculation and the four restricted obstruction arguments survive. They do not supply the requested algebraic cylinder or a new Hodge case.** The boundary argument needs an adjunction step before it can be used as a Gysin exclusion. Arapura's numerical hypothesis can be explicitly disproved for this cover. The degree-nine deck group does not descend intact through the permutation quotient; a residual order-three action does, and gives a useful exact projector.

I read `AGENTS.md`, the pin, the relevant entries of `sources/CONTENTS.md`, the iteration README, i02, and its Mumford R2, K3 R2 and partner R3 reviews. The accepted OpenAI results at **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are premises, not objects of this audit. Reused input hashes are in [reused_inputs.json](../sources/i02_hodge_r2/reused_inputs.json); newly retrieved primary sources are in [downloads.json](../sources/i02_hodge_r2/downloads.json). No prior report, shared index, staging area or other project was modified; no agents were used.

All cohomology and cycles below have rational coefficients; varieties are over C; Q(1) has weight −2. The repaired partner B attached to an actual Mumford fourfold A is distinguished throughout from the explicit degree-nine Prym B9. The latter is **not** identified with B.

## 1. Independent finite-quotient calculation

For every t≠0,1, let X be the smooth normalization of y^9=f(x)=x(x−1)(x−t). At each finite ramification point, dx/y^k has order 8−k. At each of the three points over infinity, x^m dx/y^k has order k−4−3m. Thus the regular differential basis is

    dx/y^4, dx/y^5, dx/y^6, dx/y^7, x dx/y^7, dx/y^8, x dx/y^8.

This checks the character dimensions without importing the earlier script or its fractional-part implementation. For inverse pullback labels, d_j=dim W_j^(1,0), j=1,…,8, is

    (0,0,0,1,1,1,2,2).

The ranks d_j+d_(9−j) are two for primitive j and one for j=3,6. The genus is seven. The six-dimensional primitive Jacobian factor and this family were already described in Moonen–Oort, *The Torelli locus and special subvarieties*, Example 5.6 and Proposition 5.9 ([primary PDF](https://webspace.science.uu.nl/~oort0109/ModuliHandbook-moonenoort.pdf)).

Let N=ker[(a,b,c)↦a+4b+7c] in (Z/9)^3. It has order 81. Its annihilator is exactly

    {(j,4j,7j) mod 9 : 0≤j<9}.

The invariant field is C(x1,x2,x3,z), z=y1 y2^4 y3^7, with z^9=f1 f2^4 f3^7. This is a degree-nine extension of the rational base field: valuation one along f1=0 precludes a proper Kummer degree. Thus this equation describes the normalization of the quotient Y0=X^3/N, not just a rational map into an unspecified cover.

A cyclic permutation σ normalizes N. Let Y=Y0/⟨σ⟩. In H^3(X^3), the (2,1,0) Künneth pieces have no N-invariants: the annihilator has no vector with just one nonzero coordinate. In the (1,1,1) piece the six primitive character summands each have dimension eight; σ permutes them in two three-element orbits. A three-cycle on three odd-degree factors has sign +1. The invariant primitive part therefore has dimension 16, with h^(2,1)=h^(1,2)=8. The labels 3 and 6 contribute one dimension each in (0,3) and (3,0). Consequently

    H^1(Y)=0,     (h30,h21,h12,h03)(Y)=(1,8,8,1).

The primitive part is rational because its character set is Galois-stable. Exterior multiplication identifies it with the two coherent triples {1,4,7}, {2,5,8} in H^3(B9). Equivalently pullback by the sum of Abel maps, followed by N-averaging, leaves the three cyclic slot terms; they belong to distinct character summands and cannot cancel. Denote the resulting block on Y by UY, and the corresponding block on B9 by U9.

### Quotient versus resolution

For a finite group G acting on a smooth projective variety V, H*(V/G,Q)=H*(V,Q)^G as Hodge structures and rings. One justification uses proper base change for the finite map and the invariant subsheaf (q_*Q)^G=Q; averaging is exact in characteristic zero. This does not assert an integral-cohomology identity.

Complex finite quotient singularities are rational homology manifold singularities: their local links are finite orientation-preserving quotients of spheres, with rational sphere cohomology. Hence Y has rational Poincaré duality. For any projective resolution r:Ytilde→Y, define r_* by this duality. The projection formula and r_*[Ytilde]=[Y] give r_*r*=id. This is the precise degree-one trace argument behind the claimed injection, rather than a statement that resolution preserves all cohomology.

Rational quotient singularities also imply R^i r_*O=0 for i>0. In particular q(Ytilde)=0 and h30(Ytilde)=h03(Ytilde)=1. Exceptional contributions to h21 and h12 must still be allowed. For example, already on Y0 the stratum over x1=x2=∞ has elliptic normalization: its preimage is nine copies of X, and the stabilizer of a chosen pair of infinity points acts on the remaining X through ⟨δ^3⟩, giving X/⟨δ^3⟩=E. Generically its transverse singularity is A2, from the two opposite order-three tangent characters. Resolutions encounter ruled surfaces over E. One cannot assume the whole exceptional cohomology is Tate merely because the downstairs branch strata in (P1)^3 are rational.

### A necessary deck-action distinction

The phase δ1 does not descend to Y: it fails to normalize ⟨σ⟩ modulo N. The phase τ=δ1^3 does descend and has order three. Directly, (-a,a,0) belongs to N iff 3a=0 mod 9. On UY, τ has eigenvalues ζ3 and ζ3^2; it acts trivially on the old two-dimensional block. Thus the genuine algebraic projector on Y is

    e = 1 − (1+τ*+τ*²)/3,        e H^3(Y)=UY.

This repairs any attempted later use of a full order-nine deck action on Y. The original report itself did not make that later-use assertion.

## 2. CM-source obstruction: valid with its actual-Mumford hypothesis

For the repaired B, U(1)=H^1(A)⊗K is a sum of copies of a simple non-CM weight-one Hodge structure V. Every Hodge subquotient of H*(M) with Tate twists, for M a CM abelian variety, is of CM type. The image of a Hodge map from such a source into U is therefore both CM and a substructure of a sum of copies of V. Semisimplicity forces it to be zero. This proves the stated correspondence vanishing in every allowed degree.

The proof is independent of whether a projection onto U is algebraic. It does not prohibit a source with an additional non-CM factor, and it does not apply uniformly to all fibers of B9. At special CM fibers, the non-CM hypothesis can fail. The accepted CM paper, Lemma 8.1 and Corollary 8.2, explicitly require CM Hodge structures and a CM abelian target, respectively; inspection of the pinned statements confirms the original scope restriction.

## 3. Boundary restrictions, Gysin maps, and Arapura

### Boundary exclusion with the missing adjunction made explicit

Every boundary component upstairs is of the form point×X×X or a lower-dimensional coordinate stratum. The restriction of a three-H^1 tensor to it is zero. Finite descent and pullback to resolutions preserve this vanishing for restrictions of UY to the corresponding quotient boundary components and divisors over them.

To deduce a cylinder conclusion, use the middle Poincaré pairing. It restricts nondegenerately to UY: this is a self-adjoint summand cut out by finite-group averaging and the inverse-character-stable projector e. For j:Dtilde→Ytilde over the boundary, β∈H^1(Dtilde), and α∈UY,

    ∫Ytilde (j_*β) r*α = ∫Dtilde β j*r*α = 0.

Therefore the **orthogonal UY-projection** of j_*H^1(Dtilde)(−1) is zero. Exceptional classes mapping to zero under r_* also have zero such projection. This proves a target-component exclusion, not that every boundary Gysin class vanishes in H^3(Ytilde). In particular it must not erase possible exceptional elliptic contributions. The original report carefully called its restriction calculation a detection-map calculation; the adjunction above is the extra argument needed to strengthen it.

### The precise Arapura contract fails numerically

I checked the final arXiv v2 primary manuscript, [*Hodge theory of cyclic covers branched over a union of hyperplanes*](https://arxiv.org/pdf/1201.6403v2), Theorems 3.2 and 3.4. Theorem 3.2 uses the section's degree-d cover of P^n branched over **d** normal-crossing hyperplanes, with d prime. It is not a theorem for arbitrary branched cyclic covers or arbitrary numbers of hyperplanes.

Theorem 3.4 allows a general smooth projective base Z and SNC divisor D with O(D)=L^d, but requires both its motivic-dimension conditions and

    φ(d) h^r(Z,L^(−d+1)) ≥ dim H^r_nt(Y0).

For our degree-nine cover, use the reduced-mod-nine branch coefficients. In the three P1 directions they are respectively

    (1,1,1,6), (4,4,4,6), (7,7,7,6).

Thus L=O(1,2,3). In the notation of the paper,

    L^(−8)=L^(⊗−8) ⊗ O(floor(8D/9)) = O(−3,−2,−1).

Künneth gives h^3(L^(−8))=2·1·0=0, while dim H^3_nt(Y0)=50. Condition (b) would be **0≥50**. It fails outright, even though the base and its coordinate branch intersections are algebraic-cohomology varieties. Replacing the generator by another primitive deck generator does not repair it: every primitive character has h03=0. The subsequent C3 quotient is a further separate operation, not an application of this cyclic-cover theorem.

Thus i02's refusal to invoke Arapura is correct; “not established” can be sharpened to “false for this cover's displayed data.” No general GHC conclusion is being inferred or refuted.

## 4. Universal four-branch Hom exclusion and product domination

Let X'→P1 be a connected smooth projective cyclic cover with at most four branch points. For a nontrivial character χ, let rχ count the branch points where that character has nontrivial local inertia. The corresponding local system has no global invariants; its compactly supported Euler characteristic on the punctured sphere, or the paired Chevalley–Weil formula, gives

    dim H^1(X')χ = rχ−2 ≤ 2.

Connectedness ensures rχ≥2. The trivial eigenspace is H^1(P1)=0. If A is simple, dim A≥2, and End^0(A)=Q, its isotypic summand A^m in Jac(X') is deck-stable. On H^1(A)⊗Q^m the deck endomorphism acts only on Q^m. In characteristic zero it is diagonalizable, and every occurring eigenspace consequently has dimension at least 2 dim A≥4. Contradiction. This proves Hom(A,Jac(X'))_Q=0 universally, not merely for enumerated cyclic-cover degrees.

The conclusion persists for powers and products of these Jacobians. Adding CM factors does not introduce the non-CM A. If a smooth resolution of a divisor is dominated by a product of these curves and CM varieties, its H^1 injects into the product's H^1, after resolution of the rational map. Pullback of holomorphic one-forms is injective for a dominant characteristic-zero map, and H^1 is birationally invariant for smooth projective varieties. Hence its Gysin map has zero repaired-U component.

Counterexample checks confirm the restrictions are material. A generic elliptic double cover with four branch points has End^0=Q and maps to its own Jacobian, so dim A≥2 matters. A generic genus-two double cover has six branch points and a simple End^0=Q Jacobian, so the branch bound matters. The genus-two three-branch cover y^5=x(x−1) has a simple CM Jacobian with Q(ζ5)-multiplication and maps to itself, so End^0=Q matters. These are not counterexamples to the stated theorem.

This exclusion is about degree-one Hodge factors. It neither excludes higher tensor relationships of the BHPS curves nor identifies B9 with the repaired partner. For the repaired B itself, the standard-factor versus triple-tensor representation comparison gives Hom(A,B)=0; then Albanese functoriality proves the claimed constancy for product maps C×Z→B when Jac(C)=A.

## 5. Normal rational ample divisors

For a normal ample divisor D in the repaired abelian sixfold B, assume D has rational singularities and take j:Dtilde→B. Serre duality and Kodaira vanishing give H^i(B,O(−D))=0 for i=1,2. The divisor exact sequence and rational singularities give isomorphisms

    H^1(O_B) → H^1(O_D) → H^1(O_Dtilde).

The actual pullback j* is consequently an isomorphism on H^(0,1), its conjugate, and rational H^1. The projection formula yields

    j_*j*α = α∪[D].

Since Hom_Hdg(H^1(B),U(1))=0 for the repaired partner representation, the U-projection is zero. All stated hypotheses are used. Ein–Lazarsfeld, [*Singularities of theta divisors…*](https://arxiv.org/pdf/alg-geom/9603017v1), Theorem 1, applies to an irreducible theta divisor of a principally polarized abelian variety. It does not confer principality on the repaired polarization or rational singularities on arbitrary ample divisors.

An explicit diagnostic shows why “normal” alone would be insufficient. Let C be a nonhyperelliptic genus-three curve with simple Jacobian J, and D=C−C⊂J. Away from zero, the difference map C×C→D is one-to-one: equality p−q=p'−q' would give linearly equivalent degree-two divisors, unique unless C is hyperelliptic. Its differential is injective there because the canonical map embeds C. Thus D is smooth off zero and, being a Cartier surface divisor, is normal by R1 and S2. It is ample because J is simple. The difference map is a resolution, contracting the diagonal C; its irregularity is six, whereas q(J)=3. The preceding vanishing argument in dimension three would force equality if D had rational singularities. Hence this normal ample divisor has nonrational singularities. This is a classical-type diagnostic in dimension three, **not** an asserted sixfold support or a new target theorem.

Dropping ampleness also invalidates the H^1-isomorphism assertion: a product divisor B'×{p} in B'×E omits H^1(E). These checks support the restricted lemma, not a blanket prohibition on singular supports.

## 6. Validation and disposition

The old [check.py](../experiments/i02_hodge/check.py) was rerun to [prior_check.out](../experiments/i02_hodge_r2/prior_check.out). The independent [R2 check.py](../experiments/i02_hodge_r2/check.py) constructs the regular differential basis, enumerates actual tensor-basis orbits, checks the residual group, computes the failed Arapura inequality and the new incidence-family identities. Its output is [check.out](../experiments/i02_hodge_r2/check.out). These are exact finite validations; the universal statements use the proofs above.

The audit found no counterexample to the four obstruction arguments within their hypotheses. It found no justification for identifying B9 with B, promoting restriction vanishing to total Gysin vanishing, discarding exceptional cohomology, applying Arapura here, or replacing the required cylinder by a projector. The additional constructions and their computed zero projections are recorded separately in [i02-hodge-cylinder-r2.md](../iterations/i02-hodge-cylinder-r2.md). No substantial new theorem toward the landmark MathDB Hodge target is claimed.
