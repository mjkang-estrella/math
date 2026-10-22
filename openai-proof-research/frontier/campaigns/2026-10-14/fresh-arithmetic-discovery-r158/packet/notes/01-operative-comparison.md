# Operative comparison, completed before extended deductions

This is discovery prose, not an author-proof nominee. Every operation of the two pinned Source059 manuscripts is stipulated true. The two manuscripts will be called A (September 24, multiplicities 2 and 3) and B (September 27, multiplicities 4 and 5). Authentication and exact bodies are private. Their filenames were not used to infer mathematical content.

## A: from an integer relation to an embedded equivalence

A uses multiplicity equal to the least total degree of a nonzero term. Its ambient equivalence is a homeomorphism of neighborhoods in the common complex affine space, fixing the origin and carrying one zero set to the other. Topological right equivalence means equality of the defining functions after composition with a source homeomorphism, without an arbitrary target reparametrization. These equivalences carry no differentiability or metric assertion.

The integer relation has d=3^11, indices 0<b<d/2 with 3 not dividing b, E=sum e_b>0, and products

    product ((d-b)/b)^e_b = 1,
    product (((2d+b)(2d-b))/((3d-b)(d+b)))^e_b = 1.

These are actual multiplicative relations, not numerical approximate cancellations. With D=3d, the Euclidean recursion c_next=D-floor(D/c)c produces chains beginning in weight c/D. Strict descent terminates, the terminal odd exponent exceeds two, every ordinary monomial degree is at least three, and the source gives a derivative argument for isolatedness. Adding a chain on one side and its tail on the other realizes the signed weight counts 2e_b,-2e_b,2e_b,2e_b at b/d,b/(3d),(d-b)/(3d),(d+b)/(3d). The variable excess is 4E. Balancing it with 4E squares on side 1 and adding two common cubes gives p_1,p_2 in the same even number s0 of variables, of multiplicities 2 and 3.

The source's even-character products use both integer relations; odd characters use the triple-cotangent identity, with common cubes killing the odd multiples of three. The conclusion is equality of spectra modulo two. A then uses the real Seifert classification and the integral chain monodromy-module theorem as separate operations. It does not assert that these two isomorphisms agree. The common fifth and seventh powers give q_j in s=s0+2 variables with odd monodromy order dividing 3^12*5*7 and no eigenvalue one.

For these even-variable germs, A writes T=S^{-1}S^t and B=ST^r, with 2r=1 modulo the odd monodromy order. B is symmetric unimodular, and S=BT^{-r}. Its first tensor square has equivariant isometries over every Z_l and over Q. At odd l the proof compares the forms using the self-adjoint operator P; diagonal tensor blocks use square roots and paired off-diagonal blocks use a sum-of-two-squares matrix. At l=2, odd order and absence of the eigenvalue one permit an unramified hermitian or paired-factor argument before tensoring. Rational descent includes the newly present eigenvalue-one quadratic component as well as all nonreal hermitian components. These operations are already paid.

A then really uses a second tensor square. Real coefficients produce integral reversers C with CTC^{-1}=T^{-1} and C^tBC=B. If R is the rational map and D_l the local map on the first square, the corrected second-square maps have discrepancy

    a_l tensor (C a_l C^{-1}),   a_l=R^{-1}D_l.

On a product eigenspace indexed by gamma*eta=lambda, its determinant is the product of t_gamma^{m_eta}/t_eta^{m_gamma}. The proof sums over all ordered pairs, including collisions and eigenvalue one, and obtains one. Thus the source does not rely on a general assertion that rational and integral-local isometries already patch in the full unitary group.

The six common cubes U supply eigenspaces of dimensions 22,21,21 with signatures (20,2),(6,15),(6,15), up to a simultaneous reversal. The eleventh and thirteenth powers V remove real eigenvalues. Every final hermitian factor has dimension at least 21 and is indefinite. The determinant-one centralizer is a product of restrictions of scalars of simply connected special unitary groups. Strong approximation patches the corrected maps using the stabilizers of the full Z_l lattices. The proof expressly does not replace those lattices by a falsely split integral cyclotomic direct sum.

The resulting polynomials contain four copies of q_j, U and V, and have N=4s0+16 variables, divisible by eight. Multiplicities remain 2 and 3, and Hessian ranks are 16E and zero. Separate gradients prove isolatedness; in this dimension a repeated analytic factor would force a positive-dimensional critical set, so the zero sets are reduced. Every final cyclotomic eigenvalue order has at least two prime divisors, giving det(1-T)=1. Wang/Alexander duality, Milnor connectivity and the simple-knot conditions put the links into the exact high-dimensional classification used by A. Integral Seifert congruence yields an equivalence of sphere-link pairs. Weighted radial coordinates extend that pair map over the origin to the ambient germ. Saeki/King provide the right-equivalence alternative; real coefficients remove conjugation of the function value. Corank disparity and the initial-form-fiber comparison are also source conclusions, not nominees.

The two Python objects support the relation-producing step, not the global topological theorem. The supplied finite-rank script gives a modular rank separation for a cutoff matrix. The explicit-relation verifier checks the actual integer product cancellations and reconstructs chain counts. Both were read completely and run only on authenticated own-root copies, with bounded execution. The JSON was fully parsed by the verifier, not semantically read integer by integer. Their successful runs are finite evidence for the displayed relation, not new proofs or gates.

## B: actual relative geometry and its marked lattice

B states its construction independently of A. Its use of A in the introduction/bibliography is contextual; its operative proof constructs a different four-variable example. It uses the same ordinary multiplicity and ambient zero-set equivalence, but does not supply A's topological-right-equivalence conclusion for this pair.

The plane base is h=T(X-T^2)(X-2T^2). Two degree-four finite maps, built from

    q1=(u-w-w^8)(u-w-2w^8)(u-w^2),   q2=q1-u^2,

have pullback divisors with the same six-branch contact data, but different degrees over the three base branches. B proves an integral plane Seifert isometry by a controlled branch interpolation. The degree profiles differ: (4) against (1,1,1,1), (1,1,2) against (4), and (2,2) against (4). Thus simply identifying the two plane forms does not identify their marked transfer maps.

The prepared fourfolds have yz=R_{nu,s}(p,w) and function h+w(y^a+z^b). The source fixes sufficiently large integer parameters, then a sufficiently small nonzero s; it does not prove a deformation-triviality statement as s passes through zero. Analytic elimination gives initial terms T(s^{-4}yz)(s^{-4}yz-T^2) on one side and s^{-4}yz X^2 on the other, of orders 5 and 4. The weighted boundary proof, fixed-label interface continuation and valuation contradiction establish a genuine local isolated germ and its Milnor model. These are convergent analytic charts; no algebraic-over-subfield assertion is extracted.

Let H be the base plane lattice, D_nu the pullback plane lattice, E the cone-page lattice, tau:E->Z/4 the lens marking, and pr_nu=1-(1/4)pi_nu^!pi_nu*. The actual tube lattice is

    Lambda_nu = {(pr_nu l,z): l in D_nu, z in H tensor E,
                  pi_nu* l = (1 tensor tau)z modulo 4H},

with rational form (-s_{d_nu}|K_nu) orthogonal (s_h tensor e). The inner circle collapse, the signs in Mayer-Vietoris and the Bockstein calculation determine that residue condition; it is not an optional finite-index choice. The root-vector of the full lifted lens chain is (1,1,1,1;-4), regardless of smaller braid orbits. Its marked continuation prevents a shear in the gluing. Section 8 proves the cross terms vanish, computes the exterior product pairing using full lifts and division by four, and computes the inner minus sign by two distinct balanced normal disks. The determinant of their difference is strictly negative. Incidental conical chain tips are separated from the other filling, so they introduce neither boundary nor intersection contributions.

Its arithmetic step chooses coprime n0,n1 with prescribed congruences and two classes b0,b1 carrying the same lens residue. Their normalized vectors v_j=b_j/n_j have norm -1/4. At every prime not dividing n_j they provide an integral marked splitting of Lambda_nu. The two rational comparison maps J_j therefore cover all primes. Reflection in v0-v1 compares the splittings. The discrepancy is a product of two involutions with canonically isometric minus spaces: this cancels both the spinor contribution on the eigenvalue-one factor and the determinant on the primitive-fifth-root factors. Other factors are fixed. This is stronger than merely claiming that large indefinite rank suffices.

Holomorphic differential calculations supply the indefinite real signatures. Strong approximation is then used in the determinant/spinor-trivial group and on the full glued lattice. Kato's simple-spinnable classification in S^7, with its page and collar hypotheses checked, gives the link-pair equivalence without a spherical-binding hypothesis. Local conical structure extends it to the ambient germ. A's homotopy-sphere link argument and B's tube argument are different paid mechanisms.

## Primary and original-history payment

Kirschmer's determinant-group proof supplies all norm-one unit determinants for any hermitian lattice over an unramified or split maximal quadratic order, including the dyadic case. Its exceptional smaller group is confined to a particular ramified even-rank case. Its Section 4 distinguishes special genus from genus; large indefinite rank only collapses a special genus, not all special genera. Brandhorst–Hofmann–Manthe's operative unramified/split generation argument was also read. Rapinchuk provides the group-theoretic strong-approximation conditions and explicitly separates tori from simply connected groups. Sakamoto's original join/push-off calculation supplies the product-form signs; Saeki's original links/equivalence argument supplies the precise topological interface. Full foundational proofs of every theorem those authors cite were not recursively read.

The admitted original-history projector example exhibits the failure of a rational idempotent to preserve an integral lattice. Its residue-fiber construction pays its own moment operation, not the present determinant problem. The r36 torus density section concerns its specified real torus/number-field selection and does not establish strong approximation for a norm-one adelic torus. No original topological-singularity target was found in the guarded admitted screen; that is a limited search result, not clearance of excluded history or a novelty certificate. All old targets remain immutable.
