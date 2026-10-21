# Compact ENR carriers: prefreeze derivation

These are discovery calculations, not a frozen theorem or an author-proof nominee. Throughout, the pinned source and all its operative proofs are assumed true. The point is to extend the domain of its test objects while keeping its target category unchanged.

Let N be a compact finite-dimensional ENR. Realize N as a closed subset of Euclidean space with an open neighborhood O and a retraction r:O→N. A finite union P of sufficiently small closed cubes can be chosen with N⊂P⊂O. After triangulation, P is a finite compact polyhedron. Write i:N→P and r:P→N, so ri=id_N.

For any continuous f:N→X into a source test space, the following is an actual derived-sheaf retract:

    R_N → Rr_* R_P → Rr_* Ri_* R_N = R_N.

The first arrow is the unit for r and the second is the direct image of restriction to i(N). Their composite is the identity: pullback of a locally constant section along r followed by restriction along i is the original section, and the same adjunction identity holds in the derived category. Applying Rf_* gives

    Rf_* R_N  |  R(fr)_* R_P.

The right side is a permitted compact-polyhedron generator. Consequently the left side belongs to the thick category T(X), not merely to an unspecified completion or to a category on N. The construction works for every compact test target used below, including the close-pair target C_d. It requires no equivariant retraction and makes no claim that an arbitrary open restriction belongs to T.

For the following calculation take N connected, compact, oriented, without boundary, and an ENR homology d-manifold over the integers. Equivalently for the sheaf operation needed here, use its specified real Verdier orientation R_N≅D_{N,d}R_N, where D_{N,d}=[-d]D_N. Local homology concentrated in degree d identifies the dualizing complex with the orientation sheaf shifted by d; the chosen orientation trivializes it. The evaluation/cap pairing is symmetric with the source's shifted-duality convention. Proper duality therefore supplies a degree-d symmetric form on Rf_*R_N. This is not an assertion that N itself is one of the source test spaces. The target is a test space and the retract above places its pushed object in T(X).

The coefficient plane C is used as a real vector space with B(z,w)=Re(z conjugate(w)). Its form is the orthogonal sum of two positive real lines. Hence its pushed class is twice the pushed real orientation class. All direct images here have compact support. Finite cohomological dimension follows from the finite-dimensional ENR domain (and its finite polyhedron retract model), independently of any bound on the dimension of an orbit space.

## A nonzero ordinary degree test

Assume d odd and d≥3. The source's telescope S^d --2→ S^d --3→ … has type K(Q,d), with every compact homotopy having bounded height. For an orientation class η∈H^d(N;Q), represent r*η on the finite polyhedron P by a map to that telescope. Its image has bounded height. Retraction of the finite subtelescope to its last sphere and restriction to N give f:N→S^d with

    f*γ = Dη,    D a nonzero integer after normalizing η integrally.

Changing the sphere orientation if necessary makes D>0. This uses actual finite-stage representability, not a claim that N is triangulable. It says nothing yet about the coefficient of f_*[R_N] in the source's rational Witt group. Denote that coefficient by μ:

    f_*[R_N]⊗Q = μ u_d,       μ∈Q.

The equality μ=D is exactly the detection issue investigated below; it must not be inserted into the definition of μ.

## Homotopy of pushed carrier forms

If f_0,f_1:N→S^d are close enough that (f_0,f_1) lands in

    C_d={(x_0,x_1): <x_0,x_1>≥0},

their joint pushforward is a degree-d form in T(C_d). Both projections C_d→S^d are homotopic, using normalized linear interpolation; its denominator has square at least 1/2. Source homotopy invariance on test spaces makes their pushforwards equal. A finite subdivision of any compact homotopy proves equality for arbitrary homotopic f_0,f_1. This avoids assuming a separate homology theory on all ENRs or invoking nonproper covariance on N.
