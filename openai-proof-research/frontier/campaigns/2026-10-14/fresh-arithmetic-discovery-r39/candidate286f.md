# T286F: group-theoretical finite fusion sectors of twisted lattice factors

Complete author-side proof assembled after the exact scope freeze; not an independent gate. Let D be the full finite fusion subcategory in scope286f.md, and put M=L_mu(Gamma). Source correspondence and map-level calculus are stipulated.

Theorem (unchanged frozen scope). Let Gamma be any countably infinite ICC group abstractly commensurable with a lattice in a finite nonempty product of noncompact property(T) groups H_i(k_i)^+, where k_i is real, complex, or a finite extension of Q_p and H_i is connected adjoint absolutely simple over k_i. Primes may differ between factors. For every normalized scalar cocycle mu and every full replete unitary fusion subcategory D of bifinite L_mu(Gamma)-bimodules, D is group-theoretical. Both even categories of every finite-index finite-depth subfactor of L_mu(Gamma) are group-theoretical. There is no lattice irreducibility, cocompactness or torsion-freeness assumption, no finite-order/type assumption on mu, and no irreducibility assumption on the subfactor inclusion.

## 1. The identity sector is a finite quotient representation category
Let D0 consist of objects supported on the identity-germ orbit. Under the source equivalence these are precisely H(id,rho), with rho an ordinary finite-dimensional unitary representation of Gamma: its multiplier is mu/mu=1. Tensor, conjugation, and all maps are ordinary representation operations. Hence D0 is a full finite fusion subcategory of Rep_fd(Gamma).

Take one representative of each simple object of D0 and let V be their direct sum. The span C of all their matrix coefficients is a finite-dimensional unital *-subalgebra of the algebra of functions Gamma→C. Tensor closure makes C multiplicatively closed, dual closure makes it *-closed, and translation preserves it. Let K be the intersection of their kernels. Matrix coefficients separate Gamma/K. Distinct points of Gamma/K therefore give distinct characters of the finite-dimensional commutative C*-algebra C. There are finitely many such characters, so Q=Gamma/K is finite. The coefficient algebra is all functions on Q, since a unital self-adjoint subalgebra separating a finite set is the full function algebra (polynomial interpolation suffices). Finite-group coefficient orthogonality then shows every irreducible representation of Q occurs in D0. Thus D0=Rep(Q), with K normal and finite index. This is the classical coefficient-algebra/Tannaka argument; no new claim is attached to it.

## 2. Exact identity-sector summands
Let X=H(d,sigma) be a simple object of D, with full graph delta:A→B and fibre sigma. The multiplier of sigma is mu|A/(mu|B composed with delta). Write barX for its conjugate; its graph is delta^-1 and its fibre on B is b↦bar(sigma(delta^-1 b)).

For any ordinary representation rho in D0, first fuse X with H(id,rho). The source double-coset formula has one term (B\Gamma/Gamma), with graph delta and fibre sigma⊗(rho∘delta). Then fuse with barX. Select the double coset of the identity in B\Gamma/B. The resulting graph is id_A and fibre

    sigma ⊗ (rho∘delta) ⊗ barsigma.

The scalar q_1 in the source formula is exactly1 by normalization of mu, and the two projective multipliers cancel. Regrouping at the full identity stabilizer (the diagonal Gamma) gives the ordinary representation

    W_rho = Ind_A^Gamma (sigma ⊗ (rho∘delta) ⊗ barsigma).       (1)

Thus H(id,W_rho) is a direct summand of X⊗H(id,rho)⊗barX. Since D is full and closed under all subobjects, W_rho belongs to D0. This assertion only needs one double-coset summand; it does not assert there are no further identity-orbit contributions.

## 3. K is in every graph domain and all fibres become scalar
Take rho=1. The adjoint representation sigma⊗barsigma contains the invariant identity matrix. Inducing this line shows Ind_A^Gamma1 belongs to D0. K therefore acts trivially on Gamma/A, so K⊂core_Gamma(A)⊂A.

Also W_1 is trivial on K. Its summand indexed by the identity coset A is K-invariant because K⊂A, and K acts there as sigma(k)⊗barsigma(k). Thus Ad(sigma(k))=id on End(V_sigma), giving

    sigma(k)=c_d(k) I       for every k∈K.                     (2)

No assertion is made that sigma has finite image: c_d may take infinitely many values.

For arbitrary rho∈D0, restrict (1) to its identity-coset block and k∈K. The outer scalar factors in (2) cancel, leaving rho(delta(k))=I. Since this holds for every rho∈D0, delta(k) lies in their common kernel K. Thus delta(K)⊂K. Applying the same argument to barX gives K⊂B and delta^-1(K)⊂K, hence

    delta(K)=K.                                               (3)

This is the proposed common-kernel mechanism. K depends only on D0, not on a subsequent choice of a common subgroup for individual X. In particular no infinite intersection of finite-index subgroups is used.

## 4. Restriction splits into automorphism bimodules
Put N=L_(mu|K)(K). K is ICC because it has finite index in the ICC group Gamma. Restrict a full-germ model X to the endpoint groups K×K. There are finitely many K×K orbits in its Gamma×Gamma orbit, because [Gamma:K] is finite. For a representative translated by (g,h), its stabilizer is the graph of

    theta = Ad(h) delta Ad(g^-1): K→K.

This is an actual automorphism by normality of K in Gamma and (3). The source representative-change transport is a scalar factor times sigma(g^-1 k g), hence its restriction to that graph acts by scalars, by (2). Each line in the fibre is therefore invariant. Consequently Res_N X is a finite orthogonal sum of one-dimensional full graph models.

A one-dimensional graph model for theta:K→K with scalar fibre c has multiplier c(k)c(l)/c(kl)=mu(k,l)/mu(theta(k),theta(l)). Thus

    alpha(u_k)=c(k) u_(theta(k))

is a trace-preserving *-automorphism of N, extending by the unitary that permutes the canonical Fourier basis with these phases. Its model is the corresponding invertible N-N correspondence. This proves that every Res_N X, X∈D, is a finite direct sum of invertible N-N correspondences. The phases have been retained, not discarded by passing to untwisted representations.

## 5. The regular permutation Q-system
Let q=[Gamma:K], choose left coset representatives r∈Gamma/K including1, and retain N=L_(mu|K)(K). The source identity-germ regrouping gives

    A = _M L²(M) ⊗_N L²(M)_M
      = H(id,Ind_K^Gamma1).

The regular representation of Q=Gamma/K is in D0, so A is an object of D. Put M1=<M,e_N>, where e_N is the orthogonal projection L²(M)→L²(N). The right N-module L²(M) is free with basis (u_r), and

    M1=End_N(L²(M)_N) ≅ M_q(N),
    e_N M1 e_N=N e_N ≅N.

The matrix entries are given by u_r e_N n u_s*, n∈N. The identities e_N x e_N=E_N(x)e_N and sum_r u_r e_N u_r*=1 follow directly on this free basis. They establish the displayed matrix-algebra identification without a type-III argument.

The unitary U:A→L²(M1), U(a⊗b)=sqrt(q) a e_N b, follows from tr_(M1)(x e_N y)=q^-1 tr_M(yx). Give A the algebra and *-Frobenius structure transported from L²(M1). Multiplication L²(M1)⊗_M L²(M1)→L²(M1) is bounded because M⊂M1 has finite index; equivalently it can be calculated in the finite matrix/coset basis. Its unit is the inclusion L²(M)→L²(M1). These are M-M intertwiners, so fullness places them in D. This is the usual finite-index Q-system, not a new operation.

For clarity, the identity-germ fibre of A has orthonormal basis zeta_r=u_r⊗u_r*. Under U this becomes sqrt(q) u_r e_N u_r*. These are scalar multiples of mutually orthogonal projections. Its multiplication is

    zeta_r zeta_s = sqrt(q) delta_(r,s) zeta_r,
    1_A=q^(-1/2) sum_r zeta_r.

The diagonal Gamma action permutes them; all scalar cocycle phases cancel. Thus A is the regular function algebra Fun(Q) in D0, with the standard Hilbert normalization. In particular Hom_D(1,A) is one-dimensional, and A is separable. No assumption on the order of mu is used.

## 6. A-bimodules and the basic-construction corner
We spell out the standard finite-index Q-system interface to avoid a mismatch with primary references formulated for type-III endomorphisms. Let E be the unitary category of standard A-A-bimodule objects in D, with relative tensor product over A. Separability implies every module is a retract of a free module. Hence E is finite semisimple: it is generated under direct sums and subobjects by the finitely many free bimodules A⊗X_i⊗A, where the X_i represent the simples of D. Standard Q-system duality makes E rigid. The regular right A-module category D_A is an indecomposable D-module category (A is connected), and E is its categorical Morita dual, with the harmless opposite convention fixed by choosing right actions. These are the classical algebra/module-category constructions; compare EGNO Proposition7.11.1, Remark7.12.5, Definition7.12.17 and Proposition7.12.18.

Here this dual has a concrete operator realization. A standard left A-action on an underlying M-correspondence H is equivalent to a normal extension of the left M action to M1. Indeed its action by the generator e_N is a self-adjoint projection P satisfying

    P x P=E_N(x)P,       sum_r u_r P u_r*=1.                  (4)

These are the Q-system multiplication/unit/* identities in the finite coset presentation. Conversely (4) supplies that module action. The algebra generated by these operators is represented by the finite matrix formula

    u_r e_N n u_s* ↦ L(u_r) P L(n) L(u_s*) .                 (5)

Matrix multiplication uses Pn=nP for n∈N and P u_s* u_t P=delta_(s,t)P; the adjoint follows by taking adjoints. Normality follows from the normal N action in each of the finitely many entries. Thus this identification is not merely algebraic or a fusion-ring identification. The corresponding right module relation supplies a normal right M1 action. The commuting A-actions are exactly commuting extended M1 actions.

An M-M map is an A-A map precisely when it commutes with both new projections and hence with both M1 actions, by (5). Therefore E is fully faithfully realized as M1-M1 correspondences whose restriction to M lies in D, with the required standard module structures. Relative tensor product over A is fusion over M1: in both constructions the same finite separability projection imposes the M1 balancing relation. This also identifies units, adjoints and associativity. This is the II_1 matrix realization of the familiar Q-system bimodule equivalence; BKLR Propositions3.32–3.33 and3.38 give the endomorphism formulation and its exact map/tensor assertions, but their type-III convention is not silently substituted for this matrix check.

Now compress both sides by e=e_N:

    F(H)=e H e.

Since eM1e=N, this is an N-N correspondence. The projection is the product of the commuting left and right actions of e. The matrix units in M1 identify every M1-M1 correspondence with C^q⊗(eHe)⊗overline(C^q), with the matrix entries carrying the N actions. An N-N intertwiner T between compressed corners therefore extends uniquely to the M1-M1 intertwiner I⊗T⊗I. This proves fullness and faithfulness, and proves that every closed subobject of a compressed corner comes from a subobject in E. Contracting the middle matrix indices identifies

    (eHe)⊗_N(eH'e) ≅ e(H⊗_(M1)H')e,

unitarily with the usual normalized correspondence Hilbert norms. These finite-matrix Morita identifications preserve the tensor unit and associativity. Thus F is a fully faithful unitary tensor functor whose image is closed under all subobjects and conjugates. Equivalently this is ordinary full-corner Morita equivalence restricted to E.

Crucially, eHe is also a closed N-N subobject of Res_N H, because e commutes with N on each side. Section4 showed that Res_N H is a finite sum of invertible N-N correspondences for every underlying H∈D. Therefore F(H) has the same property. If H is simple in E, fullness implies F(H) is simple in the ambient N-N category, so it is invertible. Its inverse belongs to the image because F preserves conjugates. Consequently every simple object of E is invertible: E is pointed. Since E is categorically Morita equivalent to D, D is group-theoretical.

A pointed unitary fusion category is Vec_G^omega for a finite group G and a unitary 3-cocycle omega, by choosing representatives and unitary multiplication maps for its invertible simples and reading the associator; the pentagon is precisely the 3-cocycle identity. This is the standard pointed-category classification, not an additional new construction.

## 7. Finite-depth subfactor consequence
For a finite-index finite-depth inclusion P⊂M of II_1 factors, the M-M even category is a full unitary fusion subcategory of Bimod(M), so the preceding theorem applies. The two even categories are categorically Morita equivalent through the finite semisimple P-M correspondence category generated by the inclusion. The endpoint factors make the two tensor units simple, and the inclusion supplies a nonzero bridge, so this module category is indecomposable. This standard two-object correspondence construction (also explicitly recalled by Izumi2018, printed p474) does not require P'∩M=C. Hence the P-P even category is also group-theoretical, by transitivity of categorical Morita equivalence. This proves the subfactor consequence at the unchanged frozen scope.

## Status
The preceding is a complete author-side mathematical derivation of T286F, subject to independent proof and contribution gates. The residual claim is only the common-kernel extraction and its compatibility with all twisted germ sectors, followed by the stated classical Morita step. Pinned source exhaustion, map-level calculus, finite-group representation theory, and Q-system/Morita operations are credited and not presented as new. No acceptance or campaign count is changed.
