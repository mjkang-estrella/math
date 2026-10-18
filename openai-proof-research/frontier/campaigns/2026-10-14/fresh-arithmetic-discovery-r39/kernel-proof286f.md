# T286F common-kernel proof work

Author-side derivation after the scope freeze; not an independent gate. All objects below are in the full finite fusion subcategory D from scope286f.md. Put M=L_mu(Gamma). Source correspondence and map-level calculus are stipulated.

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

## 5. Remaining categorical assembly at this work checkpoint
The regular permutation object A=L²(M)⊗_N L²(M) is H(id,Ind_K^Gamma1), so lies in D0. Its algebra is the canonical finite-index Q-system, equivalently L²(M1) for the basic construction M1=<M,e_N>. Since K is normal and Q=Gamma/K is finite, this is the regular function algebra of Q under the identity-sector equivalence, with the usual harmless normalization of multiplication.

A direct corner realization should finish: A-bimodule objects in D extend to M1-M1 correspondences; compression by e_N on both sides yields a fully faithful monoidal functor into N-N correspondences. Since the underlying M-M object is in D, the compressed object is a subobject of its N-N restriction, hence a sum of invertible correspondences. Fullness identifies simple objects with ambient simple objects; the dual category is therefore pointed. The exact extension/compression functor and its fullness are to be written explicitly in the candidate, using standard finite-index Q-system Morita theory with attribution. This checkpoint does not yet assert that the whole frozen theorem has passed proof review.
