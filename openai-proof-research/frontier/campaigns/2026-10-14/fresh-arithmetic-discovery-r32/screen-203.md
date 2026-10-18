# Family203: gradings, actions and the missing rigidity hypothesis

Closed pre-freeze screen; no nominee or count. No Puig, Broué, or arbitrary equivariant finiteness conjecture was frozen. The calculation below is a classical representation-theoretic route exclusion, not a proposed substantial result.

## Actual source operation and history

Both family203 introductions were read in full. The field paper already treats all algebraically closed characteristic-p fields and explicitly includes bounds for Cartan entries, basic Loewy lengths and fixed-degree Ext dimensions. The integral companion already treats each fixed complete mixed-characteristic DVR with algebraically closed residue field. Ordinary descent and those numerical consequences are paid.

The complete integral companion Section3 was read. Its lem:orbit assumes surjectivity of an integral orbit derivative. Its thm:gradings proves finiteness, even under inner conjugacy, of H-labelled gradings on a fixed total order A with HH¹_O(A)=0, for every finite H. Cancellation of group degrees turns the off-diagonal tangent to a grading into an algebra derivation. It does not average over H. Proposition prop:marked then retains identity markings using finite outer automorphism groups. The fixed-total-order hypothesis is essential and the source itself gives varying-total-order counterexamples.

I104 had already read and used these exact integral rigidity/comparison operations in its modular/Galois screen. Its G104 target, B104 splendid Broué screen, and later I110 twisted-moment route are not reopened here. The present question during source inspection was whether arbitrary finite-group actions could replace gradings using the same HH¹ argument. They cannot. Here is an explicit reason.

## Explicit integral action family

Let k be an algebraic closure of F_2, O=W(k), K=Frac(O), P=C_2×C_2 with named generators s,t, and A=M_4(O). For each lambda in k choose a lift a in O. Define

    S = [ 1  0  0  0 ]       T_a = [ 1  0  0  0 ]
        [ 0 -1  0  0 ]             [ 0  1  0  0 ]
        [ 0  1  1  0 ]             [-1 -1 -1  0 ]
        [-1  0  0 -1 ]             [-1 -a  0 -1 ].

Direct multiplication gives S²=T_a²=I and ST_a=T_aS over Z[a]. Thus rho_a(s)=S, rho_a(t)=T_a defines an integral representation, and conjugation defines an O-linear action alpha_a of P on A. Every such action is inner; HH¹_O(A)=0 because matrix algebra is Morita equivalent to O (equivalently, its O-linear derivations are inner).

The labelled actions alpha_a and alpha_b are conjugate by an O-algebra automorphism only if their residues lambda and mu are equal.

Proof. Every O-algebra automorphism of M_4(O) is conjugation by some U in GL_4(O). For completeness, twist the standard module by that automorphism. Under matrix Morita equivalence it corresponds to an O-module of rank one; over the local ring O this is free. An intertwining isomorphism with the standard module supplies U. If U intertwines alpha_a and alpha_b, then

    U S U^(-1)=c_s S,   U T_a U^(-1)=c_t T_b

for central units c_s,c_t. Squaring gives c_s²=c_t²=1. Since O is a characteristic-zero domain these scalars are ±1, and both reduce to 1 in k. Consequently bar(U) intertwines the two pairs of reduced representation matrices.

Write k^4=k²⊕k². Their nilpotent parts are

    N_s = [0 0; B 0],   N_t = [0 0; C_lambda 0],
    B = [0 1;1 0],      C_lambda = [1 1;1 lambda].

The space W=ker(N_s)=im(N_s) is the second k². Both N_s and N_t induce maps k^4/W→W, and the first is invertible. Hence the conjugacy class of

    J_lambda = (N_s)^(-1) N_t = B^(-1)C_lambda
             = [1 lambda;1 1]

on k^4/W is intrinsic to the labelled pair. Its determinant is 1+lambda. Intertwining therefore implies lambda=mu. Since k is infinite, there are infinitely many conjugacy classes of these actions on the one order A.

This argument needs no classification of all lattices and makes no claim that different lifts with the same residue give distinct classes.

## Exact failure of lattice rigidity

Let L_a=O^4 with this P-action. Rationally it is the direct sum of all four distinct characters of P. One can see this by writing it, in the simultaneous character space K^4, in the basis

    v1=(1,0,1,1), v2=(0,1,1,a), v3=(0,0,2,0), v4=(0,0,0,2),

where s acts diagonally as (1,-1,1,-1) and t as (1,1,-1,-1). The basis determinant is 4. This produces exactly S and T_a above. Thus End_OP(L_a) is a free O-module of rank four.

In the reduction, an endomorphism commuting with N_s must have block form

    [D 0; E BDB^(-1)].

Commuting also with N_t says that D commutes with J_lambda; E is arbitrary. The nonscalar two-by-two matrix J_lambda has two-dimensional centralizer, for all lambda. Hence dim_k End_kP(L_a/2L_a)=2+4=6. Reduction of End_OP(L_a) has dimension four: its kernel is exactly twice that endomorphism module, since division by 2 preserves the commutation equations. Applying Hom_OP(L_a,-) to multiplication by 2 gives

    dim_k Ext¹_OP(L_a,L_a)[2] = 6-4 = 2.

Every lattice in this family is therefore nonrigid. Vanishing HH¹ of the unrelated total matrix order does not remove this obstruction. This identifies the missing hypothesis more precisely than merely saying that an action-variety argument has not been proved.

## Why no equivariant Morita or crossed-product counterexample follows

The genuine representation rho_a makes L_a an equivariant Morita bimodule between (End_O(L_a),alpha_a) and O with trivial P-action. Thus all these actions are equivariantly Morita equivalent. Their skew group orders are all isomorphic to M_4(OP), via

    A⋊P → A⊗OP,   x u_g ↦ x rho_a(g)⊗g.

Even the based crossed types collapse by exterior equivalence. The units v_g=rho_a(g)rho_b(g)^(-1) satisfy alpha_a(g)=Ad(v_g)alpha_b(g) and v_g alpha_b(g)(v_h)=v_(gh). Thus the infinite strict-conjugacy family does not contradict the source's finite based graded types. In particular it supplies no counterexample to Donovan, Puig, or the source theorem.

For an actual new finiteness theorem one would need an additional condition forcing rigidity of the marked representation, or an operation preserving the relevant permutation/source structure. The source HH¹ and grading argument alone do not supply that. No such additional construction emerged in this round.

## Primary credit

Eisele's published paper, On the geometry of lattices and finiteness of Picard groups (2022), Introduction/Theorems A–B, distinguishes Ext¹-rigidity of lattices from HH¹-vanishing of orders. Its finite-lattice result requires the former; its Picard consequence uses the latter. The reduction-endomorphism test used above is explicitly explained there. URL: https://openaccess.city.ac.uk/id/eprint/27364/1/10.1515_crelle-2021-0064.pdf .

Drozd, Representations and cohomologies of Kleinian 4-rings (2022), Section1/Theorem1.2, describes the four-subspace quiver and reconstruction of lattices by taking inverse images of residue subspaces in four character components. The displayed v_i construction is an elementary instance of that established operation. Drozd credits earlier Klein-four representation work of Nazarova and related order theory. Those older bodies were not read here. URL: https://archive.mpim-bonn.mpg.de/4765/1/mpim-preprint_2022-30.pdf .

Neither a new classification nor global novelty is claimed. This packet records a failed pre-freeze promotion of an already-paid operation. Original exposition: Myeongjin Kang, no affiliation, CC BY4.0; private third-party inputs excluded from Git and release.
