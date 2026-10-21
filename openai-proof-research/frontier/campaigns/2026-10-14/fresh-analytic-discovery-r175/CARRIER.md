# Ribbon substitution: prefreeze topological calculation

This is research working material, not a frozen theorem or a correctness/contribution assessment. The one source family is Source306 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its proofs, including its analytic operations, are stipulated true. The exploratory operation is replacement of the cosmetic diffeomorphism in that proof by an oriented smooth ribbon rational homology cobordism between the two order-two surgeries. No statement about all slopes follows by applying the source's cosmetic slope reduction to a cobordism.

Fix a smooth genus-two knot K in the oriented three-sphere, set Y_-=S^3_{-2}(K), Y_+=S^3_2(K), and provisionally suppose W:Y_-→Y_+ is a ribbon Q-homology cobordism. Ribbon means a relative handle decomposition with only 1- and 2-handles, with connected nonempty ends. This is an exploratory domain; it has not been frozen as a nominee. Denote by Wbar the orientation-reversed reverse cobordism Y_+→Y_-. Wbar need not be ribbon.

## 1. Integral homology and the two central lifts

The primary ribbon paper's Lemma 3.2 applies exactly: both ends have H_1=Z/2, so W is an integral homology cobordism. Here is its algebra in this instance. The relative 1/2-handle chain complex has an equal number h of generators in degrees one and two, and its boundary matrix C is rationally invertible. Thus H_2(W,Y_-)=0 and H_1(W,Y_-) is finite. Turning the handle decomposition upside down gives H_1(W,Y_+)=0. The maps H_1(Y_-)→H_1(W) and H_1(Y_+)→H_1(W) are respectively injective and surjective. Their orders force H_1(W)=Z/2 and both maps to be isomorphisms. Hence det C=±1, the remaining relative homology vanishes, and both inclusions are integral homology equivalences.

Consequently H_2(W;Z)=0, b_1(W)=b_2(W)=0, chi(W)=sigma(W)=0, while H^2(W;Z)=Z/2 by the universal coefficient theorem. This last torsion group must not be silently erased. Every reducible SU(2) representation of W factors through H_1(W)=Z/2 and is central. There are exactly two central characters, and their restrictions to either end are bijective. The adjoint local systems are trivial for both characters, so they have identical real index corrections; they remain distinct in the determinant-one configuration space.

Integral homology equivalence also implies H^2(W;F_2)→H^2(Y_+;F_2) is an isomorphism. Since an oriented three-manifold is spin and TW restricts to TY_+ plus a trivial line, w_2(W)=0. This proves W is spin; it does not choose a spin structure or identify the two boundary spin structures without further data. In particular, equal first Chern classes do not justify identifying distinct spin-c structures when there is two-torsion.

## 2. The fundamental-group issue actually closes at the filled cells

The primary proof of Proposition 2.1 gives pi_1(Y_+)→pi_1(W) onto: from Y_+ the reversed handle decomposition has only 2- and 3-handles. It does not assert the analogous surjectivity at Y_-.

Let V_+ be one of the source's simply connected handle pieces glued along its whole Y_+ boundary. Van Kampen gives

    pi_1(W ∪_{Y_+} V_+) = pi_1(W)/<<im pi_1(Y_+)>> = 1.

Adding a simply connected trace piece along the other connected seam preserves triviality. Thus replacing a negative identification cell by the two source trace halves with W between them yields a simply connected filled cell. Likewise the return cobordism underlying f_- F_Wbar f_+ is simply connected: the initial f_+ handle piece kills pi_1(Wbar) at its Y_+ end, and the final f_- piece adds no group. This is stronger than a homological calculation and corrects the provisional worry that arbitrary ribbon 1-handles necessarily destroy the source's closed cap comparison.

This argument uses both trace attachments (or the outgoing-side attachment). It does not assert that attaching a simply connected piece at Y_- alone kills pi_1(W). It supplies no relative diffeomorphism between W and a product, and no peripheral marking of W.

## 3. The integral lattice survives, without inventing embedded spheres

Cut at the actual spherical J cuts used in the source. In the modified negative cell, Mayer–Vietoris across both rational homology-sphere seams gives H_1=0, rational b_2=2 and the same two orthogonal trace classes F,F' of square -2. One can see H_1=0 explicitly from the quotient of H_1(W)=Z/2 by the image of either adjacent seam. Filling spherical boundaries by balls changes none of this. Poincare–Lefschetz duality and H_1=0 make the integral middle form free and unimodular.

The span L_0=<F,F'> has determinant 4, hence index 2 in the whole lattice. In L_0^*/L_0=(Z/2)^2, the elements F/2 and F'/2 have square -1/2 and cannot be adjoined to an integral form. The remaining nonzero coset is (F+F')/2, of square -1. Therefore

    a=(F+F')/2, b=(F-F')/2, Q(a,b)=diag(-1,-1).

This is the source's unique integral extension, now derived for the cobordism cell. It is an identification of a lattice, not a claim that a or b has an embedded sphere representative. No smooth four-manifold classification is being used.

The source's positive cell is left literally unchanged. Its basis G,U,T_1,...,T_4 has form [[2,1],[1,0]]⊕(-I_4), and its actual square-zero sphere U is the smoothing of the chain [-1,-2,-2,-2,-1]. Its neighboring -4 spheres remain in the original negative intervals. Thus the actual [-4,0,-4] plumbing, including its disjoint neighborhoods, persists inside each B H B macro. This is why the positive-cell metric construction has a geometric carrier. An isometry of the negative-cell lattice alone would not provide that carrier.

## 4. Characteristic classes and numerical telescope

On the negative cell the evaluations c_0=0 and (Lambda_0 F,Lambda_0 F')=(-2,0) give Lambda_0(a,b)=(-1,-1), a characteristic vector. The positive cell retains

    c_0=(2,1;1,0,1,0), Lambda_0=(-2,-1;0,1,0,-1).

Their difference has evaluations (-4,-2;-1,1,-1,-1), characteristic for its full integral basis. The pieces are now glued at S^3 boundaries, whose H^1 and H^2 vanish. Therefore these integral classes, with the source cap classes, glue uniquely at this stage; this does not rely on choosing a torsion class by its square. Restriction to each rational Y seam is computed after the global classes are constructed, and the even trace evaluations give a trivializable determinant there. An actual determinant connection and transition identifications must still be fixed for the gauge problem.

Changing a bit changes c and Lambda by PD(S_i), with S_i^2=-4, c_0 S_i=0 and Lambda_0 S_i=2. Hence

    c_e^2=c_0^2-4 sum e_i, Lambda_e^2=Lambda_0^2,
    c_2(e)=c_2(0)-sum e_i.

On a cell the change in Lambda square is 2(e_j-e_{j+1}); its Theta contribution is m_cell+(e_j-e_{j+1})/2, with m_cell=0 or 1. The source's outside traces cancel the endpoints. Thus b^+=m+b_0 and Theta=m+Theta_0. With n sphere tests and cap-probe degree z, the zero-dimensional ordinary count requires

    8 kappa-3(1+b^+)=n+z,
    n_D=(5m-n)/8+Theta_0-(z+3+3b_0)/8.

For n=4m+d this grows as m/8 with fixed pads. Each inserted W has chi=sigma=0 and adds no rational middle class, so there is no hidden linear loss per repetition in this calculation. This is an index calculation only; it is not a proof that the proposed count exists or is nonzero.

## 5. Scope protection

Reversing the orientation of a ribbon cobordism without reversing its handle direction preserves ribbonness. Using S^3_r(mirror K)=-S^3_{-r}(K), a proposed reverse-direction example reduces to the displayed direction for the mirror knot. This is merely a convention check, not an additional theorem.

The original-history sections i07 §5 and i97 §§1–5 explicitly separate full lattices, geometric sphere neighborhoods and relative complement comparisons. This calculation respects that separation. It does not alter those old relative filling or involution targets, infer their missing complement comparison, or claim a new solution to any old scope. The exact completed r174 exception also supplies no nonzero Witt detection principle for nonresolvable ENR homology manifolds; none is used here.
