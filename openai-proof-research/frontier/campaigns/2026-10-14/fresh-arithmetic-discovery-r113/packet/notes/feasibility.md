# Source015 sustained continuation, PREFREEZE
One family selected. The full working question is the existing r84 direction, not a new conjecture: for EVERY sequence of orders O_i in totally real primitive sextic fields K_i, D(O_i) tending to infinity, do their complete volume-weighted invertible-ideal Picard packets, with all coordinate signs and arbitrary ordered embeddings, converge to Haar on SL_6(Z)\SL_6(R), with no escape? Includes fixed K and unbounded conductor, no rate or restricted prime/conductor/Galois hypothesis. No frozen statement or nominee.
Actual r84 local calculation and parent intake read before extended derivation: it already pays the self-dual O plus O^vee hyperbolic model, exact local Fourier index, and trace-slice cell geometry with ORDER discriminant. It explicitly leaves same-packet global unfolding/disintegration and thin trace slabs. r51 and I145/I148 class-coset/joint questions are separate and unchanged.
Notation here: M=O_K, D=Disc K, q=[M:O], Delta=D q^2, Q=q sqrt(D), kappa=Res zeta_K(1). At each p, self-dual additive measure for Tr has vol(M_p)=|D|_p^(1/2); vol(O_p)vol(O_p^vee)=1.

## Derivation in progress: exact paired unfolding
Use maximal hull ideal representatives I, local labels N_p=xi_p a_p O_p with a_p uniform M_p^units, and t in C/M^units with all signs, as in actual prime companion packets.tex. Six-dimensional sign convention is independently supplied by the sextic/quartic packet model; it does not use odd-degree W_n. Each N is invertible over O, and every Picard class occurs via this quotient. N^vee_p=xi_p^-1 a_p^-1 O_p^vee. The common label, not two independent labels, determines both vectors.
For z in K^times and integral maximal ideal b, choose local x_p generating b_p and define
 P_p(b,z)=Pr_a[x_p in a O_p AND z/x_p in a^-1 O_p^vee].
This is independent of x_p up to maximal units, and P=product_p P_p. If it is nonzero then z in O^vee. For a nonnegative pair test F and fixed z, let V_(F,z)(s) integrate F(v,sigma(z)/v) on |product v|=s with all signs and deleted logarithmic Haar. Direct Tonelli/unfolding yields
 E_mu sum_(v,y nonzero; coordinate product=sigma(z)) F(v,y)
 = (sqrt(D) kappa)^-1 sum_(b integral M-ideal) P(b,z) V_(F,z)(N b/Q).
Reason: write b=(d)I^-1, ell=z/d. The class of I is uniquely fixed; its d's form one M-unit orbit. Label averaging gives the paired P, then one common unit orbit unfolds exactly, with denominator h_M vol(C/M^units)=sqrt(D)kappa. No regulator or number-of-labels remains. No Gorenstein assumption. Unlike r51's two-copy setting there is no independent relative-unit parameter: ell is forced by d,z.

## Local disintegration being checked
For additive Haar probability on O_p times O_p^vee, let f_p(z) be density of xy with respect to self-dual dz. On z in E_p^times the map is a submersion, so density is locally constant and finite. Changing (x,y) to (x,z=xy) gives fiber dx/|N x|. Its M_p^units-coset mass is |D|_p^(1/2)c_p, c_p=product_(P|p)(1-NP^-1). Consequently
 sum_(valuation b_p) P_p(b_p,z)=f_p(z)/(|D|_p^(1/2)c_p).
Compactness of the fixed nonzero fiber intersection with O_p times O_p^vee gives finitely many accepted valuation cosets. This computes the Jacobian omitted in the r84 read, in the simpler product model, using the same classical operation as the quartic companion. It is progress in reduction, not evidence of a substantial new theorem.
Further work must retain these densities when averaging in thin real trace slices; a naive pointwise divisor bound is not justified for arbitrary orders. The quartic additive profile/Poisson/inverse-order mechanisms are compatible and will be examined before declaring a residual unpaid.
