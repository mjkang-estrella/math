# Coupled symmetry extraction — active, unresolved

Parent suggested splitting q into its odd/even parts before testing curl. This is author assistance, not an independent gate. Put U_rij=T_rij-T_irj and S_rij=(T_rij+T_irj)/2, retaining only the given symmetry in the last two tensor indices. In an eigenbasis of A the exact curl is

 C_rij = (q[a_i,a_j]+q[a_r,a_j]) U_rij/2
         +(a_i-a_r)q[a_i,a_r,a_j] S_rij.          (P)

Both terms are present. Under x->-x, curl of the odd part q_o is even and curl of the even part q_e is odd. Parity gives orthogonality of the two residuals in Gaussian L2 when that norm is available, and analogous independent distributional tests. It does NOT eliminate either term in (P): the odd part's second divided difference changes sign while (a_i-a_r) does also.

A useful exact polynomial diagnostic is available. For any symmetric slices X_r, B=sum X_s^2,

 E partial_r A(G)^3=X_r B+B X_r+sum_s X_s X_r X_s.

If B=I, this is

  3X_r-(1/2)sum_s[X_s,[X_s,X_r]].                (Q)

This follows by expanding the three product derivatives and Gaussian second moments; the double-commutator identity is exact. Thus Gaussian first-chaos extraction of a nonlinear odd function already mixes the slice with double commutators. It is not scalar multiplication by E q'(G) unless extra commutativity is supplied. Equation(Q) quantifies why an unproved replacement of first-chaos symmetry by tensor symmetry is unsafe.

Possible next route: obtain a positive coupled quadratic form controlling U and commutators from odd/even tests, using B close to I and a functional-calculus analogue of(Q). Constants must actually absorb the cross terms. Merely bounding both defects by an unspecified multiple of the other is circular. No such coupled coercivity inequality has yet been proved.
