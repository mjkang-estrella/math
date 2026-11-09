# A global conditional curl test without point evaluation

Author supporting derivation. The FULL symmetry premise below is NOT supplied for source101's first-chaos coefficients. It must not be silently added to the entropy target.

Let T be a fully symmetric real cubic tensor on R^m, X_r its symmetric matrix slices, A(x)=sum x_rX_r, and B=sum X_r^2<=2I. Suppose a symmetric weak Jacobian J=DF (equivalently locally a weak Hessian) satisfies ||q(A)-J||_(L2(gamma;F))<=epsilon. Then there is an absolute finite C such that

    sum_(r,i)||[X_r,X_i]||_F^2 <= C epsilon^2.       (S)

Here q(a)=phi(a)/Phi(-a), as in the source. This is a conditional analytic estimate, not entropy stability or a nomination.

Put K=q(A), and define

    Phi_rij=sum_a(A_ia T_raj-A_ra T_iaj).

Full symmetry shows that Phi is antisymmetric in r,i and is a linear Gaussian tensor with coefficients equal, up to the harmless commutator sign convention, to [X_r,X_i]. Thus if C0^2=E||Phi||^2 then C0^2=sum_(r,i)||[X_r,X_i]||_F^2.

At each x diagonalize A, rotating ALL three tensor indices. The derivative formula for matrix functions gives

    (partial_r K_ij-partial_i K_rj)
       =(q[a_i,a_j]-q[a_r,a_j]) T_rij
       =q[a_i,a_r,a_j] Phi_rij.                    (1)

No eigenvectors are differentiated. Repeated eigenvalues are interpreted by continuous divided differences. q'' is strictly positive: the source survival-function proof is strict because the hazard q is strictly increasing, so Var(X_a)<(E X_a)^2 and q''=q(d^2+qd-1)>0. Hence q's second divided difference has positive minimum c_R on triples in [-R,R], and is nonnegative everywhere.

We require a Gaussian matrix estimate. If A=sum x_r X_r acts on any one index of a linear tensor Z=sum x_s Z_s, then Wick's formula and B<=2I give

    E||A Z||^2 <=3||B||op sum_s||Z_s||^2.          (2)

Indeed the three Wick pairings give: sum_(r,s)||X_r Z_s||^2 <=||B||op sum_s||Z_s||^2; ||sum_r X_r Z_r||^2 with the same bound by the row-operator norm; and sum_(r,s)<X_r Z_s,X_s Z_r>, bounded in absolute value by the first sum using Cauchy–Schwarz. This applies with arbitrary passive tensor indices.

By (2), the Phi-energy on eigen-index triples with at least one |a_index|>R is at most 9||B||op C0^2/R^2. Taking R=6 leaves at least half the energy. Equation(1) therefore gives

    E sum_(r,i,j)(partial_r K_ij-partial_i K_rj)Phi_rij
       >=(c_6/2) C0^2.                            (3)

On the other hand, curl J=0 distributionally for the chosen r,i index pair because J is a symmetric Jacobian. An arbitrary nonsymmetric vector-map Jacobian would not suffice. The Gaussian adjoint of partial_r is delta_r=x_r-partial_r. Integration by parts pairs K-J with D*Phi, where (D*Phi)_ij=2sum_r delta_r Phi_rij. Since Phi is linear, D*Phi is second Hermite chaos. If Phi_rij=sum_s Z_rijs x_s, the elementary Gaussian quadratic-variance identity gives

    ||D*Phi||_2^2 <=8sum_(r,i,j,s)|Z_rijs|^2=8C0^2.

Thus (3) is at most sqrt(8)epsilon C0. Cancelling C0 (zero case immediate) proves (S) with C=32/c_6^2.

Integration by parts is justified first with compact cutoffs. K and its first derivatives have Gaussian polynomial growth because q is Lipschitz and the slices are fixed; Phi is polynomial. J is only used through its zero distributional curl and L2 difference. Gaussian cutoff errors vanish by Cauchy–Schwarz. Alternatively one may approximate the polynomial test in the Gaussian adjoint graph norm.

## Exact remaining gap

In source101, (X_r)_{ij}=(X_r)_{ji}, but there is no stated identity (X_r)_{ij}=(X_i)_{rj}. Without it, (1) has an additional term, and Phi is not simply a commutator field. Source equality obtains this symmetry from the zero-point Taylor coefficient after passing to an exact finite-dimensional limit. The present estimate therefore removes the point-jet problem ONLY after full symmetry is available. It does not justify projecting to the symmetric tensor: such a projection must first be shown small in the correct unnormalized norm from the analytic deficit.

Even after (S), a dimension-uniform GLOBAL distance-to-orthogonal-tensor theorem remains needed. local-tensor-correction.md proves one only inside an absolute neighborhood. These are separate obligations; neither can be inferred from exact associative-algebra classification.
