# Original spectral selection does not imply the proposed Peirce gap

Author response to the proposed quantitative interface, preserving the SAME full T101G69 target. This is a counterexample to

  P(H−2H²)P <= f(d0)P,  f(d0)->0,

where B=I, Q=1_(D>d0), P=I−Q, and H=K(Q). In particular no universal constant gives f(d0)=C sqrt(d0). The selection is from the ACTUAL density of the exact-isotropic tensor, not an arbitrary projection. This does not refute the global rounding target; the tensors below converge to unit orthodeco.

## 1. A fixed five-dimensional perturbation

Let T0=sum_(i=1)^5 e_i^tensor3. Let W be the fully symmetric cubic with

  W_12i=1 for i=3,4,5, including every permutation,

and all other coefficients zero. Initially set R_epsilon=T0+epsilon W. Its Gram is

  B(R_epsilon)=I+epsilon² B(W),

because W has no repeated-index coefficients. In particular its first-order Gram variation vanishes.

There is a symmetric positive congruence U_epsilon=I+O(epsilon²) such that

  T_epsilon=(R_epsilon)_(U_epsilon),  B(T_epsilon)=I.  (1)

This is a local normalization near the exact odeco tensor, not an assumed global normalizer. Explicitly, the derivative of the Gram map in a symmetric congruence E at T0 is

  L(E)=2E+4 diag(E),

which multiplies diagonal entries by6 and off-diagonal entries by2. The finite-dimensional implicit function theorem, or the already derived local contraction normalizer, gives(1). Since the initial Gram discrepancy is O(epsilon²), the congruence and resulting tensor change are O(epsilon²). Thus

  T_epsilon=T0+epsilon W+O(epsilon²).                 (2)

Only this expansion and exact B=I are used below.

## 2. Exact leading density

Write E_i=e_i e_i^t and W_i for the slices. The leading slice commutator is

  [X_r,X_i]
    =epsilon([E_r,W_i]+[W_r,E_i])+O(epsilon²).

Consequently D(T_epsilon)=epsilon² D1+O(epsilon³). Direct contraction gives, in the order1,2,3,4,5,

          [12 −3 −1 −1 −1]
          [−3 12 −1 −1 −1]
  D1 =    [−1 −1  4  2  2].                           (3)
          [−1 −1  2  4  2]
          [−1 −1  2  2  4]

A useful independent derivation is D1=B(W)+L_graph, where the graph edge ij has weight sum_r W_rij². The first term comes from the coordinates of the linearized commutator involving its distinguished slice index, and the graph Laplacian comes from the remaining coordinates. Formula(3) can also be verified directly with integer arithmetic.

The two-dimensional subspace

  V_low={x_1=x_2=0, x_3+x_4+x_5=0}

has eigenvalue2. The vector e_1−e_2 has eigenvalue15. On vectors with the two center coordinates equal to a and all three leaf coordinates equal to b, the action is

  (a,b) ->(9a−3b, −2a+8b),

whose eigenvalues are6 and11. Thus the complete spectrum is2,2,6,11,15.

## 3. The actual spectral projections and their limit

Set d0(epsilon)=3epsilon² and define Q_epsilon and P_epsilon from the actual D(T_epsilon). The gap between the leading eigenvalue2 and the next eigenvalue6 implies, for sufficiently small nonzero epsilon,

  P_epsilon -> P0=projection onto V_low,
  Q_epsilon -> Q0=I−P0.                               (4)

This is ordinary finite-dimensional spectral-projection continuity across the fixed threshold3 after dividing D by epsilon². It does not assume continuity of the kernel of D at epsilon=0.

At T0 the channel is diagonal pinching:

  K0(Y)=diag(Y_11,...,Y_55).

The diagonal entries of Q0 are1,1,1/3,1/3,1/3. By(2),(4),

  H_epsilon=K_(T_epsilon)(Q_epsilon)
       ->H0=diag(1,1,1/3,1/3,1/3).

Hence

  P_epsilon(H_epsilon−2H_epsilon²)P_epsilon
       ->(1/9)P0.                                    (5)

In particular its largest eigenvalue is at least1/18 for all sufficiently small epsilon, whereas every f(d0(epsilon)) tending to zero is eventually less than1/18. This proves the claimed obstruction, including the proposed C sqrt(d0) estimate.

Using W_12i=1/sqrt3 instead merely divides D1 by3 and permits d0=epsilon²; it gives the same limiting projections and the same1/9 limit. This explains the normalization in the initial author message to the parent.

## 4. Exact scope of the failure

The exact-nucleus Peirce statement remains valid. In this family all nonzero density eigenvalues vanish on the same scale epsilon². The low/high spectral split remains nontrivial because its threshold vanishes on that scale too. At epsilon=0 the entire space is the nucleus and Q=0; that limiting exact-kernel projection is not the limit of Q_epsilon. Thus replacing exact kernel by low spectrum is precisely the invalid step exposed by this example.

A bound requiring an ADDITIONAL separation between low density and genuinely large density is not refuted here. Nor does the example prove that no trace-paid replacement can handle the intermediate-density directions. It does rule out inferring the desired Peirce gap from the single original spectral cutoff alone.

The full frozen global cubic-rounding target is unchanged and unresolved. Since T_epsilon is already close to T0, this family is compatible with all established local and small-density supporting estimates.
