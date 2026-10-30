# An inactive-coordinate rotation

The target is Conjecture3 in AppendixD of Centorrino, Bullo and Russo, [arXiv:2506.06134v1](https://arxiv.org/html/2506.06134v1), also MathDB368725. It asserts that an orthogonal U must be a permutation if the matrix

K=Uᵀ Lᵀ (L U D Uᵀ Lᵀ)^(-1/3) L U

is diagonal, for rectangular diagonal L and positive diagonal D with distinct entries.

Take L=[1,0,0], D=diag(1,1/2,1/3), and

\[
U=\begin{pmatrix}1&0&0\\0&3/5&-4/5\\0&4/5&3/5\end{pmatrix}.
\]

Since (3/5)²+(4/5)²=1 and the two rotation columns are perpendicular, UᵀU=UUᵀ=I. D is positive definite and its diagonal entries are pairwise distinct. L has the exact source rectangular diagonal form with positive active entry and full row rank.

Direct multiplication gives LU=L and LU D UᵀLᵀ=[1]. Its negative one-third power is [1]. Hence K=LᵀL=diag(1,0,0), which is diagonal. But U_(2,2)=3/5 is neither zero nor one, whereas every permutation-matrix entry is zero or one. Indeed it is not even a signed permutation.

This satisfies all source conditions and refutes the conclusion. It illustrates the mechanism: the last two coordinates are in the kernel of L, so their rotation has no effect on LU. No distinctness assumption on D can recover information discarded by L.

## Formal coverage

The source expression is `stationary`, using `CFC.rpow` on real matrices with the standard positive-semidefinite matrix order. The positive active block is proved equal to the identity, and the actual functional-calculus theorem `CFC.one_rpow` evaluates its fractional power. No abstract oracle for fractional matrix powers is postulated.

`orthogonal_left` and `orthogonal_right` prove both matrix products. `positive_diagonal`, `diagonal_distinct`, and `rectangular_diagonal` verify the data. `not_permutation` rules out every mathlib permutation matrix. The final `counterexample` bundles all source requirements, including positive definiteness of the active block, and the failed permutation conclusion.

## Prior status and scope

Shivam Patel's posted MathDB counterexample already uses arbitrary orthogonal rotations of inactive coordinates, with a displayed 2-by-4 instance and a general family. The present 1-by-3 instance is a smaller formal verification of that same mechanism. We do not claim discovery, the full corrected rigidity classification, or a repair of the paper's separate trace-maximization theorem.
