# Formal scope

The final theorem is `NormOneCounterexample.main_counterexample`. It proves:

1. Every entry of the displayed real matrix is strictly positive.
2. Corresponding row and column sums are equal.
3. The vector `w=(2,2)` is nonzero and satisfies `J*w=2*w`.
4. Every complex eigenvalue of the same matrix has modulus at most 2.
5. The actual mathlib Euclidean norm of `w` is not 1.
6. Its Frobenius norm, defined as the square root of its sum of squared
   real entries, is not 1.

The spectrum lemma proves over every field that any eigenvalue of `J` is 0
or 2; the complex bound is therefore a conclusion, not an assumption.
`norm_square` certifies the value 8 for the squared Euclidean norm.
The main theorem refutes exactly the unnormalized statement in the source.

No dominant-eigenvalue existence theorem or Perron--Frobenius theorem is
assumed. The exhibited pair supplies existence. The explanatory general
observation about rescaling eigenvectors is written mathematics; the finite
counterexample fully suffices and is formally certified.

Numerical experiments are unnecessary for this result. Its scientific scope
is an elementary correction of a normalization omission. This should not be
presented as a deep or historically novel spectral result.
