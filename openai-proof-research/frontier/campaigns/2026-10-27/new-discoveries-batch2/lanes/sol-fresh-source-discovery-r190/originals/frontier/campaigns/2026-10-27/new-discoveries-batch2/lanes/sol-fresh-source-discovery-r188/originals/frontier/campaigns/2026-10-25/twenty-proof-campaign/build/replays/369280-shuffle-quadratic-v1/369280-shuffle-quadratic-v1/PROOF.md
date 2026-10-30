# The quadratic eigenvector of the one-shelf position matrix

For n≥3, use one-based indices and define

\[
M_{ij}=2^{-i}\left[\binom{i-1}{j-1}+\binom{i-1}{n-j}\right],\qquad
V_n(x)=n^2-3nx+\frac32x(x+1)-1,\quad v_k=V_n(k).
\]

This is the exact position kernel in Clay's Theorem1.1, and the vector is that of Conjecture1. Binomial coefficients outside their support vanish.

## Binomial transform

For every r≥0 and real a,b,c,

\[
\sum_{k=0}^r\binom rk(ak^2+bk+c)
=2^r\left(\frac{ar(r+1)}4+\frac{br}2+c\right).
\]

At r=0 this equals c. Pascal's identity changes the left side at r+1 into the transform at r of the polynomial
2ak²+(2a+2b)k+(a+b+2c). Substitution of the induction hypothesis and expansion gives the displayed expression at r+1. If r<n, extension through n−1 adds only zeros.

## Matrix calculation

Fix row i and set r=i−1. Reflecting k↦n−1−k in the second kernel term gives the undivided numerator

\[
N_i=\sum_{k=0}^{n-1}\binom rk\left[V_n(k+1)+V_n(n-k)\right].
\]

Direct expansion shows that the bracket is
3k²+3(1−n)k+(n−1)(n−2)/2. The transform just proved yields

\[
N_i=2^r\left[\frac{3r(r+1)}4+\frac{3(1-n)r}2+\frac{(n-1)(n-2)}2\right]
=\frac{2^r}{2}V_n(r+1).
\]

Dividing by 2^{r+1} gives (Mv)_i=v_i/4 for each row. Moreover v_1=(n−1)(n−2)>0, so v≠0. Its span proves that the eigenspace has dimension at least one.

## Formal correspondence and scope

`positionMatrix` and `quadraticVector` use `Fin n`; the two `one_based` theorems verify their exact correspondence to the formulas above. The transform is proved by induction in `binomial_quadratic`; the reflected finite sum and all matrix rows are proved symbolically. `quadratic_hasEigenvector` uses mathlib's nonzero eigenvector predicate. `quarter_eigenspace_dimension` proves geometric multiplicity at least one. No assertion of exact multiplicity is needed.

The source matrix formula is the definition used for this algebraic theorem. The probabilistic derivation of that established source formula is not a Lean dependency. Finite exact checks in the development lane provide supplemental evidence, but are not part of the universal proof.

## Prior result

[Clay, arXiv:2507.10294v1](https://arxiv.org/html/2507.10294v1), Conjecture1, is the target. [Tripathi, arXiv:2602.07920v1](https://arxiv.org/html/2602.07920v1), TheoremI, already proves a full spectrum theorem and gives a degree-two vector ζ with v=(3/2)ζ. This is a formal verification of a known result, not a new mathematical resolution.
