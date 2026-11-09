# W030 continuation: a real digit-cut recursion and its remaining pair count

Parent derivation after the W030 audit was delegated; this continuation is
outside that audit's original scope. No experiment. No complete improvement.

The uncarried kernel changes the problem enough to admit an explicit
divide-and-conquer operation. Let R_L(a,b) denote the truncated digit
convolution from W030. Split off h low digits, with 2h<=L:

    a=a0+B*a1, b=b0+B*b1, B=ell^h, 0<=a0,b0<B.

Use the zero-padded digit vectors in each R below. Then, over the integers,

    R_L(a,b) = a0*b0
       + B*R_(L-h)(a1,b0) + B*R_(L-h)(a0,b1)
       + B^2*R_(L-2h)(a1,b1).

Set R_0=0. Each original digit pair occurs exactly once in this expression
and survives precisely when its total digit index is below L.

Partition rows by a0 and columns by b0. In one Cartesian bucket pair,
the first term is constant, the second depends only on the row, and the
third only on the column. They can be absorbed into the existing scalar
row and column labels. The remaining interaction has L-2h digits, base
alpha^(B^2), and the high inputs truncated to those L-2h digits. This is
an actual recursively defined kernel, not an assumed coefficient oracle.
The original carry multiplier alpha^(-Q*tau) remains a scalar column label
or a separately indexed carry list. Public setup and all bucket copies cost
work; the factor product is unchanged.

At L=2h the interaction vanishes. Inside each bucket pair the remaining
product has the form product_(i,j)(1-r_i*s_j), with a fixed additional
carry factor if needed. This is an ordinary supplied multiplicative
collision product. It can be computed by a monic product polynomial and
multipoint evaluation, after checking/inverting only the unit row or column
labels, in soft time linear in the two list lengths for a fixed carry.
It does not require outputting every pair. Nonunits can instead be gcd-tested.

There is an exact obstruction to using this terminal split on the balanced
root tables. Here L is even and B=ell^(L/2)=M_t. If two rows have the same
low root A modulo B, then A^2=c*u modulo B, with c=4N*delta^epsilon a unit.
Thus their u labels are congruent modulo B. In an interval of diameter
less than B they are the SAME row. The same holds for the v table because
its scale is a unit. For balanced U,V much smaller than M_t, all nonempty
terminal buckets are therefore singletons (or a fixed number of pieces
after splitting signed domains). The algorithm has UV bucket pairs and
has not eliminated the explicit-record cost.

Earlier splitting has a concrete cost account too. After fixing a low
prefix of modulus B, each bucket contains at most O(1+U/B) row labels or
O(1+V/B) column labels, by the same congruence argument. At most
min(U,B)*min(V,B) Cartesian pairs must be considered, up to the constant
number of square/sign classes. Materializing their row/column labels
costs at most O(U*min(V,B)+V*min(U,B)), times digit/bit overhead. No lower
bound on the number of occupied pairs is inferred from these upper bounds.
An actually selected common low-digit filter removes only its specified
residue blocks; it does not make the terminal rows noninjective.

This rejects the full-prefix recursion as a route past the M term. It
does not reject a computation that combines several bucket pairs, uses
nonlinear information about the particular tables, or stops earlier and
computes the remaining interaction without expanding it. The precise next
question is joint processing of bucket pairs: the cross terms acquire both
bucket labels, so merely calling each terminal product independently loses
the desired sharing.

One setup detail for the initial block polynomial can be made explicit.
Let s_i=ell^i*(B_v mod ell^(L-i)) and X_i=alpha^(-sign*s_i). Then

    X_0=alpha^(-sign*B_v),
    X_(i+1)=X_i^ell * (alpha^(sign*Q))^(b_(v,L-i-1)).

This computes all column coordinates with one binary exponent setup and
O(L log ell) modular multiplications, using only unit powers. The expensive
step is the aggregate product, not acquiring these column coordinates.

Read the earlier subset-expansion cost as an explicit enumeration of the
2^b subsets, not a support-size lower bound: coincident exponent vectors or
coefficient cancellation could make a different implementation smaller.
Likewise its dense-box count prices that particular allocation. Neither
count rules out a more compact specialized circuit. Fixing the low digit
also lets its common monomial be absorbed into Y, but removing one of the
L growing coordinates does not resolve the dense-box cost.

Subsequent status: [reviewed with explicit parent corrections](W030-kernel-and-frontier-parent-disposition.md).
The terminal monic product and its shared-carry extension are real supplied
algorithms. The direct cut still reaches the pair count. A rank-one
bilinear exponent must not be confused with multiplicatively separable
labels: the latter arise here only once the residual exponent is zero.
