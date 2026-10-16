# Focused second attempt: mathematical checkpoint

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

Full U remains UNRESOLVED. No scope or campaign count change.

## Live history corridors

For a fixed graph and elementary partition, expand the source recursion
wall:recursion / route:history-recursion into a finite directed acyclic
skeleton: vertices are (chamber, exponent), edges strictly lower free-cone
height, and each edge weight is its full positive rational jump series.
Retain only edges lying on a nonzero path from (H_-,u) to terminal label
x_lambda. For a fixed skeleton path, all edge decorations are independent;
its generating series is the product of edge jump series.

Since the sum of these nonnegative products is the finite target polynomial
v^(-M)c_lambda(v^2), every live edge series is a finite Laurent polynomial.
Proof: fix one nonzero coefficient in every other factor on a complete path.
Each support exponent of the chosen factor, shifted by their fixed sum,
must occur in the total target. Its support is therefore finite. Dead edges
and targets with zero coefficient impose no such condition.

## Rational bar involution

Work over Q(v) at each root order, before embedding in Q((v^-1)). The source
ensures every coefficient is rational. Define bar(v)=v^-1 and bar(X_a)=X_a,
as an anti-involution. For the normalized D_p, bar(D_p)=D_p^-1: the log at
jp has coefficient (-1)^(j+1)/(j(v^j-v^-j)), which changes sign under bar.
The multiplicative automorphism tau(g)=bar(g)^-1 preserves the root cone,
each three-factor sign subgroup and the incoming prescription. Uniqueness
of the source incoming equations therefore gives tau(g)=g and fixes every
middle/wall factor. Every wall adjoint commutes with bar. Its scalar jump
coefficient is bar invariant as a rational function. Combined with the
live-edge finiteness proof, every live jump is a positive, centered,
palindromic Laurent polynomial.

This is a valid strengthening of the bookkeeping interface, not U. A finite
positive centered polynomial need not be Lefschetz. The actual local first
differences, or an aggregate partition-preserving rank injection, remain
unpaid.

## Cluster-monomial route

Davison, Positivity for quantum cluster algebras (Annals 2018), Theorem 2.4,
label mainThm in retained primary source, gives Lefschetz Laurent coefficients
for cluster monomials in arbitrary compatible skew-symmetric seeds; acyclicity
is not its hypothesis. This is stronger for cluster monomials than the general
theta result used in r8. To use it requires an exact cluster-monomial (or
Lefschetz-positive combination) realization of the pinned section together
with coefficient/normalization preservation. No such realization is obtained.

A source-section test for the blanket monomial assertion is available in the
D=2 chart: U=Theta_(d1)=A+B+C, with AC central. At v=1 and AC=1, the injective
map A=x/y, B=1/(xy), C=y/x sends U to z=(x^2+y^2+1)/(xy). In the ordinary
rank-two two-arrow cluster algebra with initial cluster x,y, z is not a cluster
monomial: at x=y=1 it is 3. All cluster variables occur in the alternating
mutation recurrence x_(k-1)x_(k+1)=x_k^2+1. Their values are 1,1,2,5,13,...
in either direction and strictly increase after 2. No variable has value 3,
and no product of adjacent cluster variables with nonnegative powers has
value 3. This proves only the asserted failure in this natural rank-two
realization. It neither rules out all larger realizations nor refutes U.
