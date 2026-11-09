# H015 — too many fixed certificate families for the simple batching premise

Date: 2026-10-08. Verified factoring complexity improvement: **NONE**.
Disposition: reject the polynomial-number-of-families premise of this grouping
rule under the [stated whole-cell hypotheses](../hypotheses/H015.md).
This is a parent mathematical derivation, not independently reviewed or Lean
checked. No finite experiment was run and no shared solver changed.

## The actual structure

The giant exponent from a certificate is E=u+v+Nt. Fix u,t and a residue
r=v mod m², and write v=r+m²*k. For a unit alpha modulo N,

    alpha^E = alpha^(u+r+Nt) * gamma^k mod N,    gamma=alpha^(m²).

Negative exponents use the ordinary modular inverse of the unit. All giant
steps in this family lie on one geometric progression. The occupied k values
need not be consecutive, and their span is not free to fill.

Fast evaluation on geometric points is existing machinery; see
[Bostan–Schost, Table 1 and Section 1](https://mathexp.eu/bostan/publications/BoSc05.pdf).
That source gives field-operation bounds. Its needed inverses and order
conditions must be checked and charged over Z/NZ; no field assumption is
imported here. The counting argument below optimistically grants all
within-family work and addresses only the number of families.

## A whole balanced cell forces small u and t

Set F(z)=u*z+v+N*t/z, and assume |F|<=H throughout [P,2P]. Direct evaluation
at P, 3P/2 and 2P gives the exact identities

    F(P)-3F(3P/2)+2F(2P) = u*P/2,
    F(P)-2F(3P/2)+F(2P) = N*t/(6P).

The triangle inequality therefore gives

    |u| <= 12H/P,       |t| <= 24H*P/N.

For sqrt(N)/4<=P<=sqrt(N)/2 and H<=C*sqrt(N*m), these imply

    |u| <= 48C*sqrt(m),       |t| <= 12C*sqrt(m).             (1)

Subtract j times the first certificate congruence from the second, reducing
modulo m. This gives `Nt=u*j² mod m`. If u=0 then m divides t, since N is
a unit modulo m. For m>(12C)², (1) gives |t|<m, hence t=0, contrary to the
informative-certificate requirement. Thus every certificate for this cell has
u nonzero at sufficiently large m.

## A family serves at most O(sqrt(m)) residue classes

For a fixed family, r fixes v modulo m as well. Its admissible j satisfy

    2u*j = -r mod m.

A linear congruence has either no solutions modulo m or exactly gcd(2u,m)
solutions: divide by that gcd, invert the remaining coefficient modulo the
reduced modulus, then lift. Restricting to units cannot increase the count.
Using u nonzero and (1), one family therefore serves at most

    gcd(2u,m) <= 2|u| <= 96C*sqrt(m)                         (2)

unit residues. The second congruence can only shrink this set. Varying the
center k leaves the first congruence unchanged.

Choose one whole-cell certificate for each of the phi(m) unit residues.
If L is the number of distinct family keys represented, the elementary
covering count from (2) forces

    L >= phi(m)/(96C*sqrt(m)).                              (3)

For the intended smooth moduli with phi(m)=m^(1-o(1)), this is
L>=m^(1/2-o(1)). When m=N^(1/5+o(1)), there are at least
N^(1/10-o(1)) families. They are exponential in the input bit length, not
polynomially many. The unrounded H012 setting has H near 16sqrt(N*m);
for its ceiling and sufficiently large inputs the conservative fixed C=32
suffices. The actual frozen samples are not used to assert (3): they sample
16 residues per N rather than covering all phi(m) residues.

The whole-cell assumption is relevant to the H012 grid: for sufficiently
large N, its dyadic grid from ceil(N^(1/3)) to floor(sqrt(N)) includes a full
doubled cell with P on this balanced scale, up to harmless endpoint constants.
All selected covers certify whole cells. The theorem itself uses the displayed
exact real endpoint assumptions; rounding only changes constants when applying
it to that grid. It does not apply automatically to a scheme allowing arbitrary
tiny subintervals or using information about the true factor's residue.

## What this does and does not reject

The proposed shortcut needed the exact family rule to leave polynomially many
geometric blocks. Equation (3) refutes that premise. Even a conventional
cost bound expressed with a log L product-tree factor still has log L=Theta(n)
when L is between this bound and the method's m*poly(n) generated candidates.
Replacing log G by log L in that bound alone does not yield an extra log n
saving. An upper-bound formula is not a computational lower bound: this
argument does not prove every product tree or multipoint evaluator takes that
many bit operations.

Most importantly, different family keys may have the same
`u+r+Nt mod m²`, or may lie in another geometric progression. Equality of
modular giant values can also involve the unknown order. The count in (3)
does **not** bound the number of distinct giant values or the best possible
geometric grouping. Dropping u,t from the key changes the problem; the linear
congruence argument no longer fixes its coefficient. Such merging would need
a new constructive rule and its own costs.

This does not close H012's different cross-interval reuse question. Nor does
it establish that fast batching is impossible. It identifies the missing step
for this attempt: exploiting relationships between distinct (u,t,r) families,
including unoccupied-center costs, without an order oracle or a unit-cost
arbitrary-point evaluation primitive. That is the next condition for reopening
the batching route; a larger finite sample of same-family runs is insufficient.
