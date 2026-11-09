# W028: a sublinear coefficient-or-factor baseline over a composite ring

Parent correction to the independent parity review. No numerical experiment
or new factoring improvement. This is a standard product-tree construction,
written out because restricting the comparator to a linear scalar scan is
too weak. It does not read or compress the W028 Newton circuit.

Let N>1 be odd and 1<=m<N. The task returns either binom(2m,m) modulo N or
a proper factor of N. Put b=ceil(sqrt(m)), s=floor(m/b), h=m-s*b. Form
over R=Z/NZ the degree-b polynomials

    D_b(T)=product_(i=1..b)(T+i),
    A_b(T)=product_(i=1..b)(4*(T+i)-2).

Evaluate both at T=jb, 0<=j<s, by ordinary monic multipoint evaluation.
The product trees and remainder trees use ring arithmetic; division in the
remainder tree is by monic polynomials, not by arbitrary residues or point
differences. Thus this construction needs no hidden field or known factors.
Compute the remaining h<b factors directly. Multiplying all denominator
blocks and tail entries gives D=m! mod N. The analogous numerator is
A=product_(i=1..m)(4i-2) mod N.

If gcd(D,N)=1, return A*D^(-1) mod N. This equals the required coefficient
by the integer identity D*binom(2m,m)=product(4i-2).

If gcd(D,N)>1, scan the s stored denominator block values and at most h
tail entries. A proper gcd is already an answer. If a block has gcd N,
scan its b original integers; at least one has nontrivial gcd. Because
each lies between 1 and m<N, none can have gcd N, so the first nontrivial
gcd is proper. This also handles prime powers and other nonsquarefree N.
Only one full-gcd block needs expansion. A unit total product cannot hide
a nonunit denominator factor.

Both polynomial degrees and the number of evaluation points are O(sqrt(m)).
Fast polynomial arithmetic gives O~(sqrt(m)) ring operations, plus
O(sqrt(m)) gcd calls and one unit inversion. A conservative bit account is
O~(sqrt(m)*M_int(log N)); all stored residues have O(log N) bits, with
ordinary polynomial-convolution temporary widths charged. Space is
O~(sqrt(m)*log N). The monic evaluation construction avoids the additional
small-integer invertibility hypotheses of some faster progression-shift
implementations.

This is a disjunctive contract. In the factor branch it need not also return
the coefficient. That branch is useful to a factoring caller, but must not
be silently represented as an unconditional scalar-coefficient evaluator.
For m=0 the answer is 1 without this construction.

Primary comparator: Bostan, Gaudry and Schost,
[Linear recurrences with polynomial coefficients and application to integer
factorization and Cartier–Manin operator](https://mathexp.eu/bostan/publications/BoGaSc07.pdf),
introduction, printed pages 1779–1780, explicitly describes Strassen's
block-factorial method and its validity in any ring. Their later optimized
algorithms have additional invertibility conditions which they account for
in the factoring application. The parent read the introduction and the
statement of Theorem 11, not the entire paper. No novelty is claimed here.

Consequences: taking m=floor(sqrt(N)) already ensures the factor branch for
every composite N and recovers the classical N^(1/4) scale. Taking m on the
order of N, as in W022's central-coefficient selector, makes this baseline
slower, not faster. Neither comparison improves the separately verified
one-fifth deterministic reference. Degree preservation over Q does not
preclude a sublinear scalar algorithm; this baseline makes that distinction
explicit, while leaving the desired faster Newton-circuit consumer unresolved.
