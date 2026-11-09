# W008 displacement multiplication audit

2026-10-08. Independent child review of the original full brief and the frozen
parent derivation. **Accepted, with the representation scope made explicit.**
The determinant formula and transfer to generic split lists in characteristic
zero are correct. Two individually rank-2 displacement factors have a product
of displacement rank K. This refutes a uniform bounded-rank closure claim for
this operator. It does not prove a lower bound for other representations,
scalar norms, arithmetic circuits, random inputs, or factoring.

The one escape audited here is a scalar norm tree with shared preprocessing.
Its identities are valid, but the explicit shared polynomial has K^2+1
coefficients. The fully specified elementary implementation below takes
Theta(K^4) ring operations and Theta(K^2) stored ring elements. It provides
no improvement over the already paid K^2 poly(log N) evaluator.
**Verified factoring improvement: NONE.**

## 1. Read scope and evidence

Read AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md and
`docs/SPECIFICATION.md` in full; read the current/resume and closing portions
of STATE for context. Read the parent displacement note in full and **only
section 9** of the four-list review for the mathematical motivation. The prior
probability/bit-cost audit, affine-grid review and W007 residual dynamics were
not reopened. No external prior-art or novelty claim is made: all identities
used below are derived here.

[Input manifest](W008-displacement-review-inputs.json) records immutable copies,
byte counts and SHA-256 hashes for eight inputs, frozen at
2026-10-08T20:13:24Z. In particular:

- Parent displacement note: `b48466bdcb0926a56a1da04909679d920c432292aae2878ee026dd7d7ed48890`.
- Original four-list motivation: `cde42fe85d005f8a8cb37ec1f302ce3d77c875a0982f378f8461f70489a33579`.

Parent work can continue independently; conclusions here refer to those
snapshots. All created files have the assigned `W008-displacement-review`
prefix. No shared state/task/source/Lean file was changed. No packages,
delegation, candidate runs, parameter sweeps, commits or publication occurred.
The only executed arithmetic check was the single exact symbolic identity in
section 5; it is corroboration, not the proof for general K.

## 2. Exact all-K proof

Use indices 0,...,K-1 and the downward shift J, so

    Delta(M)[r,s] = (r>0 ? M[r-1,s] : 0)
                 - (s>0 ? M[r,s-1] : 0).

For a general single degree-K factor, the truncated unreduced scaled array
has entries `(r+s)! h_(r+s)` with h_t=0 for t>K, hence is Hankel. Monic
reductions of the two degree-K pure terms change only row 0 and column 0.
Its displacement therefore has support only in rows or columns 0 and 1,
and rank at most 4, uniformly in K. In the proposed family the stronger
rank-2 assertion follows directly below.

### The residue and its scaling

Expand `(X+Y)^(2K)` using X-exponent t. Terms with t<=K have Y-exponent
2K-t>=K and vanish. Write the remaining exponent as t=K+r. For
1<=r<=K-1, reduction gives `X^r Y^(K-r)`; t=2K gives 1. These outputs are
distinct basis monomials. Thus exactly

    C[0,0] = 1,
    C[r,K-r] = binom(2K,K+r),   1<=r<=K-1.

Multiplication of each coefficient by r!(K-r)! gives

    w_r = (2K)! r!/(K+r)!.

For a single H, the same calculation gives scaled mixed entries K! on
r+s=K, and entry 1 at (0,0). The mixed anti-diagonal cancels in Delta;
its displacement is exactly `E_(1,0)-E_(0,1)`, of rank 2 for every K>=2.

### Support, signs and determinant

For the product, the (0,0) entry contributes the isolated block

    rows/columns 0,1:  [[0,-1],[1,0]].

A shifted mixed entry must lie on r+s=K+1. Since both indices are at
most K-1, both must be at least 2. Conversely each r=2,...,K-1 has
s=K+1-r in that range and both contributions exist. Their difference is

    w_(r-1)-w_r
      = (2K)! (r-1)!/(K+r-1)!
        - (2K)! r!/(K+r)!
      = K (2K)! (r-1)!/(K+r)! =: d_r > 0.

There are no additional entries, and no connections between the two
blocks. On indices 2,...,K-1 the array is an anti-diagonal matrix of
size m=K-2. Its reversal permutation has m(m-1)/2 inversions. The first
block has determinant 1, giving exactly

    det Delta = (-1)^((K-2)(K-3)/2)
                product_(r=2)^(K-1) d_r != 0.

K=2 has an empty second block and determinant 1. K=3 has a one-entry
second block, so there is no parity/skew-symmetry objection in odd
size. The product array need not be symmetric after the unequal quotient
reductions. Hence rank Delta=K for every K>=2.

No algebraic correction to the parent's formula is needed. The operation
is **one multiplication of two input factors**, or two accumulator updates
starting at 1. At K=2 full rank already holds for a single factor; the
unbounded growth assertion concerns the family as K increases.

## 3. Transfer from coefficients to split-list roots

Fix K. Let P be the polynomial ring over Q in the nonleading coefficients
of three independent monic degree-K polynomials F_A,F_C,F_D, and in two
shifts b_1,b_2. Monic division by F_C and F_D uses no coefficient inverses.
Consequently the residue coefficients of

    F_A(X+Y-b_1) F_A(X+Y-b_2)

are in P, as are their factorial scalings and the determinant D of the
displacement. The certificate in section 2 is a specialization of D to a
nonzero rational integer. Thus D is a nonzero polynomial. F_C need not
split over Q for this implication, and repeated roots present no problem:
the monic quotient is free of rank K^2 even on those fibers.

Now introduce independent formal lists alpha_i, gamma_i, delta_i and map
the three coefficient blocks to their signed elementary symmetric
polynomials. This map is injective. An elementary proof uses lexicographic
order z_1>...>z_K: the leading monomial of e_j(z) is z_1...z_j. Thus

    leading monomial of product_j e_j(z)^m_j
       has z_i-exponent sum_(j>=i) m_j.

These exponent vectors determine every m_j by successive differences.
Distinct monomials in the e_j therefore have distinct leading monomials;
a polynomial relation cannot cancel its largest one. Apply this argument
to the three disjoint variable blocks, retaining the shifts as independent
variables. Signs in the monic coefficients do not change injectivity.
For a split B list, simply set b_1=beta_1 and b_2=beta_2; K>=2 supplies
these independent variables, and unused beta entries add free variables.

The image of D is consequently nonzero. Full rank holds on a nonempty
Zariski-open set of characteristic-zero split-list tuples. Over Q, an
infinite field, such tuples also exist with rational entries. This remains
true on the open locus where each list has distinct entries: multiply D
by the relevant nonzero discriminant products in the root polynomial
ring. The repeated entries and equal shifts of the displayed witness do
not confine the generic conclusion to that special locus.

This is an algebraic genericity statement, not a sampling estimate. It
provides no claimed success probability on the finite modular domains
used for factoring. Characteristic changes, factorial scaling when it is
not invertible, and reductions where the certificate vanishes require
separate treatment; no modular probability or factoring conclusion is
inferred here.

## 4. Exact scope of the storage obstruction

Over the characteristic-zero field, `Delta=UV^T` with U,V of size K-by-r
implies rank Delta<=r. Thus any such generator for this product requires
r>=K. A storage scheme allocating every entry of both arrays needs at
least 2K^2 slots at that point, before any reconstruction boundary data.
This defeats a uniform o(K)-column generator guarantee and its claimed
O(Kr) saving under this explicit dense-array convention.

It does **not** mean every representation of a full-rank generator needs
K^2 independently stored numbers. In this witness Delta has O(K) nonzeros
and a factorial formula. For example U=I and V=Delta^T admit sparse or
implicit descriptions even though they have K columns. All input lists
also have only O(K) entries. Rank supplies no information-theoretic or
arithmetic-circuit lower bound for their derived arrays.

There is a particularly sharp scalar check: for the witness, H is 1
modulo the nilpotent ideal (Y), since X^K=1. Multiplication by H is the
identity on each successive quotient of the Y-adic filtration, each of
dimension K. Its multiplication matrix is triangular in a filtration
basis with all diagonal entries 1. Hence

    Norm_Q(H)=1,     Norm_Q(H^2)=1.

The full-rank displacement witness therefore has a trivial scalar norm.
This reinforces rather than weakens the scoped closure obstruction.

## 5. Executed symbolic cross-check

The [exact check output](W008-displacement-review-symbolic-check.json) uses
K=3 once, retaining u,v as formal indeterminates and reducing in
`Z[u,v][X,Y]/(X^3-u,Y^3-v)`. A standard-library sparse polynomial expansion
and the six-term 3-by-3 determinant expansion verified

    H = u+v+3 X^2 Y+3 X Y^2,
    H^2 = u^2+20uv+v^2
          +(6u+15v) X^2 Y+(15u+6v) X Y^2,
    det Delta(scaled H^2)
          =18(u-v)(u^2+20uv+v^2)^2.

The calculation independently formed H*H and `(X+Y)^6` and checked their
equality; it also checked that the single-factor 3-by-3 displacement
determinant is zero. At u=1,v=0 the displayed symbolic formula gives 18,
matching the all-K proof. There was no loop over K, sampled root list,
factoring instance, benchmark or parameter search. No Lean certification
is claimed.

## 6. One concrete escape: scalar norm tree with shared preprocessing

Work over a commutative base ring R, including Z/NZ, with the original
split lists of length K. Put n=K^2 and let T_C,T_D be the K-by-K matrices
for multiplication by X,Y in their univariate monic quotients. In Q,

    S = T_C tensor I_K + I_K tensor T_D

is the multiplication matrix of X+Y and has **dimension n by n**, not
K by K. Each H_b has multiplication matrix F_A(S-b I_n), also n by n;
storing one such dense matrix would use K^4 ring elements.

Define the common monic polynomial

    G(t) = det(t I_n-S)
         = product_(c in C,d in D) (t-c-d),    degree G=n.

For completeness, over the fraction field of independent formal roots
with distinct entries, evaluation at all (c,d) diagonalizes S and proves
the product identity. Both sides are polynomials with integer
coefficients in the roots, so equality there is a polynomial identity.
Specialization proves it over every commutative R, including repeated
roots and nonunits. The execution below uses no diagonalizing inverse.

Since F_A splits and determinant is multiplicative,

    s_b := Norm_Q(H_b)
         = product_(a in A) det(S-(a+b) I_n)
         = (-1)^(K^3) product_(a in A) G(a+b).

For a binary tree on the K factors indexed by B, let H_I be the product
at a node and s_I its norm. The actual scalar update is

    s_(I union J) = s_I s_J,
    s_root = (-1)^(K^4) product_(a in A,b in B) G(a+b).

The K-1 internal multiplications are cheap, but this says nothing about
free leaf acquisition. Here is an explicit division-free algorithm that
pays for it, rather than appealing to a structured determinant routine.

### Coefficient and scalar updates, with complete charges

Enumerate the n sums c+d from the input lists without retaining a pair
list. Begin with q_0(t)=1. If s is the next sum and
`q_m(t)=sum_(j=0)^m q_(m,j)t^j`, update

    q_(m+1,j) = q_(m,j-1) - s q_(m,j),

where coefficients outside 0,...,m are zero. Descending updates in one
array, with space for the next leading coefficient, implement this
identity. After n steps the array is G. This is n sequential updates of
length Theta(m+1), hence Theta(n^2)=Theta(K^4) elementary ring operations
and n+1=K^2+1 coefficient slots; generating the sums adds O(K^2)
additions. This is a concrete slow upper bound, not a claim of optimality.

For **each of the K shifts b**, initialize a scalar accumulator and visit
**each of the K roots a**. Evaluate G(a+b) by the recurrence

    h_n=1,
    h_j=(a+b) h_(j+1)+g_j,    j=n-1,...,0,

then multiply h_0 into that factor's accumulator and apply the sign.
There are K^2 such evaluations, each with n multiplications and n
additions: Theta(K^4) ring operations in total. Products within the K
leaves add O(K^2) operations. Combining their norms adds K-1 more.
Keeping every scalar tree node needs O(K) ring elements; streaming a
single root needs still less. Neither changes the dominant stored G.

All determinant/norm extraction has now been replaced by explicit
coefficient updates, evaluations and scalar products. No n-by-n matrix
is materialized, no oracle is hidden, and repeated entries/nonunits do
not break the identities. Over Z/NZ, canonical residues give
Theta(K^2 log N) bits in a fixed-width coefficient array and a conservative
O(K^4 poly(log N)) bit upper bound for this implementation. Rational
coefficient heights are a separate issue; this ring-operation count is
not a characteristic-zero bit bound.

### Disposition of this escape

The shared dense G immediately recreates K^2 coefficient slots, so any
implementation explicitly materializing it has already failed an
o(K^2)-work/state target, irrespective of subsequent improvements to
multiplication or evaluation. This is a symbolic output-size objection
to this materialization step, not a lower bound for G in other forms.

The same scalar formula can instead leave G factored and evaluate
`G(t)=product_(c,d)(t-c-d)` directly. That uses O(K) input storage and
constant working accumulators, but still K^2 operations at each of K^2
points, hence Theta(K^4) total. Retaining a B norm tree adds only O(K)
scalars. Thus **quadratic storage is not forced for every scalar norm
algorithm**; this alternative storage schedule pays with the displayed
work. Neither schedule improves the already reviewed paid evaluator.
No claim about localization costs or a new complete splitter follows.

The failed assumption is that cheap scalar internal-node updates make
the K leaf norms cheap. The exact replacement obligation is a jointly
shared computation of `product_(a,b) G(a+b)` directly from the four input
lists, with subquadratic total work and without the K^2-coefficient
expansion. Giving G a short product formula does not supply that
computation. A concrete recurrence meeting that obligation, including
its nonunit behavior and all K leaf factors, would change this escape's
disposition. A new displacement operator would be a separate audit;
none was evaluated here.

## 7. Handoff

Accept the parent's two-factor determinant and characteristic-zero
split-root transfer. Retain the dense-generator qualification and read
“two updates” as accumulation of two factors; do not report two binary
product gates or growth at K=2. Close the uniform bounded Hankel
displacement-rank representation under this multiplication.

Reject the particular shared-G materialization as a subquadratic escape.
The scalar-tree identity survives, with leaf acquisition still the exact
missing fast primitive. General implicit norm computation remains open.
The useful next step is to audit an explicit alternative recurrence and
its full state/work account, not to screen this identity on factoring
inputs. No new factoring improvement is established.
