# H047 compact-filter block reporter: explicit circuit, no improved work bound

2026-10-09 UTC. Paper algorithm and independent review; no implementation or
experiment. Best supported ECDLP exponent1/2; verified gain **NONE**. This
fills in an actual reporter for the mixed-radix construction, but its supplied
upper invoice does not improve on enumerating the long progressions.

## Inputs and complete blocks

Let E:y²=x³+A_E x+B_E over Fp, p>3, and G have odd prime order q. Choose
a public divisor d of p-1 and u=(p-1)/d>=1. The finite subgroup filter is
S={P:x(P)^u=1}; O is excluded. Write delta=|S|/q for its ACTUAL density.
Divisibility alone does not prove delta=Theta(1/d), and computing an exact
cardinality is not free preprocessing. The circuit is correct for any given
block size; its optimized parameter analysis assumes a justified public
density scale, not a cardinality oracle.

Consider one length-M progression P_t=P_0+[t]H with nonzero H of order q,
M<q, as in H047-mixed-radix-success.md. For M>=9, choose integer
1<=b<=floor(sqrt(M)) with D=2b+1<=M. Complete blocks have centers
C_j=P_(jD+b) and points C_j+[i]H for -b<=i<=b. Directly scan the final
partial block, which has fewer than D points. Small M uses direct scanning.
Let a be the number of complete blocks, so a=O(M/b).

Generate centers, offsets iH and integer descriptors, charging their group
operations and normalization. Centers are distinct as points because D<q,
H has order q, and a<q; they may repeat as abscissae. A center O occurs at
most once and its block is scanned directly. One conservative version also
directly scans centers whose abscissa equals an offset abscissa. There are at
most 2b such centers. Detect these by sorted abscissa lists or another paid
exact lookup, not an unpriced pairwise comparison loop. Their scan work is
O(b²). Exclude these exceptional centers from the polynomial stage.

## Division-free resultant flags

For remaining centers form the monic polynomial
L(X)=product_j(X-x(C_j)). If there are none, skip this stage. Retain all
center descriptors even when abscissae repeat. Work in R=Fp[X]/(L), without
assuming R is a field or that L is squarefree.

For y_i=x(iH), 1<=i<=b, write the short-Weierstrass summation polynomial as

    F_i(X,Z)=A_i Z²+B_i Z+C_i,
    A_i=(X-y_i)²,
    B_i=-2((X+y_i)(X y_i+A_E)+2B_E),
    C_i=(X y_i-A_E)²-4B_E(X+y_i).

For ordinary finite points with distinct abscissae, its Z-roots are exactly
x(C_j+iH),x(C_j-iH). The general biquadratic relation is classical; root
read [BDLS, Lemma 4.3 and sections 4.5–4.10](https://arxiv.org/pdf/2003.10118).
Its particular evaluation algorithm is not automatically a theorem about this
reporter; the following circuit and cost are derived and reviewed here.

Compute in R the polynomial identity

    Res_Z(Z^u-1,F_i)=A_i^u+C_i^u-T_u,
    T_0=2, T_1=-B_i,
    T_j=-B_i T_(j-1)-A_i C_i T_(j-2).

For generic roots alpha,beta of F_i, T_j=(A_i alpha)^j+(A_i beta)^j.
The resulting formula is a polynomial identity in the coefficients, so it
continues to hold in the quotient ring and at degree drops. Freeze the shown
resultant order: reversing actual-degree resultants can change the sign when
A_i specializes to zero. No inversion is used. Matrix powering computes T_u
in O(log(u)+1) ring multiplications.

Multiply all b residues and the center factor X^u-1 modulo L. The latter
includes offset zero and has a paid modular-power cost. Evaluate this product
at the recorded center abscissae by monic polynomial remainders. Repeated
abscissae cause no problem; interpolation or division by their differences is
neither required nor allowed for free.

At a nonexceptional center, a zero occurs exactly when one of its represented
finite points belongs to S. All roots of Z^u-1 are in Fp since u divides p-1,
but the circuit never enumerates those roots. Scan every flagged block in
full, perform exact point membership tests, and emit the actual integer
indices/orientations. The directly dispatched blocks and partial tail emit
their own witnesses. An output cap aborts an oversized trial explicitly.
The optional conservative equal-abscissa dispatch avoids relying on tangent
specializations; these can also be handled directly without inversions in R.

## Paid invoice and success scope

Using standard polynomial multiplication/remainder/evaluation algorithms,
the polynomial stage has upper field-operation invoice

    softO(ab (log(u)+1) + a + b).

The soft notation retains polynomial-arithmetic logarithms. Explicit lists
and product trees use softO(a+b) field-record space, not an unqualified linear
workspace bound. Returned records and their sort/match workspace are additional.

For a fixed complete block, its flag indicator is at most the number of actual
filter hits in that block. Thus the randomized progression's uniform point
marginals and linearity of expectation give O(M delta b) expected ordinary
flagged scanning. No independence between blocks or Poisson model is needed.
Add O(b²+b) exceptional/tail scans. Each scanned membership test pays a
modular power, and each generated/scanned point pays group arithmetic. A
conservative separate ledger is:

- polynomial field work as above;
- O(a+b+log q+b²+b+M delta b) expected group operations, including initial
  scalar-multiplication setup and scans, plus their actual normalization cost;
- O((b²+b+M delta b)(log(u)+1)) field operations for exact scanned powers;
- capped output records K, their softO(K) sorting/matching operations and
  coordinate/index/scalar bit widths, seed/setup/retry work and verification.

One can conservatively price each affine group operation by I_p+O(1) field
operations with charged inversion I_p, rather than hiding it in a group count.
A projective/batched implementation needs its own precise invoice. Nothing
here is a measured runtime or a constant-factor improvement.

Under a justified density scale, choose b of order min(delta^-1,sqrt(M)),
with integer constraints above. Then M delta b<=O(M) and b²<=M; expected
work is softO(M) up to inversion and bit-arithmetic costs, and capped space is
softO(sqrt(M)+M delta) field/index records. Even without expectation, scanning
each disjoint block at most once is bounded by M points. The H047 output-cap
and rejection analysis preserves constant success under its explicit density
assumptions; caps do not silently turn unsuccessful trials into solves.

For two independent progressions U_t=Q+[r+t h]G and V_v=[s+v g]G, retain
indices at every equal-abscissa cross match. Test both equations
k=+/- (s+v g)-r-t h modulo q and verify kG=Q. The filter is symmetric;
expected indexed signed cross matches are at most 2M²|S|/q², hence O(1) at
the accepted parameters. This bounds expected candidate verification work,
not the maximum number on every trial. Exact matching, aborts and all failed
trial work remain paid. No unknown log is used to generate either list.

Since M has order q^((1+gamma)/2), this supplied invoice does not establish
sub-square-root total work for gamma>0. Direct enumeration already has the
same M-scale upper bound. No Omega(M) theorem for arbitrary compact circuits,
or novelty claim, follows. The next needed operation is cheaper shared
reporting WITH witness extraction, not another compact polynomial name.

## Independent checks and disposition

Native Sol /root/h034_c4_implementation supplied the circuit. Native Astra
/root/h007_additive_relations independently checked resultant order, quotient
zero divisors, repeated roots, offset zero, block boundaries, flags and scans.
Root separately derived the recurrence, checked exact integer block indices,
exception count, paid point arithmetic, output recovery and source scope.
All roles read-only; root alone integrated. No test or infrastructure admitted.
No scripts/imports/experiments, seeds, curve instances, Lean claims or Audit
additions. H034 consumed cap unchanged. Validation command/result in STATE;
existing Lean compilation does not certify this paper construction.
