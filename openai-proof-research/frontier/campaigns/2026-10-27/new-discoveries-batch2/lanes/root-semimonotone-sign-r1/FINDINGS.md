# Semimonotone exact-order-two: a sign reduction, not a resolution

29 October 2026 UTC. Target: Chauhan–Dubey, arXiv:2603.00639v1,
Definition 3.7 and Conjecture 3.12 / MathDB373375. All principal
(n-2)-blocks are E0; all principal (n-1)-blocks are almost E0.
The source's Theorem 2.2 gives their entrywise nonpositive inverses.
Full nonsingularity, det A<0 and inverse Z remain UNPROVED.
Credit0; count3 additional/33 total unchanged. No novelty or Lean claim.

This follows root's direct read of the source and the completed Sol r6 report.
It does not adopt the source's apparent swapped inequalities in the preliminary
prose definition of almost (strictly) E0: the literal exact-order definition
and the stated inverse theorem are the dependencies.

## 1. Ordinary sign lemma

Let n>=3 and B be nonsingular with every b_ii nonzero. Suppose for each i
the single-pivot Schur complement is entrywise nonpositive:

    b_jk - b_ji b_ik / b_ii <= 0     (j,k distinct from i).       (S)

Then all diagonal entries have the same sign. Moreover exactly one of the
following descriptions applies:

* diagonal positive, all off-diagonal entries strictly negative;
* every entry strictly positive;
* diagonal negative, every entry nonpositive.

No originality is claimed for this elementary sign lemma.

### Mixed diagonal signs are impossible

Suppose b_ii>0>b_jj. The two diagonal inequalities in (S) give
b_ij b_ji=b_ii b_jj<0. Put r=b_ji/b_ii.
If r>0, the two row inequalities give, for every k other than i,j,

    b_jk <= r b_ik,   b_ik <= b_jk/r.

They are equalities; the same row proportionality holds at i,j from the
product identity. B is singular, contradiction.
If r<0, then b_ij>0 and the identical argument applied to B transposed gives
proportional columns (the corresponding transposed ratio is positive).

### Positive diagonal case

Positive row scaling preserves (S), nonsingularity and entry signs, so
normalize all b_ii=1. Diagonal inequalities give b_ij b_ji>=1;
opposite off-diagonal entries have the same nonzero sign.
If none is positive, the first alternative holds.
Otherwise choose b_12,b_21>0. If their product equals1, the two row
inequalities yield proportional rows, contradiction. Thus p=b_12 b_21>1.
For k distinct from1,2,

    b_1k <= b_12 b_2k <= p b_1k.

Hence b_1k>=0, and the pair product bound makes it strictly positive.
All b_k1 are also positive. Repeating the same argument with the positive
pair (1,k) makes each row positive. This proves the second alternative.

### Negative diagonal case

Normalize all b_ii=-1 by positive row scaling. Now (S) reads
b_jk+b_ji b_ik<=0 and b_ij b_ji<=1.
Suppose b_12>0 and take k distinct from1,2.
The pivot-k inequality forces b_1k b_k2<0.
If b_1k>0>b_k2, pivot2 implies b_2k<0 and

    b_12 <= -b_1k b_k2 <= b_12 b_2k b_k2 <= b_12.

All are equalities, so b_2k b_k2=1. Since both factors are negative,
the two row inequalities with pivots2,k make row k equal
(-b_k2) times row2, including their pivot entries. Contradiction.
If instead b_1k<0<b_k2, apply this argument to B transposed,
starting at its positive entry (2,1). Thus no entry of B is positive.

## 2. Consequences for the target, with nonsingularity assumed

Write A(i) for deletion of row/column i. If A is nonsingular and all A(i)
are nonsingular with A(i)^-1<=0, then B=A^-1 satisfies (S), by the block
inverse identity. Its diagonal is nonzero because
b_ii=det A(i)/det A.
Thus all det A(i) have one common sign. Also either A^-1 is a Z-matrix
or A^-1 is strictly positive. There is no further inverse-sign alternative.
This does NOT decide det A or exclude the positive-inverse branch.

## 3. Common sign of maximal minors even without nonsingularity

For the literal E0_2 target, all det A(i) have the same nonzero sign,
even if A is singular. Here is the perturbation argument, including the
degenerate case rather than silently assuming invertibility.

Take strictly positive column vectors u,v and A_e=A+e u v^T.
Every principal (n-2)-block of A_e is strictly E: for x>=0 nonzero,
an E0-witness coordinate becomes strictly positive after the rank-one term.
Put C_i=A(i)^-1<=0. Every row and column of C_i is nonzero, hence
C_i u_(i)<0 and v_(i)^T C_i<0. For sufficiently small e>0,

    A_e(i)^-1 =
      C_i - e (C_i u_(i))(v_(i)^T C_i)/(1+e v_(i)^T C_i u_(i)) < 0.

The denominator is positive. Consequently A_e(i) is not E0:
-A_e(i)^-1 times the all-ones vector is positive and is mapped to minus ones.
This also shows the full A_e is not E0 by heredity, so A_e remains E0_2.

If A is singular, rank A=n-1 because a maximal principal block is invertible.
Its adjugate is nonzero. Choose positive u,v with v^T adj(A)u nonzero
(a nonzero bilinear polynomial cannot vanish on the product of open positive
orthants). Then det A_e=e v^T adj(A)u is nonzero. If A was nonsingular,
ordinary continuity suffices. Apply Section2 to small e and pass to the
limit: each det A(i) is already nonzero, so its sign is stable.

This only proves common sign. The separate Wendler determinant-sign
conjecture for almost E0 matrices cannot be silently assumed to make it
negative. No claim that the present target is equivalent to Wendler's is made.

## 4. Exact obstructions to dropping the smaller-block hypothesis

Local inverse signs plus positive diagonal entries of A are insufficient.
Set A=B^-1 in the following two examples; all A(i)^-1<=0.

First, let B have diagonal1, off-diagonal4 within the pairs {1,2},{3,4},
and cross-pair entries2. Then A has diagonal1/9, within-pair entries4/9,
cross-pair entries-2/9, and determinant1/81>0. B is strictly positive.
The principal pair {1,3} sends (1,1) to (-1/9,-1/9).
So A violates the literal smaller-block E0 hypothesis; it is NOT a
counterexample to Conjecture3.12.

Second, split six indices into two groups of3. Let B have diagonal-1,
within-group off-diagonal-9/25 and cross-group entries-3/5.
A has diagonal175/176, within-group225/88, cross-group-375/176,
and determinant -244140625/11534336. Again a cross-group principal pair
sends ones to (-25/22,-25/22), violating smaller-block E0.
This realizes the negative-diagonal inverse branch despite A having positive
diagonal. It does not contradict the target inverse-Z conclusion.

check.py verifies these statements exactly, as well as the sign lemma on
125000 normalized integer 3x3 inputs (144 nonsingular qualifying matrices).
The finite checks are diagnostics, not the all-order proof.
An initial throwaway diagnostic used int(Sympy BooleanTrue), failed before
producing a result, and was corrected to direct Boolean comparisons in the
retained script. No candidate disagreement was hidden.

## Remaining work and limits

The full target still requires nonsingularity, negative determinant, and
exclusion of the strictly positive inverse branch using the actual E0
conditions on smaller blocks. The sign lemma alone supplies none of these.
No full PROOF.md, Lean, manuscript, packet, count or acceptance is warranted.

The actual arXiv source was read from the prior lane's retained body, including
Theorem2.2, Definition3.7, Theorem3.9 and Conjectures3.11–3.12.
Published LMA body remains unread. Fresh primary search exposed Wendler's
Conjecture4.1 and the2023/2024 companion scope; only their indexed theorem/
intro excerpts were read, not their full bodies. An actual open attempt at
the2019 publisher PDF failed405; no retry. The2023 F0 survey actual HTML
sections1–2 was read: its N0/F0 assumptions include a Z condition and do
not silently cover this unrestricted source. Nabben1997 was read only at
abstract level. No new comprehensive registry or novelty clearance is claimed.
