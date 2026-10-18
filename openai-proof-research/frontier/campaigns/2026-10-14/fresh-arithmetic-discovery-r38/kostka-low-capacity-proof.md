# A uniform low-capacity Kostka bound (author proof, not independently reviewed)

This is work toward the unchanged frozen T205M target. The campaign count is
now 14/20 after the separate T027O acceptance; no count is claimed here.
The quantitative configuration formula and the one-cell perturbation operation
are credited to Kirillov, *Generalization of the Gale–Ryser theorem*,
arXiv:hep-th/9304099v2, Theorem 1.1, Corollary 1.3 and the proof of Theorem 2.1.
The contribution under consideration is the uniform staircase case analysis
and its use in the inherited-multiplicity induction, not that primary formula.

## 1. Statement

Let m≥8, N=m(m+1)/2 and ρ=(m,m−1,…,1). Let L⊢N satisfy

    L_1≤m−1,    C=L_1+L_2+L_3+L_4≤2m,

where missing parts are zero. Then

    K_(Lᵗ,ρ)≥m,

unless L is one of

    (1^N), (2,1^(N−2)), (m−1,1^(N−m+1)),
    (m−1,m−1,1^(N−2m+2)).

The lemma makes no claim of a ≥m bound on those four exceptions. In fact the
maximal configuration has weight 1 on the column and m−1 on each other
listed shape. Exact equality there is not needed below.

## 2. Configurations and estimates used in the proof

Write w=L_1, t=number of parts of L at least two, s=number of parts equal
to one, α=Lᵗ and

    D_j=∑_(i≤j)((ρ)_i−L_i).

For j≥4 and j≤m−1, the average of the first j parts is at most the
average of the first four, hence

    D_j≥ j(m−j+1)/2 ≥ m−1.                         (2.1)

For j≥m, D_j is the area of L strictly below row j and is nonnegative.
If w≤m−2, D_1≥2, D_2≥3 and D_3≥3. If w=m−1, D_1=1,
D_2=m−L_2≥1; also D_3≥m−2 because L has at least four rows and
L_1+L_2+L_3≤2m−1. Thus D_j≥0 for every j, so L is dominated by ρ.
The maximal configuration has ν^(k)=(α_(k+1),α_(k+2),…), and its weight is

    M=∏_(j=1)^t binom(D_j+L_j−L_(j+1), L_j−L_(j+1)).       (2.2)

All factors are positive integers. Its first conjugate partition is
q_j=(ν^(1))'_j=max(L_j−1,0). For 1≤u<v≤t, replace q by

    q'_j=q_j+1_(j=u)−1_(j=v).                           (2.3)

If q' is a partition and D_j≥2 for u≤j<v, this is an admissible new
configuration. Indeed Q_j(ν^(1)) increases by one exactly on [u,v), so
its first vacancy number decreases by two and its second increases by
one there; all other vacancy numbers stay unchanged. On that interval
the maximal first vacancy is exactly D_j. Thus all new vacancies are
nonnegative. Distinct configurations contribute additively to Kirillov's
formula; their weights will be denoted M and W.

For u=1,v=t and t≥3, (2.3) is always a partition. Its first rigging
multiplicity at j=1 is at least one, giving a factor at least
m−w−1. Its first rigging multiplicity at j=t−1 is also at least one,
giving a factor at least D_(t−1)−1. These are different positions.
If t≥m+1 and v_0=L_t≥2, then D_(t−1)=v_0+s.
The second-configuration rigging factors at j<t multiply to at least

    ∏_(j<t)(1+max(L_j−2,0)−max(L_(j+1)−2,0))
       ≥ 1+∑_(j<t)(max(L_j−2,0)−max(L_(j+1)−2,0))
       = w−v_0+1.                                      (2.4)

For every nonzero multiplicity in that product the maximal second vacancy
is zero; the perturbation makes it one. It follows that

    W≥(m−w−1)(v_0+s−1)(w−v_0+1)
      ≥(m−w−1)(w−1),                 if t≥m+1.           (2.5)

The last inequality uses (v_0−1)(w−v_0+1)≥w−1 for 2≤v_0≤w.
For 5≤t≤m, (2.1) instead gives

    W≥(m−w−1)(m−2).                                    (2.6)

These inequalities are used only when the perturbation is admissible.

## 3. Widths 3≤w≤m−2

If t=1, (2.2) is binom(m−1,w−1)≥m. Suppose first 2≤t≤4.
For t=2, put v=L_2≥2. There are further unit rows, since N>2(m−2),
and the j=2 factor of (2.2) is

    binom(2m−2−w,v−1).

Its upper argument is at least m and 1≤v−1≤m−3, so this factor is
at least m. For t=3, if L_3≥3 then D_3≥m−2 and the final drop
L_3−1≥2 give a factor at least binom(m,2)≥m. If L_3=2 then
D_3≥3m−5−2(m−2)=m−1, giving a factor at least m. For t=4,
D_4≥2m−6≥m, so again the final nonzero drop supplies a factor at
least m. The existence of the unit rows in these cases follows from
N>4(m−2), valid for m≥8.

Now let t≥5. On 1≤j<t all D_j≥2: use the first three estimates,
(2.1), and for j≥m the fact that a row of length at least two remains.
Thus the u=1,v=t perturbation is admissible.

If 3≤w≤m−3, (2.6) gives W≥2(m−2)≥m when t≤m, whereas
(2.5) gives W≥2(m−4)≥m when t≥m+1. Here the minimum of
(m−w−1)(w−1) on 3≤w≤m−3 is 2(m−4).

If w=m−2, the condition C≤2m prevents L_1=L_2=L_3=L_4=w.
Consequently there is a positive drop at some j≤3. At that j, D_j≥2,
so (2.2) gives M≥3. Formula (2.6) gives W≥m−2 for t≤m, while
(2.5) gives W≥m−3 for t≥m+1. In either case M+W≥m.

## 4. Width two

Write L=(2^t,1^s), with t≥1. The case t=1 is a listed exception.
For 2≤t≤m, the final nonzero drop in (2.2) gives a factor at least
m: for 2≤t≤m−1,

    D_t=t(m−2)−t(t−1)/2≥m−1,

by concavity and the endpoint values; for t=m, D_t=s=m(m−3)/2≥m−1.
If t>m and s≥m−1, the same factor is at least s+1≥m.

It remains that t>m and 0≤s≤m−2. Here t−2≥m (use 2t+s=N
and m≥8). Since α has two rows, take the single partition

    ν^(1)=(t−2,2),    ν^(k)=∅ for k≥2.

Its size is correct. Its first vacancy is m−4 at j=1, is 2m−9 at
j=2, and on 2≤j≤t−2 is the concave function Q_j(ρ)−2j−4,
whose other endpoint is s. For j≥t−2 it is s. All vacancies are
therefore nonnegative. (The second vacancies are automatically Q_j(ν^(1))≥0.)
There are two distinct occupied lengths, 2 and t−2, so this configuration
has weight

    (2m−8)(s+1)≥m.

## 5. Width m−1

If t=1 we have a listed hook. If t=2, put v=L_2. Formula (2.2) is

    M=(m−v) binom(m−1,v−1).

For 2≤v≤m−2 this is at least 2(m−1)≥m. The remaining v=m−1
is the listed double-row exception.

Suppose t≥3. Put v=L_2 and a=m−v. Since L has at least four rows,
C≤2m gives L_3+L_4≤a+1 and hence L_3≤a. Also v≤m−2:
otherwise the first two rows and L_3≥2,L_4≥1 would exceed capacity.
Thus a≥2. If a<m/2, then d=v−L_3≥m−2a≥1. The first two
factors in (2.2) yield

    M≥a binom(a+d,d)≥a(a+d)≥a(m−a)≥m.

The elementary middle inequality uses a,d≥1.

If a≥m/2, use the perturbation (2.3) with u=2,v=t. It is a partition
because its new second entry is L_2≤m−2=q_1. Its vacancy conditions
hold: D_2=a≥2, D_3≥m−2, (2.1) treats later indices below m,
and a remaining row of length at least two treats j≥m. The first
rigging multiplicity at j=1 has decreased by one, while its vacancy
stays 1, so this factor is a−1. At j=2 the new first rigging
multiplicity is at least one and the vacancy is a−2, giving another
factor at least a−1. These remain valid when t=3, when that multiplicity
increases by two. Therefore

    W≥(a−1)^2≥m,

since a is an integer at least m/2 and m≥8. This finishes the lemma.

## 6. Application to the narrow T205M induction

Let m≥9 and λ⊢N_m have λ_1≤m and top-four capacity C≤2m.
If λ_1≤m−1, the lemma gives K≥m except the column and three
listed shapes, whose maximal weights are m−1. Thus K≥m−1 for
every such λ other than the column.

If λ_1=m, delete the forced full tableau column and put L=(λ_2,λ_3,…),
h=m−1. Then |L|=N_h and L_1+L_2+L_3≤m=h+1. In particular L_1≤h. Since L_4≤(h+1)/3, its top-four capacity is
at most 4(h+1)/3≤2h. If L_1=h, its remaining
second and third entries sum to at most one. Since |L|=N_h>h+1,
there are at least two further positive parts, a contradiction. Thus
L_1≤h−1, and the lemma applies at h≥8. It gives K_(Lᵗ,ρ_h)≥h=m−1,
unless L is one of its four exceptions. The column and width-two hook
correspond exactly to H_m and J_m. The width-(h−1) hook corresponds
to the critical family (m,m−2,1^(N_m−2m+2)), already paid by the
coefficient-two LR calculation. The double-(h−1) exception cannot occur:
its first three parts sum to 2h−1>h+1 for h≥8.

Therefore the low-capacity branch of the sufficient narrow lemma is paid
uniformly for m≥9, using only the established critical-family LR argument.
The finite m=7,8 induction boundary and the high-capacity branch must still
be supplied separately. This document is an author derivation, not an
independent proof or contribution verdict.
