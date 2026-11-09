# Svinin coefficient-shape research: no nominated outcome

Date 2026-10-28. Credit 0. Neither Conjecture 5.1 nor 5.2 is proved here.
No complete Lean endpoint, paper, independent review, or novelty clearance.

## Source and knownness

The exact primary target is Svinin, arXiv:1610.05387v2, Sections 2–7,
especially Conjectures 5.1/5.2. MathDB 334352 is the coefficient-shape
question, Conjecture 5.2. The latest arXiv version is dated 2017-03-01;
the dynamic date in its HTML is not a new revision. The published article
is Experimental Mathematics, DOI 10.1080/10586458.2017.1306815. Its indexed
author-shared typeset body repeats Conjecture 5.2, but no PDF comparison
has been completed in this lane.

The author's 1710.04779v1 Section 3 and 1806.07022v1 Section 3 were read
at their actual primary bodies. They retain the multiple-sum conjecture;
the latter proves the degree-one binomial sum and the n=1 Tuenter/Gandhi
specialization, but leaves the general polynomial representation as an
assumption in Eq.(3.15). These known special cases earn no credit.

The public trureturing Svinin record inspected by root is about the
different 1505.06394v2 difference-equation identity; it is not a resolution
of the present coefficient question. This distinction is not novelty
clearance; no exhaustive prior-art/citing-body audit has been performed.

## Exact finite screen

`check_shape.py` builds the source's C_{r,q}(n) by literal tuple-sum
convolution, then calculates the source binomial combination S_{k,j}(n)
with integer arithmetic. It normalizes using

    t=n(n+1),  g_j(n)=j*binomial(j(n+1)-1,j-1),
    P_k(n,j)=2^(k+1)*S_{k,j}(n)/(t^(k+1)*g_j(n)).

For each fixed n and k, it interpolates a degree-k polynomial in j through
j=0,...,k (zero at j=0, as in the source's stated shape), and checks all
remaining j up to KMAX+1. This is a test of the polynomial hypothesis,
not an unbounded proof of that hypothesis. Leading coefficient k! is checked.

For the proposed coefficient basis, put

    z=t^2/(t+1)^3.

Then the source's law is equivalent to

    p_{k,j}(t)*t^j/(t+1)^j = sum_q alpha_{k,j,q} z^q.

The script fits that polynomial using floor(j/3)+1 distinct integer-n
samples, and verifies the remaining samples exactly. At KMAX=60 there are
n=1,...,23 and j=1,...,61, and all 13,230 fitted alpha coefficients are
strictly positive; five printed anchors are checked explicitly. The
degree-k fit in j also passes throughout these finite grids. Memory is
capped at 1 GiB, CPU at 150 seconds. Recorded runtime is about 11 seconds.

This extends the source's finite evidence k<=11, but **does not prove any
unbounded conjecture or qualify as a discovery outcome**. Interpolation
must not be confused with a theorem valid for every n or j.

## Formal generating-function reduction (ordinary proof)

Let A_n(v)=sum_(q=1)^n exp(qv). If W(z) is the formal solution of

    W=z(1+W)^(n+1), W(0)=0,

then Lagrange–Bürmann inversion gives the exact coefficient identity

    S_{k,j}(n) = j*(2k+1)! * [z^j v^(2k+1)] (-log(1-A_n(v)W(z))).

Indeed Lagrange inversion applied to -log(1-AW) gives
j[z^j](-log(1-AW))=[w^(j-1)] A/(1-Aw)*(1+w)^(j(n+1)).
Expanding the geometric series gives sum_(r=1)^j binomial(j(n+1),j-r)A^r.
The coefficient of v^(2k+1) is exactly the literal tuple moment from the
source. All manipulations are formal in z; the finite coefficient in z
makes the v-coefficient extraction legitimate. This reduction uses a
classical inversion theorem, not a new tool.

The pole W=1/A_n(v) maps under z=W/(1+W)^(n+1) to

    Z_n(v)=A_n(v)^n/(1+A_n(v))^(n+1).

This is even in v. To prove this for every positive integer n, write q=e^v.
The finite geometric sum satisfies A_n(-v)=q^(-n-1)A_n(v) and
1+A_n(-v)=q^(-n)(1+A_n(v)); the powers of q cancel in Z_n.
Equivalently, near v=0,

    Z_n(v)=sinh(v/2)*sinh(nv/2)^n/sinh((n+1)v/2)^(n+1),
    Z_n(0)=n^n/(n+1)^(n+1).

## Exact positive invariant expansion (ordinary proof)

Set t=n(n+1), u=t+1 and

    D_m(n)=(n+1)^(2m+1)-n^(2m+1)-1,  m>=1.

Then, for every m>=1,

    D_m(n)/t = (2m+1) * sum_(q=0)^floor((m-1)/3)
        binomial(m-q,2q+1)/(m-q) * u^(m-1-3q) * t^(2q).

Proof. The three numbers n,1,-n-1 have sum zero, pairwise-product sum
-u, and product -t. Hence their power sums p_r satisfy
p_r=u*p_(r-2)-t*p_(r-3), with p_0=3,p_1=0,p_2=2u.
Equivalently, as formal power series in z,

    -sum_(r>=1) p_r*z^r/r = log(1-u*z^2+t*z^3).

In the logarithm expansion, an odd exponent 2m+1 requires selecting an odd
number 2q+1 of the cubic term and m-1-3q of the quadratic term. Its
coefficient is binomial(m-q,2q+1)*u^(m-1-3q)*t^(2q+1)/(m-q).
Since D_m=-p_(2m+1), the displayed formula follows. Its coefficients are
strictly positive. This uses Newton power sums and the formal logarithm,
classical ingredients, with no novelty claim or independent credit.

This is precisely the invariant basis in the conjecture, with j=m-1.
Moreover the classical expansion of log(sinh(v/2)/(v/2)) gives

    log(Z_n(v)/Z_n(0))
      = -sum_(m>=1) B_(2m)*D_m(n)*v^(2m)/(2m*(2m)!).

The Bernoulli signs and the positive invariant expansion suggest a route
through Lagrange inversion to the conjectured polynomial coefficients.

## Exact remaining gap

Neither evenness of Z_n nor the positive D_m expansion establishes that
the original binomial sums admit a degree-k polynomial in j after the
source normalization. Nor do they identify the alpha coefficients as
positive combinations of those D_m polynomials. A proof needs that
all-order reconstruction bridge and its sign control. The finite fits do
not supply it. No induction, recurrence for the full P_k, or positivity
theorem for every k is asserted.

The argument above should be developed only if that bridge can be proved;
do not promote the 60-row screen or the classical structural helpers as a
substitute for the exact unbounded source question.
