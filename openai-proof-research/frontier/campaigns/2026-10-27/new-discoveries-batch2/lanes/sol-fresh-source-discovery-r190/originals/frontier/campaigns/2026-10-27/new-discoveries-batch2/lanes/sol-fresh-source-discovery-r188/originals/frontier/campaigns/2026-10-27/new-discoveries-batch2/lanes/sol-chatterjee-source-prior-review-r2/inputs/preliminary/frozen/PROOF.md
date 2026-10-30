# No uniform multiplicative triangle bound for three Chatterjee distances

This is a full ordinary result, pending independent review and source/novelty
clearance. It is not a campaign acceptance or priority claim.

Let xi(X,Y) be the population Chatterjee coefficient, with the conditioning
variable first, as in Chatterjee Theorem 1.1 and Chierichetti–Giacchini–Kumar
equation (1). Set

    d(X,Y)=1-xi(X,Y),
    D_avg(X,Y)=(d(X,Y)+d(Y,X))/2,
    D_min(X,Y)=max(d(X,Y),d(Y,X)).

Here D_min is the source's d'_min, because the minimum is taken on the
correlations. For each of these three functions D and every real K>0 there
exist jointly absolutely continuous real random variables A,B,C, each uniform
on (0,1), such that

    D(A,C)>K (D(A,B)+D(B,C)).

All six directed pair distances in this construction are strictly between zero
and one. Thus this conclusion needs neither discrete marginals nor exact-zero
edges. It refutes the existence of ANY finite universal multiplicative constant
for each of the three distances asked about in source Section 6.

## Construction and conditional laws

Fix an integer n>=2. Let I,J be independent uniform on {0,...,n-1}, and let
U,V,W be independent uniform on (0,1), independent also of I,J. Put

    A=(I+U)/n,
    B=(n I+J+V)/n^2,
    C=(n J+I+W)/n^2.

The joint law has density n^3 on the disjoint union, over i,j, of boxes

    (i/n,(i+1)/n)
      x ((ni+j)/n^2,(ni+j+1)/n^2)
      x ((nj+i)/n^2,(nj+i+1)/n^2),

and zero elsewhere. The total mass is n^2 n^3 n^-5=1. Each marginal is uniform.
Given A one knows I, and learns nothing about J,V,W. Given B one knows I,J;
given C one knows J,I. The remaining within-bin coordinates are independent.
These facts follow directly from the independent product construction, with
bin endpoints a null set.

## Two exact integration facts

For uniform Y, write p_X(t)=P(Y<=t|X). The definition, with denominator
integral_0^1 t(1-t)dt=1/6, gives

    xi(X,Y)=6 integral_0^1 Var(p_X(t)) dt.

Suppose conditioning reveals exactly which of m equal consecutive bins contains
a uniform Y, and Y is conditionally uniform in that bin. Inside that bin its
conditional CDF runs linearly from zero to one; outside it, it is zero or one.
Consequently integral E[p_X(t)(1-p_X(t))]dt=1/(6m): for each bin the
conditional contribution is (1/m) integral_0^1 z(1-z)dz=1/(6m), and the bin
is selected with probability 1/m. Summing the m contributions yields 1/(6m).
The law of total variance therefore gives d(X,Y)=1/m.

For the other fact, let H_i(s)=min(1,max(0,ns-i)), with I uniform on the n
indices. These are the conditional CDFs of a uniform variable given its n-bin
index. Hence E H_I(s)=s, and the preceding calculation yields

    6 integral_0^1 Var(H_I(s))ds=1-1/n.

For t in the j-th coarse C-bin, write t=(j+s)/n. Conditional on I=i,

    P(C<=t|I=i)=j/n+H_i(s)/n.

Its variance over I is Var(H_I(s))/n^2. Integrating over all n coarse bins,
using dt=ds/n, proves

    xi(A,C)=(1-1/n)/n^2.

## All six distances and the full quantifier

Write r=1/n. Applying the consecutive-bin fact with m=n to A|B, A|C and
B|A, and with m=n^2 to B|C and C|B, and the scattered-bin fact to C|A gives

    d(A,B)=d(B,A)=d(C,A)=r,
    d(B,C)=d(C,B)=r^2,
    d(A,C)=1-r^2+r^3.

In particular 1-r^2+r^3>r for n>=2. Thus for directed d and for D_min the
triangle ratio is

    (1-r^2+r^3)/(r+r^2),

whereas for D_avg it is

    (1+r-r^2+r^3)/(2(r+r^2)).

Both exceed n/4. Indeed r<=1/2, the first numerator is at least 3/4 and
the denominator at most 3r/2; for the second ratio its numerator is at least
one and its denominator at most 3r. Given K>0, choose any integer n>=2
with n>4K. This proves the stated theorem for every K. No bounded check
or asymptotic approximation is used to establish this quantifier.

The source leaves 'approximate version' informal. The theorem resolves the
standard uniform multiplicative interpretation for all three distances; it
does not compute optimal universal additive defects. For directed d and
D_min this construction also has additive defect 1-r-2r^2+r^3 tending to one, the
largest possible limit because each distance is at most one. For D_avg the
displayed additive defect tends to 1/2; its optimality is not asserted.
