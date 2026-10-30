# Literal refutation of Güday–Sahin Conjecture 1; eligibility not established

Source: published Integers 26 (2026), A5, pp2,11,16, DOI10.5281/zenodo.18154045. Journal and versioned Zenodo-record PDF are byte-identical (SHA256 c03890cdf0f519b945e38b0788b413244c15e74761e27ddb640f9eb06fbebb7c). This proof addresses the explicitly printed sum over tuples subject to the displayed congruences. It does NOT refute the existence of an order-mr constant recurrence with different coefficients.

Set r=4,m=5 and q0=q1=q2=q3=0,q4=1. For n>=5 define the integer sequence by

* n=0 or2 mod4: qn=q(n-4)+q(n-5);
* n=1 mod4: qn=q(n-3)+q(n-5);
* n=3 mod4: qn=q(n-1)+q(n-5).

Thus the only nonzero a(i,j) are a(0,4),a(0,5),a(1,3),a(1,5),a(2,4),a(2,5),a(3,1),a(3,5), all equal1. In particular every highest coefficient a(i,5) is nonzero. As in the source normalization a(i,0)=1.

The printed conjecture would supply coefficients A4,A8,A12,A16,A20, each a signed sum with one term for every tuple (d1,d2,d3,d4) of total d, 0<=dj<=5, satisfying

d(j+1) != d1+j (mod4), j=1,2,3.

Terms involving a zero coefficient vanish. The possible nonzero tuple entries therefore belong respectively to {0,4,5},{0,3,5},{0,4,5},{0,1,5}. For total4 the eligible tuples are exactly

(0,0,4,0), (0,3,0,1), (4,0,0,0).

For total8 they are exactly

(0,3,0,5), (0,3,4,1), (0,3,5,0), (4,0,4,0), (4,3,0,1).

This exhaustiveness can be checked by distinguishing the first entry 0,4,5 and solving for the last three; an entry5 in the first position cannot produce total4; for total8 the last entry must be1 or5, and no allowed second and third entries complete the remaining sum. Every listed product equals1. Hence A4 and A8 are odd integers for EVERY assignment of the unspecified plus/minus signs. The values of the other A's need not be determined.

Repeated substitution in the defining integer recurrence gives, for n=0 through22,

0,0,0,0,1,0,0,0,1,1,0,0,1,1,1,1,1,2,2,3,2,3,4.

In particular q22=4, q18=2, q14=1, q10=q6=q2=0. The proposed recurrence at n=22 would say

4=2*A4+A8.

Its right side is odd and its left side is even. Contradiction. This is an exact finite counterexample proof of the universal conjecture, not an inference from tested cases. It defeats even signs chosen separately for this numerical coefficient matrix and these initial data.

If the statement is read as requiring the recurrence only eventually, the same obstruction still works. Reduce q modulo2. Each one-step map on five successive values is invertible because the coefficient of the oldest value is1. Including the phase modulo4 gives an invertible permutation of a finite state space (or take four steps at a fixed phase). Every state on this orbit therefore recurs, with no transient. The length-23 window above repeats modulo2 at arbitrarily late shifts divisible by4. Each repeated window gives the same parity contradiction, regardless of signs.

## Structural explanation and boundary of the result

A determinant monomial must select distinct column residues (i-di) mod r across ALL rows i. The printed conditions exclude collisions only with the first row. For r=4 they allow e.g. (0,3,0,1), whose selected column residues are (0,2,2,2). This contributes to the printed A4 but cannot occur in a determinant. For r=3 the total-degree congruence forces the remaining two columns to be distinct once both differ from the first; that implication fails at r=4.

Replacing the displayed restriction by the full permutation condition repairs this mechanism by the ordinary determinant expansion. This is a serious eligibility objection: the literal refutation may be a coefficient-formulation correction rather than a substantive new resolution of the intended algebraic problem. No new tool, no novelty PASS, no formal investment, and no credit are claimed. Root must adjudicate this distinction.
