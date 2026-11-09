# W004 disposition — accepted at its stated scope, with corrections

Date: 2026-10-08. Verified new complete factoring improvement: **NONE**.

The parent consumed the complete construction, reciprocal supplement, proposed
screen and independent review. The final independent review is
[W004-independent-review.md](W004-independent-review.md). Its 42 frozen input
records and 58 delivery entries were independently rehashed with no mismatch.
Original reports, submitted copies, assignments and evidence remain unchanged.

Accept the auxiliary-prime/CRT selector, distinct quadratic fields, explicit
rotation and reciprocal identities, localized extraction, the genus calculations
and conservative finite/complete cost bounds, subject to the review's exact
hypotheses and the following qualifications. These are mathematical deductions
at the stated scopes, not new formally checked Lean theorems.

1. In the weaker conic, write A = Z_(N). Valid unit reductions of h,k alone
   do not suffice for arbitrary rational l. The extracted quotient squares to
   R exactly when (s_1-s_2)*l^2 lies in N*A. It suffices that l is in A;
   actual integer l=p*q satisfies this. At each p dividing N the exact
   condition is v_p(s_1-s_2)+2v_p(l) >= v_p(N). Keep the conic reduction
   one-way with this witness condition.
2. Adopt the review's section 8 ordering of fields, signs, epsilon choices,
   rows and coprime parameters as a completion for future executions.
   It was not fully specified by the original report.
3. The reported O(N_0^(3/2)*poly(log N_0)) complete expected bound is an
   upper bound obtained from the paid reference Norm2 and old gcd successes.
   It is slower than the cited trial-division envelope. No useful mixed-packet
   supply bound, speedup or matching lower bound is established.
4. Genus alone proves neither absence of points nor computational hardness.
   A point on the norm quotient still needs the remaining square lifts,
   field-square tests and valid unit reductions.

The new elementary coverage lemma in review section 9 is accepted. If
1 <= M < N <= M(M+1), the coprime rows 1 <= p,q <= M necessarily give a
factor or a modular root for every unit square R. The cyclic gaps between
0,x,...,Mx give a,b <= M with a = +/- x*b mod N. After dividing by
d=gcd(a,b), K=N/gcd(N,d)>1 still divides p^2-R*q^2. A proper row gcd
splits N; a full row gcd forces q to be a unit by coprimality and gives
the root p/q. This argument applies to repeated prime powers and does not
provide the hidden root x to the algorithm.

Consequently **decline the proposed finite screen**. On its entire interval
128 <= N < 512, M=bitlength(N)^2 already meets the lemma's condition.
Elementary row checks guarantee coverage regardless of mixed-target supply.
A budget stop would remain unknown; completed success would not test the
missing mechanism. No test was run, and no implementation or Lean change
is selected by this disposition.

The user's subsequent operating-mode change makes the parent a principal
ideator while T3 children validate. This accepted result motivates two distinct
questions: can choosing a field after constructing a useful rational point
remove the fixed-curve search, and can a direct factor mechanism avoid these
square lifts entirely? These are developed in the new W005 brief; their
claims are provisional and do not inherit acceptance from this disposition.
