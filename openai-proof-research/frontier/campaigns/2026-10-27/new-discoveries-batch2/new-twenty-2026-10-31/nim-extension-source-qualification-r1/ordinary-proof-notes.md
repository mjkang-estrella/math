# MathDB 328314: independent ordinary analysis

These are zero-credit helper arguments, not a proof or refutation of Fox's conjecture. No seed enumeration, mex DP, witness computation or Lean execution was performed.

## Operational definitions and their limits

Let A=(a_0,...,a_n), 1=a_0<a_1<...<a_n, n>=2, k=a_1, q=a_n. For a finite seed, use all its denominations and allow an unrestricted top digit: starting with residual x, descend i=n,...,0, set d_i=floor(residual/a_i) and replace residual by residual mod a_i. Omit leading zeroes in the displayed representation; represent zero by 0. For an infinite increasing positive sequence, use the finitely many places <=x. Do not append a fictitious next place to a finite seed. This greedy convention is the one used in Fox's proofs and algorithms and is consistent with his printed finite-word example. It is not an independently resolved interpretation of every sentence in Definition 10.

A zend has d_0(x)=0. A position x is 2-volatile when the representation of x+1 has at least two trailing zeroes. Thus define w_A(x)=k if d_0(x+1)=d_1(x+1)=0, and otherwise d_0(x). The successor is positive, so padded lower digits cannot create spurious 2-volatility at zero. The alphabet is {0,...,k}. Volatile zends are a subset of 2-volatile positions; replacing all zends, or only all a_i-1, is incorrect. The finite subtraction set is S_A={1,...,k-1} union {a_i-1:2<=i<=n}; positive, nonempty, with M=q-1. Infinite T(b) uses every i>=2.

## L1: finite greedy period, independently proved

For every x=tq+r, 0<=r<q, division by the top place q leaves residual r. Hence its lower n digits, including d_0 and d_1 because n>=2, equal those of r. If r<q-1, the same argument for x+1=tq+(r+1) shows that the successor's two lower digits equal those of r+1. Therefore volatility and the output symbol agree at x and r. If r=q-1, x+1=(t+1)q has lower n digits zero, and q itself has lower n digits zero. Both positions output k. Consequently w_A(x)=w_A(r) for all x. This proves a period q, not necessarily the least period.

Multiples of q require both cases: w_A(tq)=w_A(0)=0, while w_A(tq-1)=k for t>=1. At q, include the q-place: q is 100...0. Computing q using only the preceding seed prefix, where it may have exactly two displayed digits, changes the volatility test and is unsound. Compute representations through q, inclusive, to construct the q-symbol block.

## L2: corrected block computation; r256 rule refuted

Compute both greedy representations of r and r+1 directly for every 0<=r<q, and apply Definition 16. This requires only divisions. Alternatively use the source's recursive rule, testing for a seed endpoint AT EVERY recursive step: F(t)=t if t<k; F(t)=k if t=a_i-1 for some 2<=i<=n; otherwise F(t)=F(t-a_j), where a_j is the largest defined place <=t. Every recursive call decreases t. At a nonendpoint with j>=2, subtracting a_j leaves the last two digits of both t and t+1 unchanged. With j=1, neither successor can have two trailing zeroes unless it reaches a_2, the excluded endpoint; the last digit is preserved. This proves the recurrence without trusting the summary or applying an infinite-index formula at the undefined a_{n+1}.

The r256 wording tests endpoints only on the original residue and otherwise reduces down to a last digit. That rule is false as written. For A=(1,2,5,13), r=9 is not a seed endpoint, yet r+1=10 has digits 200 and w_A(9)=2. Plain reduction 9 -> 4 -> 2 -> 0 would return 0. The corrected recursive algorithm returns 2 at residual 4. Fox's printed block 0101201012012 independently confirms position 9. This is an error in the proposed helper description, not a counterexample to the conjecture. No new theorem credit.

## L3: finite mex check gives the full infinite premise

Let S be any finite nonempty set of positive integers, M=max S, q>=1, and W:N->N have period q. Suppose for every x with 0<=x<q+M,
W(x)=mex{W(x-s):s in S, s<=x}.
For x>=q+M, x-q>=M, so every s in S is legal at both x and x-q. Periodicity gives W(x-s)=W(x-q-s) and W(x)=W(x-q). Thus the option-value sets agree, and the checked recurrence propagates by strong induction in x. Positivity of S gives uniqueness of the Nim sequence by induction starting at zero. The claimed endpoint q+M-1 inclusive is sound; a q-term prefix alone is insufficient. For A above, M=q-1 and the required range is 0,...,2q-2, using W(x)=block[x mod q]. No assumption that q is a minimal period is needed.

## L4: recurrence growth and exact finite cutoff

For m>=2 and consecutive positive x>y,
z=(m+1)x-(m-1)y satisfies z-x=x+(m-1)(x-y)>0.
Induction shows all appended b terms are strictly increasing positive integers. In particular they are unbounded (an increasing integer sequence has b_j>=j+1). Given B>=0, retain the initial seed and generate only until the first term b_J>B+1. All omitted later terms also exceed B+1, so their subtraction moves b_i-1 exceed B. Legal move sets through B are exactly T(b) intersect [1,B], and induction proves that a finite mex table for that set agrees with the infinite game's values through B. Omitted representation places also exceed B+1, so greedy digits for x and x+1, x<=B, agree with those from the retained list. Equality b_i=B+1 MUST be included: its move B is legal at B and it may change volatility at B. If a seed term already exceeds B+1, later places are irrelevant by seed order and recurrence growth; keeping the entire seed is safe.

For a discrepancy at t<=B, a certificate therefore consists of the exact seed and last-step equality, the full L3 seed-premise checks, b through the cutoff, representations of positions up to t+1, and exact mex values through t. First certify the premise using L1-L3; do not infer it from a finite extension prefix. L4 proves such a discrepancy would refute the GREEDY interpretation at an admissible m>=2. No discrepancy exists in this lane's output.

## Source fidelity objection: Definition 10 versus greedy

Fox calls a representation a minimum digit-sum expansion, then asserts uniqueness and greedy construction for every strictly increasing sequence beginning at 1. These assertions are not true in that unrestricted generality. For (1,2,5,6), greedy 10 is 6+2+2 (three summands), whereas 5+5 uses two. For the source's own example (1,2,5,10,13), 15 has two minimum two-summand representations, 13+2 and 10+5. These are hand-derived definition checks, not searched conjecture witnesses, and are not creditable endpoints. Definition 11 imposes no canonical-coin-system restriction. The source's actual proofs operationally use greedy division. A future formal endpoint must explicitly settle this bridge (or verify the needed stronger property for the chosen seed and infinite extension). Silently defining representation as an arbitrary minimizer is unsafe; silently restricting all seeds to canonical ones cannot prove the full printed statement.

## Full-scope proof ideation

A direct route is to prove mex preservation, not just a word-length identity. For every x, require (E) v(x-s) != v(x) for every legal s in T(b), and (A) for each h<v(x) there exists legal s with v(x-s)=h. Together these characterize mex exactly. The recurrence creates repeated blocks, but carries at b_j-1 change the output symbol; comparisons across two different scales are the obstruction. Under the extra strongly Fergusonian hypothesis, Fox's Theorem 5 reduces much of this to exclusion of differences of nonvolatile zends from T, with the volatile-zend comparison separately controlled. A promising exact missing invariant is that no difference of two extension nonvolatile zends equals b_i-1 or a member of [1,k-1], plus strong Fergusonian structure. The finite seed premise alone has not been shown here to preserve these conditions across the new boundaries. A word recurrence or growth identity does not prove that invariant. No full-scope proof presently survives this gap.
