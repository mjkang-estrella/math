# I205: short Egyptian fractions with a polynomial denominator budget

2026-10-12. **UNRESOLVED — NO SUBSTANTIAL NOMINATION.** Eight accepted findings remain eight. No ninth finding is claimed. Two independent acceptance reviews remain necessary for any future nomination; none was launched here.

The exact target is the existence of absolute A,C,b0 such that every integer b>=b0 and every 1<=a<b has a sum of at most C loglog b distinct positive unit fractions with all denominators <=b^A. Its truth and worldwide open status are not assumed. The stipulated results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were accepted without an upstream audit.

The full [analytic record](../experiments/i205_bounded_egyptian/analytic-attempt.md) contains proofs and counterexample checks. [Reading and failures](../experiments/i205_bounded_egyptian/reading-and-failures.md), [input hashes](../experiments/i205_bounded_egyptian/input-authentication.json), and [primary literature](../sources/i205_bounded_egyptian/literature.md) are separate. Partial records were written before the detailed attempts and updated in place.

## Route A: replace the emitted expansion

I204's backward-counting result only obstructs short polynomial-cost paths in the literal source recursion. It does not obstruct replacing the emitted sum globally. This follow-up tried to absorb a very small tail into earlier terms and to make duplicate removal quantitative.

A positive block of value below 1/B cannot by itself be replaced using denominators <=B. Thus retaining the entire earlier prefix and only cleaning up such a tail cannot work. Borrowing mass by replacing 1/n with 1/(n+1) creates a positive correction, but the resulting correction can still carry the tail's large denominator. No uniform short bounded completion of that correction was obtained.

There is a useful proved technical reduction: **the target with repetitions allowed implies the distinct target**, with only absolute constant-factor losses. More precisely, if the multiset version has constants A>=1,C, then the distinct version can use exponent 12A+3 and length coefficient 4C+3, after increasing the threshold. A short greedy prefix makes a tail small; a multiplier K=2^{O(loglog b)} supplies at least four times as many divisors as tail terms. Apply the hypothesized multiset theorem to K times the tail, scale back, and split each reciprocal over a different proper divisor of K. Each split avoids the earlier choices and costs at most a square of the original maximum denominator. Positivity automatically separates the tail from the prefix.

This is a full conditional implication, not a proof of the multiset hypothesis. Its ingredients are the already-paid greedy preparation and divisor-indexed splitting. It removes a technical obstacle but does not meet the substantial-contribution gate. In particular it does not turn the source's superpolynomial raw denominators into polynomial ones.

## Route B: independent rational denominators and changing lcm

The source's actual rational-divisor supply was read in full. It already allows independent positive t_i in s=sum e_i/t_i, e_i|K, and its grouping emits denominators (q/d)(K/e_i)t_i. The actual t_i are bounded by 5K, but K=m^{O(loglog m)}. A polynomial-size common K with bounded block length and polynomial t_i would close a concrete sufficient construction, as the analytic record verifies with all factors included. Such a supply was not proved.

One cannot simply replace the source's K by a polynomial-sized K while retaining its three integer prime blocks. For fixed h, the positive integers (e_1+...+e_j)/t with j<=h and e_i|K number only K^{o(1)}: each integer output divides the corresponding numerator, and there are only tau(K)^h numerator lists. A fixed number of such integer blocks cannot represent every integer through Y when K<=Y^D. This obstruction does **not** cover genuinely independent rational summands whose intermediate sums are nonintegral, or a different K for each target.

The other attempted construction removes prime factors using short sums of modular reciprocals and permits the lcm to change. Its exact cancellation identity and positivity conditions are recorded. The [primary Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte paper](https://www.its.caltech.edu/~dconlon/egyptian.pdf), read through all nine pages, provides a genuine prime-power absorption construction with small individual denominators. Its fixed-parameter reciprocal supply uses up to q^{delta/2} terms, and its total mass control does not imply the required double-logarithmic length.

A proved counting barrier sharpens this attempt: for fixed epsilon>0, all residue sums of h reciprocal divisors of any M<=p^{1-epsilon}, allowing M to depend on the residue, cover only p^{1-epsilon+o(1)} classes for fixed h. Even h<=epsilon loglog p/6 covers at most p^{1-epsilon/2} classes for large p using the explicit elementary divisor bound in the record. Thus a uniform prime-removal step that contracts the next lcm by a fixed power cannot use a bounded number of terms. This is **not an obstruction to the actual target**, which allows a much larger lcm than its individual denominators.

The unresolved input is either an exact supply using nonintegral rational blocks with a polynomial size budget, or an absorption argument with an amortized O(loglog b) total length over all introduced prime powers. Congruence solvability, a bound on the largest new prime, and positivity are separate requirements. None was conflated with the others.

## Literature, validation and scope

Primary literature was checked before investment and again for the final verdict. The [Tenenbaum–Yokota theorem](https://tenenb.perso.math.cnrs.fr/PPP/Egyptian.pdf) supplies a simultaneous near-linear denominator cap with order log b/loglog b terms; it is not the target. Its seven pages were read in place, preserving the prior OCR limitations. Martin's dense representations, Martin–Shi's finite-denominator algorithm, and Liu–Sawhney were checked at primary abstract/metadata level only. No unread statement or secondary search result supplies a theorem here. The bounded search did not settle the target's worldwide status.

The analytic checks cover exact equality, positivity, distinctness, unreduced inputs, order of choices, the t_i factors, the full lcm, and cumulative length. No numerical evidence is used. The surviving deductions are technical constructions and method limitations, not a substantial nomination. Both major routes remain unresolved beyond their explicitly restricted failures.

Only the assigned I205 files and one fully read source copy were written. No child agents, research code, numerical scans, tests, snapshots, seals, historical replay, shared/ancestor edits, staging, commits or publication were used. I31 and other live branches were outside scope. Detached output hashes accompany the handoff; the authentication record does not hash itself.
