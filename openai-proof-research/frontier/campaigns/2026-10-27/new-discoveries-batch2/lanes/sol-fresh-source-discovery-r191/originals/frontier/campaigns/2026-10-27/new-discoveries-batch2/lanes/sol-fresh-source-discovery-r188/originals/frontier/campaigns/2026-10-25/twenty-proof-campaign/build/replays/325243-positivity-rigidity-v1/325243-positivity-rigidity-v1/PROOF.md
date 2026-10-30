# An unconstrained endpoint coefficient

Write S_k for the finite binomial sum in Conjecture11 of [Lóczi and Ketcheson, arXiv1303.6651v1](https://arxiv.org/html/1303.6651v1), also recorded as MathDB325243. Its summation index satisfies m≤min(k,s)≤s. Consequently none of the assumptions depends on p_(s+1). The printed conclusion nevertheless requires

p_(s+1)=p_0 choose(s,s+1)(q̃/q)^(s+1)=0.

This already identifies the defect, but a complete counterexample must also satisfy every premise. Set s=1, q=q̃=1, p_0=p_1=1, and p_2=t, for any nonzero real t. These parameters satisfy the sign restrictions. The three required sums are

S_0=p_0=1,
S_1=−p_0+p_1=0,
S_2=p_0−p_1=0.

All are nonnegative. The conclusion at m=2 would give t=0, a contradiction. Thus t=1 is an explicit witness, with no zero initial coefficient or zero denominator.

## Exact scope

The source itself prints p_m for 0≤m≤s+1, sums only through min(k,s), and quantifies its conclusion through s+1. This is not merely a discrepancy in MathDB's transcription. It is plausibly an endpoint typo: in the surrounding application p_m arises from a polynomial of degree at most s, where p_(s+1)=0 already. This observation is only an interpretation of the surrounding application. We do not assert that the intended corrected statement is false, and do not claim a substantive resolution of that corrected problem.

## Formal coverage

`sourceSum`, `Hypotheses`, and `Conclusion` express all sums, side conditions and printed conclusions, using a total natural-indexed sequence whose values beyond s+1 are irrelevant. `sum_ignores_endpoint` proves invariance under changing p_(s+1) for every s,k,q,q̃. `candidate_hypotheses` checks every required k for the nonzero-initial-coefficient family. `candidate_not_conclusion` rejects the printed conclusion for each t≠0. `printed_conjecture_false` refutes the entire universal statement. The counterexample is not just a numerical check or an isolated failure of a supporting identity.
