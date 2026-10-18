# An attempted oddification route and its exact obstruction

Before assembling the final construction, I attempted to apply source025 to obtain a short unrestricted expansion and then replace its even denominators by odd ones at bounded multiplicative cost. That route fails in a concrete family.

For every odd b>1 put x_b=(b+1)/(2b)=1/2+1/(2b). It has an unrestricted two-term distinct expansion, and in lowest terms its denominator is odd. Nevertheless its minimum length using odd denominators tends to infinity.

Here is a quantitative proof, allowing repetitions and thus also covering the distinct case. Suppose x_b=sum_{i=1}^k1/d_i, with odd d_i in nondecreasing order. Let j be the first index for which the partial sum exceeds1/2. No partial sum equals1/2: after clearing its odd common denominator its numerator cannot equal half an odd integer. Before index i<=j, the remaining gap to1/2 is therefore at least1/(2P_{i-1}), P_{i-1}=product_{h<i}d_h. The remaining k-i+1 reciprocals exceed that gap, and each is at most1/d_i. Thus d_i<=2kP_{i-1}, and induction yields P_i<=(2k)^(2^i-1).

At the crossing, the positive excess of the j-th partial sum above1/2 is at least1/(2P_j). It is at most the final excess1/(2b). Hence

    b<=P_j<=(2k)^(2^k-1).

Thus no function of the unrestricted length alone can bound the odd-denominator length; in particular there is no universal constant-factor oddification. The estimate is an elementary denominator-product obstruction, not a counterexample to T025O54, whose logarithmic double-logarithmic budget accommodates it. The final proof instead constructs odd denominators from the start and separates the two merged lists by a growing marker prime.

A second exploratory approach used odd-divisor reservoirs at the terminal stage. It was replaced before proof assembly by the explicit base5 templates in constrained-descent.md, which provide distinctness by different 5-adic valuations without invoking a general odd practical-number theorem. No numerical subset-sum experiment is used in the final proof.
