# A counterexample to published Problem 5.6

Source: S. Aivazidis, M. Loukaki and T. W. Müller, *On the common transversal probability*, Journal of Group Theory 27 (2024), 1233–1285, DOI 10.1515/jgth-2024-0030. Problem 5.6 is printed on p.1281. The retained published PDF and its p.1281 rendering were inspected. Preprint numbering is Problem 12.6; use the published numbering here.

The question asks whether, for distinct integers greater than one in each list, equality of the products of f(t)=Gamma(t+1)/t^t forces equal list lengths and equality up to rearrangement. We give two disjoint lists, so the witness also meets the stronger interpretation that all integers across both lists must be distinct.

Let

    A = {3,5,6,7,8,14,16,20,36},
    B = {4,10,12,15,18,21,32}.

Then

    product_{a in A} a!/a^a = product_{b in B} b!/b^b.

Here is a complete finite arithmetic proof of the equality. For a prime p and positive rational r let v_p(r) be its exponent in the prime factorization. Counting multiples of p, then p^2, etc. among 1,...,t gives

    v_p(t!/t^t) = sum_{j>=1} floor(t/p^j) - t v_p(t).

All terms vanish for p>36. Applying this displayed formula to the two explicit finite lists gives:

| p | sum over A | sum over B |
|---|---:|---:|
| 2 | -123 | -123 |
| 3 | -37 | -37 |
| 5 | -4 | -4 |
| 7 | -8 | -8 |
| 11 | 6 | 6 |
| 13 | 5 | 5 |
| 17 | 3 | 3 |
| 19 | 2 | 2 |
| 23 | 1 | 1 |
| 29 | 1 | 1 |
| 31 | 1 | 1 |

Thus both products are exactly

    11^6 13^5 17^3 19^2 23 29 31 / (2^123 3^37 5^4 7^8).

Unique factorization proves equality. Since Gamma(t+1)=t! for positive integers, these are the literal source products. But |A|=9 and |B|=7, contradicting the proposed conclusion n=k. This refutes the universal source assertion in full. No unbounded search, floating-point inference, group realization, minimality claim or extension of domain is required.

`verify_exact.py` independently verifies the identity by rational arithmetic, 240-digit integer cross multiplication, the above prime totals, and all 176 individual valuation entries. The verifier uses only the Python standard library. Its results are an independently executable check of the finite arithmetic, not a substitute for the argument above.

This does not contradict source Theorem 4.6 (pp.1263–1265): that theorem requires one side to consist entirely of distinct primes, and neither side here does. Its actual proof uses that largest-prime-side hypothesis to obtain a strict majorization contradiction. Replacing its prime list by either of our composite-containing lists removes that step. Its proof body does not supply this collision.

Ordinary arithmetic/source-scope self-check PASS. Substantive assessment: this is a refutation of the exact published arithmetic injectivity claim, not a helper, instance of an already established source theorem, or wording correction. Independent substantive review and historical/current-public-priority clearance remain pending. No discovery credit is claimed.
