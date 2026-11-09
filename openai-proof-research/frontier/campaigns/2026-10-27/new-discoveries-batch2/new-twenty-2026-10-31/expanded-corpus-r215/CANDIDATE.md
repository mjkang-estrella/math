# Held ordinary-proof lead: MathDB 334353

Status: ordinary full-scope proof offered for review, **not a qualified campaign solution**. There is no literal Lean endpoint, no independent review, and no demonstrated literature novelty. Do not count it. A historical same-family HOLD was recovered in `../lanes/root-svinin-shape-r11/PROOF.md` and `../lanes/pi-svinin-multiple-sum-preliminary-review-r1/review.md`: their Conjecture 3.1 argument explicitly does not prove this reserved Conjecture 6.1, but it identifies an unread closest same-author journal body and an unresolved routine-corollary objection. These gates remain binding. In particular, the argument is short enough that the campaign's routine-bridge exclusion needs an explicit ruling. No acceptance is asserted.

## Exact target and source fidelity

Svinin, arXiv:1610.05387v2, Sections 2, 3 and Conjecture 6.1, defines, for integers k ≥ 0, j ≥ 1, n ≥ 1,

\[
s_{k,l}(n)=\sum_{a_1,\ldots,a_l=1}^n(a_1+\cdots+a_l)^{2k+1},\qquad
S_{k,j}(n)=\sum_{q=0}^{j-1}\binom{j(n+1)}q s_{k,j-q}(n).
\]

The target is the existence of F in Q[t] such that

\[
S_{k,j}(n)=\left(\prod_{r=1}^{j-1}(jn+r)\right)F(n(n+1))
\]

for all positive integers n. This proof does not assume the source's separate Conjecture 3.1 equating S with a different multiple sum.

## Ordinary proof

Put m=2k+1. Let

\[
A_N(x)=\frac{e^{(N+1)x}-e^x}{e^x-1}\in\mathbb Q[N][[x]].
\]

The quotient exists formally: numerator and denominator are divisible by x, and (e^x-1)/x has constant coefficient 1. The coefficient of x^h is a polynomial in N of degree at most h+1. For positive integral N=n this is the geometric sum \(\sum_{a=1}^n e^{ax}\).

Define the polynomial

\[
P(N)=m![x^m z^j]\frac{(1+z)^{j(N+1)}}{1-zA_N(x)}.
\]

Here the generalized binomial expansion is in z. Its coefficient z^j is a finite sum. Its term containing A^0 has zero x^m coefficient because m>0. Thus P agrees with S on positive integers, and has degree at most j+m: the term with binomial index q has degree at most q+(j-q)+m.

First show P(-N-1)=(-1)^(j+m)P(N). Directly,

\[
A_{-N-1}(x)=-1-A_N(-x).
\]

Use the coefficient-change identity

\[
[z^j]f(z)=(-1)^j[w^j](1+w)^{j-1}f\!\left(\frac{-w}{1+w}\right).
\]

It is enough to check f=z^h for h≤j; for h<j the transformed polynomial has degree j-1, and for h=j its coefficient is (-1)^j. Apply it to

\[
f(z)=\frac{(1+z)^{-jN}}{1+z+zA_N(-x)}.
\]

The transformed expression, including the factor (1+w)^(j-1), is exactly

\[
\frac{(1+w)^{j(N+1)}}{1-wA_N(-x)}.
\]

Taking x^m contributes (-1)^m. This proves the claimed reflection identity.

Next fix 1≤r≤j-1 and specialize N=-r/j. Since j(N+1)=j-r, ordinary polynomial expansion in z gives

\[
[z^j]\frac{(1+z)^{j-r}}{1-zA_N(x)}
=A_N(x)^r(1+A_N(x))^{j-r}.
\]

The identities

\[
A_N(-x)=e^{-(N+1)x}A_N(x),\qquad
1+A_N(-x)=e^{-Nx}(1+A_N(x))
\]

follow directly from the geometric expression. Consequently the preceding product is invariant under x↦-x at N=-r/j: its multiplier is exp(-(jN+r)x)=1. Its coefficient of the odd degree m is zero. Therefore P(-r/j)=0 for every r in this range.

The distinct linear factors jN+r divide P, hence Q_j(N)=∏_(r=1)^(j-1)(jN+r) divides P in Q[N]. Write R=P/Q_j. Since Q_j(-N-1)=(-1)^(j-1)Q_j(N) and m is odd, the reflection identity yields R(-N-1)=R(N). Set U=N+1/2; R(U-1/2) is even, so it is a polynomial in U². Since U²=N(N+1)+1/4, R belongs to Q[N(N+1)]. This proves the target, with degree F≤k+1. The empty product j=1 is included.

## Checks and limitations

`scripts/polynomial.py` checks the source definition by exact rational interpolation and decomposition in powers of n(n+1); its output records the actual completed range. This is diagnostic, not formal proof. The abstract coefficient-change identity above can also be checked directly on monomials, as explained in the proof.

The source's v1 and v2 were fetched and the defining sections and target compared. Svinin's 2018 companion arXiv:1806.07022, Sections 3.1–3.3, was read: it defines the same binomial sums and proves the m=1 formula (Proposition 3.6), but the inspected body does not state the general reflection/root argument above. The 2019 Russian Mathematics journal body was also fetched (`svinin-journal-body.pdf`, SHA-256 in its receipt); Section 2.3, Proposition 5, proves m=1 and then restates the general expression as a supposition from the earlier work. Its text extraction has Cyrillic encoding defects, so the mathematical formulas and labelled section were used for the bounded comparison. Literature and current public-registry screens are bounded non-findings, not novelty clearance. The similarly named Omega Svinin discrete-polynomial project concerns a different source and identity.

## Missing acceptance requirements

The closest unresolved prior body from the historical HOLD is **Generalization of the Power Sum Arising in the Theory of Integrable Hierarchies**, J. Math. Sci. 239(2):159–171 (2019), DOI 10.1007/s10958-019-04299-6, translated from Problemy Matematicheskogo Analiza 96 (2019), 43–53. It is different from the Russian Mathematics paper fetched here. Its full body has not been read in this pass; the earlier access failures are preserved in the historical review. Do not infer clearance from the accessible companion.

The literal Lean endpoint must define the source's finite sums, establish their polynomial extension and the exponential coefficient representation, prove the coefficient change and root/reflection identities, and derive the Q[t] factorization for every k,j. None of these bridges is claimed formalized. The fresh strict replay, leanchecker, axiom audit, significance ruling, independent review and same-object journal/citing-work clearance remain outstanding. A helper invariant or bounded diagnostic must not be substituted for this endpoint.
