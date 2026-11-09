# Candidate: coefficient positivity of the centered exponential remainder

Strict discovery credit: **0, excluded as a known-result connection**. The elementary recurrence proof is valid, but Skorski2023 Corollary3 already implies the full result via centered Beta(1,r) moments. Costly formalization has been paused. The sharp shift classification is the same old-family connection and is not separately counted.

## Exact primary problem

E. Rodney Canfield, J. William Helton, and Jared A. Hughes, *Uniform convergence of an asymptotic approximation to associated Stirling numbers*, Contributions to Discrete Mathematics **21**(1) (2026), 227–244, Conjecture 3.2. Published primary PDF: <https://cdm.ucalgary.ca/article/download/80046/58851/277478>. Original arXiv:2409.01489v1, Conjecture 3.3.1: <https://arxiv.org/html/2409.01489v1#S3.SS3.SSS1>.

The primary definition is

\[
 B_r(x)=e^x-\sum_{j=0}^{r-1}\frac{x^j}{j!}=\sum_{j\ge r}\frac{x^j}{j!}.
\]

For every integer \(r\ge1\), the conjecture asserts that every Taylor coefficient at zero of \(F_r(x)=e^{-x/(r+1)}B_r(x)\) is nonnegative. MathDB364606 has no posted solution in the retrieved snapshot.

## A coefficient recurrence proves the full conjecture

Write \(c_m=[x^{r+m}]F_r(x)\), and set

\[
 a_m=(r+m)!(r+1)^m c_m\quad(m\ge0).
\]

The coefficients below degree \(r\) vanish. Since \(B_r'=B_r+x^{r-1}/(r-1)!\),

\[
 F_r'=\frac r{r+1}F_r+rac{x^{r-1}}{(r-1)!}e^{-x/(r+1)}.
\]

Coefficient comparison gives

\[
 a_0=1,\qquad a_m=r a_{m-1}+(-1)^m\binom{r+m-1}{m}\quad(m\ge1).
\]

In particular \(a_1=0\). For \(k\ge1\), two recurrence steps yield

\[
\begin{aligned}
 a_{2k+1}
 &=r^2a_{2k-1}+r\binom{r+2k-1}{2k}-\binom{r+2k}{2k+1}\\
 &=r^2a_{2k-1}+\frac{2k(r-1)}{2k+1}\binom{r+2k-1}{2k}.
\end{aligned}
\]

Every added term is nonnegative, so induction gives \(a_{2k+1}\ge0\) for every \(k\ge0\). The even recurrence then gives

\[
 a_{2k}=r a_{2k-1}+\binom{r+2k-1}{2k}>0\quad(k\ge1).
\]

Hence all \(a_m\ge0\); their scaling factors are positive, proving all \(c_m\ge0\) and the exact source conjecture.

When \(r>1\), the paired increment is strictly positive, so the only zero coefficient at or above degree \(r\) is degree \(r+1\). When \(r=1\), all odd \(m\) vanish and all even \(m\) are positive; indeed \(F_1(x)=2\sinh(x/2)\).

## Sharp shift classification, the same outcome

For every integer \(r\ge1\) and every real \(\lambda\), all coefficients of \(e^{-\lambda x}B_r(x)\) are nonnegative **if and only if**

\[
 \lambda\le\frac1{r+1}.
\]

Necessity follows from
\[
 [x^{r+1}]e^{-\lambda x}B_r(x)=\frac{1-\lambda(r+1)}{(r+1)!}.
\]
For sufficiency, write
\[
 e^{-\lambda x}B_r(x)=e^{(1/(r+1)-\lambda)x}F_r(x).
\]
Both factors have nonnegative coefficients under the stated bound; their Cauchy product does too. This gives the optimal shift, rather than a separate counted result.

## Independent computational sanity checks, not proof

Exact rational expansion agrees with the recurrence for all \(1\le r\le9\), \(0\le m\le19\). No numerical or bounded check is used in the argument.

## Preliminary novelty investigation (superseded by exclusion below)

The actual 2026 published source still explicitly lists the complete positivity statement as a conjecture. Preliminary exact-title/formula searches found the source and no resolution. This is evidence only: a full independent prior-art investigation is still required, including possible older general results on centered beta moments and generalized derangement generating functions. No claim that the elementary recurrence or classical coefficient tools themselves are new is made.

## Independent exclusion

Maciej Skorski, *Bernstein-type bounds for beta distribution*, Modern Stochastics: Theory and Applications10(2) (2023),211–228, DOI10.15559/23-VMSTA223, Corollary3: odd central Beta(α,β) moments have the sign of β−α. Primary full text: <https://www.vmsta.org/journal/VMSTA/article/265/text>. Directly inspected2026-10-26. Taylor integral remainder gives F_r(x)=x^r/r! E[exp(x(U−1/(r+1)))], U~Beta(1,r), so the whole source conjecture is an immediate special case of this stronger prior theorem. This precludes genuine-new-discovery credit under the campaign criterion.
