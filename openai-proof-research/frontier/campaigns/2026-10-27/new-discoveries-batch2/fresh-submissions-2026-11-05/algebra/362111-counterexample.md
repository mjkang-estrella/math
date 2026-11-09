# MathDB 362111: n = 170 refutes the Dolfi–Hafezieh–Spiga distinct-prime-divisor conjecture

## Statement under test (literal)

**Primary source.** S. Dolfi, R. Hafezieh, P. Spiga, *On the structure of the character degree graphs
having diameter three*. Published as J. Algebra **685** (2026) 337–360, Conjecture 4.3. Preprint:
arXiv:2402.19335v1 (29 Feb 2024), Conjecture `conj:1`, line 702 of the e-print TeX.

> Let $n$ be divisible by $\ell$ distinct primes and assume $\gcd(2^n-1,n)=1$. If $\ell\ge 3$, then
> $2^n-1$ is divisible by at least $2^\ell$ distinct primes.

The published text is the same as the arXiv text. The paragraph before it works with an arbitrary
positive integer $n$: "let $n$ be a positive integer". It notes that their Lemma 4.2 gives only
$2^{|\pi(n)|}-1$ when $p=2$, and says: "Except when $|\pi(n)|\le 2$, we have no examples where $2^n-1$ has
exactly $2^{|\pi(n)|}-1$ distinct prime divisors." The published version adds that the conjecture "is
compatible with the results and the tables" of Brillhart et al., *Factorizations of $b^n\pm1$*.

MathDB record 362111 (live, 2026-11-08T02:29Z) gives the same statement for every positive integer $n$.
Its status is `open`, with no solutions, model attempts, comments or replies.

## Theorem

For $n=170$, the hypotheses hold with $\ell=3$, but $2^{170}-1$ has exactly $7=2^3-1$ distinct prime
divisors. So the conjecture is false. The authors' lower bound $2^\ell-1$ is attained for $\ell=3$.

## Proof

1. **$\ell=3$.** $170=2\cdot5\cdot17$.

2. **$\gcd(2^{170}-1,170)=1$.** $2^{170}-1$ is odd. Modulo 5, $2^4\equiv1$ and $170\equiv2\pmod 4$, so
   $2^{170}\equiv4\not\equiv1$. Modulo 17, $2^8\equiv1$ and $170\equiv2\pmod 8$, so
   $2^{170}\equiv4\not\equiv1$.

3. **Factorization.** Write $2^{170}-1=(2^{85}-1)(2^{85}+1)$. Then
   $2^{85}-1=\Phi_1(2)\Phi_5(2)\Phi_{17}(2)\Phi_{85}(2)$ and
   $2^{85}+1=\Phi_2(2)\Phi_{10}(2)\Phi_{34}(2)\Phi_{170}(2)$. The values are
   - $\Phi_1(2)=1$, $\Phi_2(2)=3$, $\Phi_5(2)=31$, $\Phi_{10}(2)=11$,
   - $\Phi_{17}(2)=131071$, $\Phi_{34}(2)=(2^{17}+1)/3=43691$,
   - $\Phi_{85}(2)=(2^{85}-1)/(31\cdot131071)=9520972806333758431$,
   - $\Phi_{170}(2)=(2^{85}+1)/(3\cdot11\cdot43691)=26831423036065352611$.

   Exact integer multiplication confirms
   $$2^{170}-1=3\cdot11\cdot31\cdot43691\cdot131071\cdot9520972806333758431\cdot26831423036065352611 .$$

4. **Every factor is prime.**
   - $3, 11, 31, 43691, 131071$: trial division.
   - $m_1=9520972806333758431$. We have
     $m_1-1=2\cdot3\cdot5\cdot17\cdot257\cdot27953\cdot2598660833$, and every factor is prime by trial division.
     Pocklington–Lehmer applies with $F=m_1-1$ fully factored. The witnesses
     $a=3,5,2,2,3,3,3$ for the primes $q=2,3,5,17,257,27953,2598660833$ satisfy $a^{m_1-1}\equiv1$ and
     $\gcd(a^{(m_1-1)/q}-1,m_1)=1$.
   - $m_2=26831423036065352611$. We have $m_2-1=2\cdot3\cdot5\cdot17\cdot257\cdot204710635813423$, and the last
     factor is prime by trial division up to $1.44\times10^7$. The Pocklington–Lehmer witnesses are
     $a=2,3,2,2,3,3$.
   - Separate check: deterministic Miller–Rabin with the first 13 prime bases, which is valid below
     $3.317\times10^{24}$ (Sorenson–Webster), also declares both prime.
   - External check: FactorDB entry `2^170-1` has status `FF` (fully factored) with exactly these seven
     factors (queried 2026-11-08T02:41Z).

5. **Counting.** There are exactly 7 distinct prime divisors. The order of 2 modulo each one is
   2, 10, 5, 34, 17, 85 and 170 respectively, one for each divisor $d>1$ of 170. This is consistent with
   Lemma 4.2. Since $7<8=2^\ell$, the conclusion of the conjecture fails. $\square$

## Remarks

- **Minimality and uniqueness in range.** We scanned every $n\le 10^5$ with at least three distinct prime
  factors and $\gcd(2^n-1,n)=1$. For each one we checked whether every $\Phi_d(2)$ ($d\mid n$, $d>1$) can be
  a prime power. The only $n$ that passes is $170$, so it is the smallest counterexample. A failing $n$ is
  backed by a Miller–Rabin compositeness witness, which is rigorous. One caveat: the perfect-prime-power
  test is skipped for values with 1000 or more bits, so a counterexample whose $\Phi_d(2)$ is a huge proper
  prime power could be missed. Files: `scan_ell3.py`, `scan_ell3_100000.txt`.
- **Why the even case allows this.** Under the gcd condition, every prime divisor of $\Phi_d(2)$ is
  primitive. A counterexample with $\ell=3$ therefore needs all seven $\Phi_d(2)$ to be prime powers. For
  $n=2pq$ this means: $p$ and $q$ are both Mersenne and Wagstaff exponents, and $\Phi_{pq}(2)$ and
  $\Phi_{2pq}(2)$ are prime. $p=5$, $q=17$ satisfies this.
- **Scope.** The literal conjecture, as published in J. Algebra and recorded on MathDB, covers all $n$,
  with no parity restriction. The application the authors have in mind is a putative 11-vertex
  diameter-three graph, which would force an odd $n=qt_1t_2$. There they would need every $\lambda_d(2)$ to
  be a prime power for an odd product of three primes. That odd case is **not** settled here. No odd
  counterexample exists with $n\le10^5$. A targeted screen over products of three Mersenne exponents is
  recorded in `odd_pairs_*.txt`.
