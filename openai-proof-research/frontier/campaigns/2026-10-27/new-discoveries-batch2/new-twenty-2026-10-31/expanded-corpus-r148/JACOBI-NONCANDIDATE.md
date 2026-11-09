# Jacobi route: excluded by the August 2026 proof

This is retained reasoning, not a discovery nomination or a Lean certificate.
The later, statistic-specific literature search located Lin, Wen and Yan,
*Bijective proofs of several conjectures on Jacobi permutations*,
arXiv:2608.11771v1 (12 August 2026). Its Conjecture 1.2 is exactly the
reserved Conjecture 9.4. Section 2 supplies the bijection and concludes the
full formula. The primary PDF, current abstract and dated hash receipts are
in sources/jacobi-proof.*. The abstract/title search used earlier did not
locate this paper; that earlier non-finding is superseded.

The lane's separate elementary count route also closes at the ordinary
mathematical level, using the source's recursive definition and its
Theorem 2.7. It receives no novelty credit and was not formalized.

Let D_n(a,b) count Jacobi permutations ending in a,b, and let E_n,k count
up-down permutations of length n starting at k (zero outside the legal
range). Write e_n for the Euler number, with e_0 = 1. A Jacobi permutation
must end in a descent: otherwise the penultimate letter has an odd
rightward larger block of length one. Thus only a > b matters.
For b = 1, the minimum-letter decomposition has empty right part, so
D_n(a,1) = E_(n-1,a-1) by the source's last-letter theorem.
The n = 2 case is the unique permutation 21.

For b > 1, write the permutation as alpha,1,beta, with beta of even size
r >= 2. If a and b have ranks x > y within beta, the label choices are

    binom(b-2,y-1) binom(a-b-1,x-y-1) binom(n-a,r-x).

There are e_(n-1-r) choices for alpha. Inductively the beta count is
E_(r-1,x-y). Put g = a-b, t = x-y-1, and u = y-1. Vandermonde summation
in u gives the exact recurrence

    D_n(a,b) = sum over even 2 <= r <= n-1 of e_(n-1-r)
        * sum over t of binom(g-1,t) binom(n-g-2,r-t-2) E_(r-1,t+1).

All binomial coefficients outside their ordinary nonnegative range are
zero. The right side is E_(n-1,g): split an up-down permutation of
length n-1 starting at g at its maximum n-1. Since g <= n-2, this maximum
occurs at an even position r >= 2. Its prefix has length r-1 and starts
with g; choosing t smaller labels and r-t-2 larger labels gives the two
binomial factors and the prefix count E_(r-1,t+1). The suffix contributes
e_(n-1-r). This proves D_n(a,b) = E_(n-1,a-b) by induction, hence the
reserved cpen/last identity after setting a = n+1-i and b = k.

The exact recurrence was checked through n = 28; literal Jacobi and
alternating permutations were independently enumerated through n = 9.
Those checks are corroboration, not the proof or a formal certificate.
Even absent the prior publication, this route would require root review
of whether it is merely a routine bridge from the source's own recursion,
Theorem 2.7, and classical Vandermonde summation.
