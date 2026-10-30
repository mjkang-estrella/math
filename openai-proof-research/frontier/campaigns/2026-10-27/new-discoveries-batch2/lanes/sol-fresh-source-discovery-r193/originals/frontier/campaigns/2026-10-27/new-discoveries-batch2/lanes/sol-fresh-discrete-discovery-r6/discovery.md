# Research outcome: no qualifying completed discovery

Solo lane. No discovery nomination, acceptance request, Lean work, count change,
shared edit, git operation or external mutation. Full ordinary results rediscovered
below were excluded when actual earlier proof bodies were found. They are not new
results. The final selected question remains unresolved.

## Final target: full ordinary denominator log-concavity

Ballantine–Beck–Feigon–Maurischat, *Reciprocals of subsum polynomials*,
arXiv:2605.10512v1, Conjecture 4; published open-access version,
Ramanujan Journal 70, article 46 (2026), DOI 10.1007/s11139-026-01419-0,
same Conjecture 4. Actual statements and definitions were read in both bodies.

For every integer n>=1 let

    den*(n,x) = product_{a=1}^n (1+x^a)^floor(n/a),
    h_lambda(x) = den*(n,x)/product_{a in lambda}(1+x^a),
    G(n,x) = gcd_{lambda partition n} h_lambda(x),
    D_n(x) = den*(n,x)/G(n,x).

The exact question is whether the coefficient sequence of D_n is log-concave
for every n other than 3,5,6,7. Log-concavity means a_j^2 >= a_{j-1}a_{j+1}
at every internal index. The four exceptions are also part of the claim.
No alteration of domain, numerator normalization or sequence convention is proposed.

### Mathematical attack

The source's cyclotomic valuation calculation gives

    D_n(x) = product_{d=1}^n Phi_{2d}(x)^floor(n/d).

This follows independently because Phi_{2d} occurs in 1+x^a precisely when
a is an odd multiple of d. Across partition denominators its maximal exponent
is floor(n/d), attained by floor(n/d) copies of d and a partition of n mod d.
Thus taking the gcd of the common-numerator summands leaves exactly that
maximum exponent in D_n. This calculation does not use coprimality of the sum.

Writing n=2^v b with b odd gives the useful literal recurrence

    D_n/D_{n-1} = product_{d|n} Phi_{2d}(x)
                = (1-x^(2n))/(1-x^b)
                = sum_{j=0}^{2^(v+1)-1} x^(bj).

To verify the middle identity, write d=2^a e with e|b and 0<=a<=v.
For each fixed a the product over e is x^(2^a b)+1, and the product over a
is the displayed geometric quotient. Hence D_n has positive integer
coefficients with no internal zeros and is palindromic. These facts are
already source-level consequences, not discoveries.

I attacked the full log-concavity question through this product recurrence.
It gives a linear-memory, exact integer update. If D is the previous
coefficient array and E the new one, with L=2^(v+1), then

    E_j = E_(j-b) + D_j - D_(j-Lb),

with out-of-range indices zero. The complete computed range 1<=n<=500
has precisely the listed four exceptions. At n=500 the polynomial degree
is 167104. This is bounded exact evidence, not a proof of the conjecture.
A separate cyclotomic multiplication check through n=50 cross-checks the
recurrence, degrees and all coefficient inequalities.

### Strongest objection and precise missing argument

The product recurrence does NOT inductively preserve log-concavity in general.
Sparse uniform factors have internal zeros; the usual convolution closure
for log-concave sequences does not apply. For instance the log-concave
polynomial 1+x multiplied by 1+x^3 gives coefficients (1,1,0,1,1), which
are not log-concave. Even a strictly positive log-concave input is insufficient:
(1+x)^2(1+x^3) has coefficients (1,2,1,1,2,1), violating the inequality at
index 2. An induction must use additional quantified properties of these
specific D_n, not generic log-concavity, symmetry, or unimodality.

No such invariant or injection was established. Central-limit heuristics would
also leave the endpoints and a uniform transition regime uncontrolled.
The strongest falsifier of any proposed result is one exact negative
coefficient determinant a_j^2-a_{j-1}a_{j+1} at an unexcluded n.
The present checks do not preclude this above n=500.

## Early nonduplicative screening and exclusions

The earlier campaign rules, ledger, prior context, q-Hoggatt and An–Djokovic
rejections, and the recent percolation and Krasniqi closeouts were read first.
No forbidden active or accepted family was pursued.

1. **Gawron–Ulas factorial sign Conjecture 4.4**, 2202.05221v1.
   Read current Omega Problems/gawron-ulas-2022-factorial-sign-conjecture-4-4.md
   in full. It already refutes the full universal assertion via m=3,k=2 and
   the negative progression 12s+38. Its cubic identity, exact scope and
   journal-version limitation were inspected. Excluded before attacking it.
2. **Barry Riordan determinant**. Read the actual current Omega Barry
   Riordan–Pascal kernel problem body: Gram identity and determinant one
   for all truncations. This concerns the 2013 paper, not the distinct 2021
   almost-Riordan row-sum conjecture (2108.13537). The latter's actual
   Conjecture 27 was read but not promoted: it appears to be an elementary
   production-matrix calculation. No assertion that the two are identical.
3. **Hypercube semicompleteness**, 2102.07083v1 Conjecture 1.0.3.
   Read the actual source and its definition. For C_M^N=sum_{i=0}^M
   binom(N-1,i), the hockey-stick identity gives
   1+sum_{h<N} C_M^h >= C_M^N. Classical complete-sequence induction
   therefore supplies all subset sums, a stronger property. Excluded as
   routine classical corollary, not claimed as a discovery.
4. **Associated Stirling coefficient positivity**, 2409.01489v1
   Conjecture 3.3.1. Read source definitions and statement. Taylor's integral
   remainder converts the coefficients of e^(-x/(r+1)) B_r(x) into central
   moments of Beta(1,r). Read the actual Skorski *Bernstein-type bounds for
   beta distribution*, Theorem 3 and Corollary 3: the recurrence and signs
   of all odd central moments already yield the result immediately.
   Excluded as a routine published-theorem corollary. No source conjecture
   novelty is inferred from the lack of an exact titled match.
5. **Squared-path cut-complex diagonal recurrence**, 2407.08158v1,
   Conjecture 4.10. Derived the complete face-count route: complements of
   size k+1 are bad exactly when they are intervals, and complements of
   size >=k+2 are good; connected k-sets have gaps 1 or 2. This yields

       beta(k,n) = binom(n-1,n-k)
                   -sum_j binom(k-1,j)(n-k-j+1) + (n-k),

   with 0<=j<=min(k-1,n-k), hence polynomial diagonals of degree r-1.
   Live search located Zhang–Yang 2605.22808v1 (May 21, 2026).
   Read its actual full theorem/proof body, which gives exactly this formula
   and complementary-face argument. Excluded immediately; no proof packet.
6. **Ordinary reciprocal-subsum coprimality**, 2605.10512v1 Conjecture 2.
   Independently found the reduction n mod d followed by positive-ray
   noncancellation at exp(pi i/d): all products for partitions of r<d
   have the same phase, with positive cosine factors. Live search found
   Chen–Ono–Zhang 2605.21718v1 (May 20, 2026). Read its actual Theorem 1,
   Lemmas 4–5 and proof: identical reduction and cosine argument.
   The actual published original also acknowledges that settlement.
   Excluded; moved to the distinct surviving Conjecture 4 above.

RSK operators (2410.23009v1) and combinatroid reconstruction
(1907.09644v1) were also body-read as screening leads, not attacked deeply
or declared settled. No result or exclusion theorem is claimed for them.

## Current-registry coverage and limits

Initial live HEADs, complete nontruncated Problems/D5/Blueprint trees,
OpenAI preprints tree and count-ex-machina tree/registry are saved, with
real UTC fetch timestamps and SHA256 hashes. OpenAI stayed at 7ef5c0cc...;
Omega advanced beyond the earlier f6219b3... snapshot to e1236ab0....
The relevant live Omega claim bodies above were read, not just filenames.
The count repository was correctly suvrit/count-ex-machina.
No matching denominator log-concavity resolution was located in these
bounded registry/title/primary-body screens. This is not body-wide coverage
of every public file, nor a global novelty clearance. The selected primary
successor explicitly distinguishes the unresolved coefficient-shape questions
from its coprimality and special-value results. The original journal is open
access and was retrieved without credentials. No challenge was bypassed.

## Reproduction

Run from any working directory, with Python 3 and SymPy 1.14.0:

    python /absolute/path/to/this/lane/denominator_check.py
    python /absolute/path/to/this/lane/cross_check.py
    python /absolute/path/to/this/lane/factor_check.py

The last script is a separate bounded diagnostic of the ordinary numerator
irreducibility question, NOT a proof or the selected target: n=2..20,
primitive factors over Q all irreducible. Polynomial contents are explicitly
reported; no Z-vs-Q convention counterexample is promoted. It enumerates
partitions only up to 20, with no unbounded cache. Every diagnostic sets a
512 MiB hard address-space limit and one BLAS/OpenMP thread; there is no
randomness. Fetches are reproducible through fetch.py but will naturally
observe later heads. No Lean was started because there is no qualifying full
ordinary result requiring a substantive preliminary check.
