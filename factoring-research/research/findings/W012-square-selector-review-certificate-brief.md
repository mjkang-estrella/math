# Fixed certificate preregistration — W012 review D

This file is written before executing the certificate program. No candidate
performance run, random trial, parameter sweep, or input search is authorized.
The mathematical proof, rather than these examples, establishes formulas (1)-(6).

Fixed cases and checks:
1. N=100001, B=4: exact ceiling roots, residual identities/bounds, condition
   9N>64(B+1)^5, second differences, slope-bin cardinalities and first/last
   binary-search bins. Expected t=(317,224,183,159), w=(52,17), total 69.
   Count bins algebraically; do not enumerate all slopes. Check the four bin
   endpoints J=24,40,41,92 and the excluded endpoint transitions J=23,93.
   The probability 52/69 is not dyadic: a witness against interpreting exact
   sampling as always using a bounded number of unbiased bits.
2. Same N, B=3: deterministic single interior vertex. B=2: empty interior,
   zero normalizing denominator; formula (5) is intentionally inapplicable.
3. N=15, B=5: t=(4,3,3,2,2), negative w_3 and a half-integer objective tie
   at lambda=1/2. A counterexample only to removing the curvature hypothesis.
4. N=19,v=2 and N=18,v=2: guard against truncating N/v before ceiling,
   and against always adding one to an exact integer square root.
5. N=36: (v,t)=(1,6),(4,3) have zero residual, while their midpoint has
   residual 117/8, proving the zero-residual sublevel is nonconvex.
6. N=45,v=5: zero residual is retained and a proper gcd is identified.

All checks use Python standard-library exact integers/Fraction; no randomness,
performance timings, factorization libraries, or generic optimization solver.
The result will retain every failed check. No shared solver or Lean code changes.
