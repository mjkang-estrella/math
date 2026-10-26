# Potential next pair: arithmetic-function ratio inequalities

Exact MathDB snapshots: `375256.json`, `375257.json`. Both use the source
arXiv:2606.12484. Both have an existing full posted proof by Shivam Patel;
any formal verification must credit that prior argument and not claim a
new disproof/proof. Do not count an abstract real inequality alone as a
complete proof of the arithmetic-function statement.

For 375256, set `x=phi(n)^k`, `y=psi(n)^k`, `z=sigma(n)^k`,
`a=(n-1)^k`, `b=(n+1)^k`. Need fully justified arithmetic bridges
`0<x<=a<b<=y<=z`, then a purely rational inequality.

An elementary derivative-free certificate for the real step is available.
Write `r=x/y`, `t=z/y=1+v`, `q=a/b`, so `0<r<=q<1`, `v>=0`, and

    S(r,t) = r/(1+t) + 1/(r+t) + t/(r+1).

Algebra gives

    S(r,1+v)-S(r,1)
      = v*[2v^2+(4+r-r^2)v+r(1-r)(r+3)]
        /[2(v+2)(r+1+v)(r+1)],

and

    S(r,1)-S(q,1)
      = (q-r)*[4-(1+r)(1+q)]/[2(1+r)(1+q)].

Both are nonnegative in the specified domain. These identities were
derived by the parent by expanding common denominators, not imported as
axioms. They still require Lean checking.

An alternative natural definition for Dedekind psi is

    psi(n) = sum_{d|n, squarefree(d)} n/d.

This standard divisor-sum expression gives psi<=sigma by dropping the
squarefree restriction and using `Nat.sum_div_divisors`. The lower bound
psi>=n+1 follows from the terms d=1 and any prime divisor of n. Euler phi
positivity and phi(n)<=n-1 have standard mathlib lemmas. HOWEVER, a full
packet must justify that the chosen psi definition is the same arithmetic
function as the source's Euler-product definition; don't hide that bridge.

For 375257, the posted source contains an explicit positive-coefficient
common-denominator polynomial. Read and verify it rather than relying on
its numerical or algebraic claims. The same arithmetic-function bridge
may be reused, but this is a distinct mixed-ratio source question; count
the question once, not each coefficient or equality case.

Potentially cleaner arithmetic route (no squarefree-sum bridge): define the
standard integral Dedekind product directly,

    psi(n) = product_{p in n.primeFactors} p^(factorization(n,p)-1)*(p+1).

For n>=2 every exponent is positive, and each factor is strictly larger
than p^exponent. Positive product comparison plus
`Nat.factorization_prod_pow_eq_self` gives psi(n)>n, hence psi>=n+1.
Mathlib's
`ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`
at exponent1 expresses sigma(n) as a product of geometric sums. Each sum
dominates its final two terms `p^(e-1)+p^e`, exactly the corresponding psi
factor, giving sigma>=psi by pointwise product comparison. The integral
product is a standard definition of Dedekind psi; a formal equivalence to
`n * product(1+1/p)` may be included to remove any source-model ambiguity.
`Nat.totient_pos` and the strict upper bound on totient supply the phi side.
The source's equality classification is not needed for either conjectured
inequality, so do not overextend scope to it unless separately proved.
