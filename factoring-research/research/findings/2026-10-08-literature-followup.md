# Primary-literature leads retained from the continuation

2026-10-08. This is a bounded source check and future-work record, not an
exhaustive latest-baseline claim. Verified new factoring improvement: NONE.
The immediate active work remains H014/H016/H017.

## Batch processing relevant to H016

Bernstein's [smooth-parts manuscript](https://cr.yp.to/factorization/smoothparts-20040510.pdf)
states a batch bit bound in the total input length for finding the largest
factor-base-smooth divisor of each input. His
[factorization page](https://cr.yp.to/factorization.html) also identifies the
related small-factors algorithm. These are established candidate subroutines,
not new mechanisms discovered here. H016 must inspect the actual constructions,
recover needed prime exponents, and distinguish integer data from ideal data.
The H014 proposer recorded a failed PDF retrieval; a fresh primary search now
returns the indexed text, so that retrieval failure is not a mathematical gap.

## Tensor-network Schnorr sieving: deferred constructive lead

The [January 2026 revision](https://arxiv.org/html/2410.16355v3) of Tesoro et al.
reports numerical resource fits for a lattice-based relation generator; its
complexity extrapolation is not a complexity-theoretic proof. The method uses
LLL/Babai followed by nearby binary lattice corrections, tensor optimization,
and sampling without replacement. A transverse-field perturbation makes the
sampling Hamiltonian nondiagonal; pointing out that the unperturbed diagonal
Hamiltonian has product eigenstates would not refute their actual method.
The resource accounting sets aside the optimization sweep count based on
observed convergence. Lattice rank and input bit length are distinct parameters.

Potential independent question, not yet a hypothesis or delegated task: can
the original diagonal-plus-one-row lattice objective supply a costed exact
low-energy generator with enough useful relations? In original exponent
coordinates its form is sum_j f_j^2 e_j^2+(sum_j a_j e_j-T)^2. This algebraic
structure suggests dynamic programming, but the sum range and log precision
must be charged, and the transformed binary domain is not a simple original
coordinate box. No fast algorithm or yield bound has been derived here.

Any continuation must measure complete processing, useful matrix rank and
proper splitting, not just a count of smooth triples. A general NP-hardness
statement about CVP does not settle this particular structured input family.
Do not install a tensor-network package or repeat tiny factorizations merely
to reproduce an empirical polynomial fit.

## Practical and conditional results kept separate

[CUDA-MPQS, October 2026](https://arxiv.org/abs/2610.07126) reports GPU
implementation gains within quadratic-sieve scaling. The reported benchmarks
have not been reproduced here and supply no new asymptotic factoring bound.

[Integral polynomials with small discriminants and resultants](https://arxiv.org/abs/1501.05767)
studies fixed-degree counting with varying polynomial pairs. H017 may inspect
it, but cannot import those quantifiers into a growing-degree fixed-f problem.
No theorem from this lead was used in the accepted H013 count.
