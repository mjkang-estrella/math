# H039 arithmetic proposals: scoped rejection, no universal exclusions

Claude Opus5.5 completed this independent lens without a surviving operator.
Raw report and task ID: H039-arithmetic-opus-raw.md. Root reviewed its algebra
and checked the stale3SUM statement against a primary source. A requested new
native Sol critic role failed with 'agent thread limit reached'; it did not run
and is not counted as an independent review. Root performs the qualification
below. Existing composition reviewers are separate roles. No runs, imports,
experiments, implementation or Lean changes; verified improvement NONE.

## Translation resultants

For monic F(Y)=product_i(Y-y_i), the defining identity
Res_Y(F(Y),S3(X,Y,c))=product_i S3(X,y_i,c) holds exactly. When y_i!=c, the
quadratic factor has leading coefficient(y_i-c)² and residual roots
x(P_i+C),x(P_i-C), with usual rational-point and sign conventions. For finite
C with f(c)!=0 and y_i=c, the factor is linear and the missing root represents
infinity. Two-torsion, multiplicities, scalar factors and modular wraparound
must be handled separately. Dyadic translations represent the indicated odd
interval roots only with these conventions.

Dense expansion has a linear output-size cost in its actual degree. That does
not prove an implicit evaluator must expand all leaves. The claimed soft-linear
resultant-construction algorithm was not specified or independently verified.
No new compressed evaluation identity or target-witness recovery was delivered;
the existing missing interval-product operation has merely been restated.

## Endomorphism and coset costs

The imaginary-quadratic norm inequality for a noninteger endomorphism remains
the scoped H036 result. It is not a universal evaluation-cost lower bound.
If a SPECIFIED isogeny chain uses degrees at most B, degree multiplicativity
gives a chain-length bound log_B(deg(alpha)). Translating that into field work
requires actual step formulas and initialization. Generic-size discriminant
heuristics and the numerical256-bit chain comparison were not proved or priced.
The displayed canonicalization ratio assumes enumeration of all m images with
the stated per-image cost; different representations or orbit procedures need
their own analysis. No new cheap endomorphism operator was supplied.

For the abscissa-coset predicate, use the actual eligible point count N rather
than the root parameter n. The q/sqrt(N) birthday invoice assumes a particular
fresh-sampling/endpoint law and useful recovery. It is not a universal lower
bound. H038's bounded-graph lemma requires its fixed explicit base, materialization,
fresh targets and bounded dependencies; it cannot be invoked automatically for
an implicit predicate or arbitrary distinguished-point algorithm. No new log
recovery from multiplicative structure of abscissae was constructed here.

## Coprime homomorphisms and probabilistic polynomials

A group homomorphism from a prime-order q group into a group of exponent
coprime to q is trivial. This excludes the stated homomorphic bridge only.
It does not classify every nonhomomorphic lift, observable or richer invariant.
The listed ring/auxiliary-pairing schemes require individual maps and targets;
the broad one-line exclusion is not accepted beyond that precise lemma.

High EXACT Boolean degree does not exclude low PROBABILISTIC degree. Root's
elementary counterexample over F2 is OR on n bits. For ell independent uniform
vectors r_j in F2^n, define

    P(x)=1-product_(j=1..ell)(1-<r_j,x>).

Its degree is at most ell. At x=0 it equals0 always; for each fixed nonzero x,
the ell inner products are independent fair bits, so P(x)=1 with probability
1-2^(-ell). OR has exact multilinear degree n, yet constant per-input error
permits constant ell. This invalidates the report's inference from exact degree
alone. It does NOT supply such a polynomial or a fast batch algorithm for S3.
Likewise, explicitly expanding a zero-count coefficient tensor is one method;
its size is not a lower bound on every circuit or contraction strategy.

The report's claim that the best integer3SUM gains are only polylogarithmic is
stale. Root freshly read the primary abstract of
[Alman–Vassilevska Williams, submitted5 October2026](https://arxiv.org/abs/2610.06783),
which states deterministic O(n^1.9992) time for polynomial-size integers.
H017-hybrid-disposition.md already records the fuller theorem-scope check.
No finite-field elliptic-curve reduction is supplied by this fact: an actual
success-preserving reduction with paid size and recovery is still required.
This is an abstract-level freshness correction, not an independent audit of
the entire76-page paper or an ECDLP improvement.

## Decoding scope and disposition

Agreement thresholds retain the specific code dimension, evaluation set and
decoder assumptions in H006. Failure of a named sufficient decoding radius
does not prove every specialized decoder impossible. No new decoder was given.

No mechanism from this pass meets the full-work acceptance gate. Preserve the
specified missing operations, decline numerical testing, and do not promote
unsupported lower bounds into closures of coordinate-aware research. Ordinary
square-root baseline unchanged; no calibrated hardware or full-solver saving.
