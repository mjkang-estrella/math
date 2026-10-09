# H044 conditional global chirp decoder via significant Fourier recovery

2026-10-09 UTC. A constructive follow-up to H044-information-disposition.md.
Root proposed replacing the unsupported short-window FFT by global significant
Fourier recovery. Native Astra /root/h007_additive_relations located the exact
source and derived the Boolean lift below. Root independently read the theorem
and checked the reduction. Native Sol /root/h034_c4_implementation independently
read the source and reviewed costs, deterministic precision and success scope.
No correlated public ECDLP feature has been supplied. No executable experiment,
new Lean theorem, practical speedup or novelty claim. Verified improvement NONE;
the working complete-solver exponent remains 1/2.

## Hypotheses and exact public queries

Let G have known odd prime order q and Q=kG. A public, deterministically
evaluable feature f on the entire subgroup defines F(n)=f(nG), |F(n)|<=1.
All exceptional point values must be specified. Suppose public alpha!=0,
beta modulo q and a known lower bound epsilon>0 satisfy

    S=E_n F(n)e_q(−alpha*n²−beta*n),  |S|>=epsilon.

The feature, its precision guarantee, these parameters and their construction
are hypotheses whose costs must be supplied, not free advice. The phase of S
need not be known. For arbitrary publicly chosen d compute

    y(d)=f(Q+dG)e_q(−alpha*d²−beta*d).

Substituting n=k+d in the normalized Fourier coefficient gives exactly

    y_hat(2alpha*k)=e_q(alpha*k²+beta*k)*S.

Hence the target coefficient has magnitude at least epsilon for every k.
This is a global identity requiring no local-window signal, independent noise
model or assumed secret interval. Computing dG costs a scalar multiplication,
not generally one addition; choosing arbitrary d is essential to this method.

## Source theorem and deterministic Boolean lift

[Akavia–Goldwasser–Safra, Section 7.2, Theorem 6 and footnote 5](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf)
give a query-access algorithm for Boolean functions on arbitrary Z/NZ. With
squared Fourier threshold tau and failure allowance delta, it returns
O(1/tau) characters containing all coefficients above that threshold with
probability at least 1−delta. Its stated runtime is
soft-O(log(N)*log²(1/delta)*tau^(−5.5)); the footnote suppresses specified
logarithmic factors. Their preceding complex-valued theorem does not state
this explicit exponent. We therefore apply the Boolean theorem through the
following reduction, rather than infer an epsilon^(−2) runtime.

Write y=r+i*s. At omega=2alpha*k, at least one of |r_hat(omega)| and
|s_hat(omega)| is >=epsilon/2, by the triangle inequality. Choose the smallest
power of two M>=32/epsilon. Compute deterministic clipped dyadic approximations
r_tilde(d),s_tilde(d) in [−1,1], each within epsilon/16. Define

    g_r(d,j)=+1 if j < floor(M*(1+r_tilde(d))/2), otherwise −1,
    0<=j<M,

and similarly g_s. Averaging over j approximates the corresponding real value
within 2/M+epsilon/16<=epsilon/8. Thus at least one lifted function has Fourier
coefficient magnitude >=3epsilon/8 at product-group frequency (omega,0).

Because gcd(q,M)=1, query t in Z/(qM)Z at (t mod q,t mod M). The product
character (omega,0) is exactly the cyclic character with frequency M*omega.
Run the Boolean theorem on each lift with tau=(epsilon/4)² and failure
allowance delta/2. Retain only returned frequencies divisible by M. Each
such frequency has a unique omega in [0,q), with no CRT alias. Form

    k_candidate=(2alpha)^(-1)*omega mod q,

and verify k_candidate*G=Q. There are O(epsilon^(−2)) candidates overall.
Union bounding the two decoder failures proves successful recovery with
probability >=1−delta for every k under the coefficient premise. No incorrect
candidate can pass exact verification. Failed lists may be retried with fresh
decoder randomness; the premise and paid query oracle remain necessary.

## Cost, memory and limits

Let C_query include Q+dG, deterministic feature evaluation, phase computation,
rounding and threshold arithmetic; let C_scalar price final scalar verification.
The source-theorem operation model and this reduction give the conservative
conditional invoice

    soft-O(epsilon^(−11)*polylog(q/delta)*(C_query+1)
           + epsilon^(−2)*C_scalar)
      + feature/parameter construction cost.

This is a sufficient upper bound, not the optimal dependence on epsilon.
No smaller workspace bound is asserted: retaining at most the total-work
amount is a conservative upper bound, and a practical memory comparison
would require implementing and accounting for the actual source algorithm.
Oracle and any explicitly charged fixed-base precomputation workspace are
additional; runtime-sized SFT workspace does not make that storage free.
There is no length-q orbit table or precomputed inverse table in this reduction.

The deterministic lift needs O(log(1/epsilon)) fractional precision plus
O(log q) integer operands. Reduce the known phase exponent modulo q before
approximating its exponential. Repeated inputs must produce the same Boolean
function, including deterministic rounding and boundary conventions. The source
algorithm's norm estimates also
need guard precision relative to their threshold gaps. A full bit-level
implementation/proof is not supplied by quoting the source's operation bound;
any claimed bit bound must account for those finite computations and the
actual feature evaluator. This record is a mathematical conditional reduction,
not an implemented or Lean-certified solver.

If all setup/query/precision overheads are polylogarithmic and
epsilon=q^(−gamma), gamma<1/22 is a conservative sufficient sub-square-root
regime, with logarithmic margins. Polylogarithmically small correlation gives
polylogarithmic recovery under the same hypotheses. No feature achieving
either regime is known from this wave. These conditional thresholds are
stronger signal requirements than the raw short-window proposal; their value
is removing an unjustified local-noise assumption, not proving an attack.

As a separate consistency source, [Galbraith–Laity–Shani, Theorem 7 and Section 3.2.3](https://arxiv.org/pdf/1607.01842)
state significant-Fourier recovery with arbitrary query access and distinguish
it from random-sample access. Root read the theorem; its unspecified polynomial
dependence is not used to improve the explicit exponent above.

## Admission and next decisive question

The earlier information report's missing short-window coherence is no longer
a reason to reject every global-chirp decoder. Its actual missing signal,
parameter discovery and costs remain. The next useful object is a named public
point observable with a proved or independently testable coefficient premise
strong enough for a priced decoder. Abstract sequences defined using secret
scalar phases are not implementations of f. No training, spectrum scan or
synthetic run is admitted merely because this conditional reduction exists.
Known sparse Fourier methods are prior art, not discoveries of this project.

No code changes or new audit entries. Existing checks do not certify these
paper arguments. Commands and final review disposition are recorded in STATE.
