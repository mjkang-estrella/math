# Jacobi shifted denominator: incomplete, credit 0

Root read the completed pi-jacobi-shifted-denominator-r2 report and scripts on
2026-10-28. No full denominator law or Lean endpoint was delivered. Count remains
2/30 additional, 32/60 total. Original worker files are preserved.

The index-swap proof does establish B_n(v,u)=conj(B_n(u,v)). Consequently Im B_n
is antisymmetric and divisible by u-v with an integral symmetric quotient.
The axis subtraction f(u,v)-[f(0,v)-f(0,u)] is divisible by uv(u-v), also with
integral symmetric quotient. These elementary structural facts are uncredited.

Several stronger assertions are not proved by the supplied argument:

1. Swap/conjugation symmetry does not imply Im B_(2k)=0. The claim that
   F(Z)F(-Z) is real 'by (iii) applied twice' is circular: swapping variables
   only conjugates that product. For example F(t)=1+i(u-v)t^2 has precisely the
   swap symmetry and its product with F(-t) is not real. This is a counterexample
   to the proposed implication, not to even reality for the actual Jacobi series.
2. Theorem 3's forward direction does not locate the valuation minimum at the
   highest pure coefficient. The Law implies slice divisibility and coupling
   divisibility, but not the specified top-coefficient unit without another
   theorem. For m=2, f=64(u-v)+128(u^3-v^3) is an elementary counterexample to
   that general inference. The stated (A)+(B) are sufficient, not an established
   equivalence. A true equivalent condition is divisibility of both slice and R,
   together with attainment in at least one of their coefficient sets. The
   primitive factor uv(u-v) preserves 2-adic content by reduction modulo 2.
3. Degree bounds are asserted in theorem statements although the report itself
   labels the general degree law conjectural. They are not supplied by swap
   symmetry or divisibility. Conditional on deg f=m+1, nonzero R has degree m-2,
   not the degree m-1 equality claimed in the verification table.
4. The report's shifted-variable prose includes the erroneous mu_alpha=1/4-alpha;
   use u=alpha^2-1/4 and v=beta^2-1/4. Its heading/access date 2026-10-27 predates
   the actual Oct28 task. Do not inherit those dates as verified retrieval times.

Root's independent SymPy construction reproduces n<=9 exactly, including even
reality in that finite range, Im B_5=64(u-v)(7u^2+22uv-86u+7v^2-86v+150), and
R_5=960. These are checks, not proofs of the missing all-order statements.
Root executed the worker's decomposition.py division routine on K=960uv(u-v):
it returns None instead of R=960. Its ascending
u-exponent loop rejects the negative u*v^2 term before solving for the constant
R_5. The summary verification JSON is not the output schema of that routine.
No reported m<=30 verification is adopted without reproducible checks.
Root fixed one scratch-check bug (comparing an expanded expression to an unexpanded
right side syntactically); the corrected exact difference is zero and all tests pass.

Next research must derive a genuine all-order transfer/valuation mechanism from
the exact source. Do not formalize the flawed equivalence or parity argument,
count helpers, or advertise a new resolution from these partial observations.
