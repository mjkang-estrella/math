# Full formal completion after the preliminary freeze

The 25 files in preliminary-review-hashes.json are unchanged. In particular,
PROOF.md and STATUS.md describe the earlier 18-declaration supporting stage and
remain as honest historical snapshots for the running preliminary reviewer.
This addendum supersedes their statements that the literal endpoint is absent.
It does not supersede their pending novelty/eligibility status.

The full literal endpoint now passes a fresh isolated strict replay: 64
declarations, 11 modules, warnings as errors, all module logs empty, and only
propext/Classical.choice/Quot.sound. The parent read every actual declaration
type and axiom report. Receipt and report are retained in verification/.

The source defines Euler numbers by the analytic generating function sec+tan.
The formal eulerGenerator is literally 1/cos+tan on the complex numbers.
normalizedEuler n is its real derivative coefficient at zero. Analyticity and
euler_coefficient_eq_real prove the coefficient is genuinely real, and
eulerGenerator_hasFPowerSeriesAt explicitly states that these are its actual
power-series coefficients. Thus the object is the source's E_n/n!, not an
abstract sequence chosen to satisfy the target conclusion. The final endpoint
source_conjecture_338918 has only n:Nat, j,k>=1; no normalization, convergence,
error-contraction or optimizer premise remains.

The previously missing analytic bridge is proved as follows. For k>=1, the
known cotangent derivative series in the upper half-plane is taken to a real
noninteger a along a+iy. Each reciprocal-power summand has norm bounded by
|m+a|^(-k-1), which is summable. Dominated convergence and continuity of the
actual iterated derivative identify the real-point derivative. At a=1/4,
the proved local identity sec z+tan z=cot(pi/4-z/2) and the affine chain rule
give the actual coefficients. All integer-series reindexings and parity sums
are explicit Lean proofs, including absolute summability.

The zeroth coefficient is handled directly: c0=1-pi/4. This avoids any
conditional-series rearrangement in the formal proof. The classical bound
pi<63/20, together with c2<=1/27, proves c2<=c0/3. The remaining even/odd
tails have the original contraction estimates. This is an alternative proof of
the same boundary fact in PROOF.md, not a new outcome or a changed theorem.

The two-page main.tex/paper.pdf has been built, rendered and read in full.
It retains credit zero and pending-review language. The preliminary review
does not cover these new formal/paper bytes; a NEW final five-gate review and
final deterministic packet/extracted replay remain required before counting.
No global priority claim, source-known subsequence credit or helper credit.
