# H021 — Coordinator disposition

2026-10-08. **ACCEPT the costed generation constructions after one localized
recovery correction. Useful relation supply remains unresolved.**
Verified full factoring complexity improvement: **NONE**.

## Evidence and correction

The independent [review](H021-independent-review.md) read all 577 submitted
lines and accepted the prefix DP, capped suffix enumeration, exact counting/
unranking, expected-time uniform sampling, rational-log construction and
precision bounds within their explicit scopes. It found one false alternative
recovery claim: a table capped at E+1 loses comparisons above E.

The [submitted draft](H021-submitted-draft.md) is preserved byte-for-byte,
SHA256 `bba886b8995f0020cc22e28c8a8fc51f59b162a7008068bd6ed9dede8d664915`.
The review SHA256 is
`fbf77260be74592643de25ac35655d5d1f94d3d4896f3ba46e123b01cfed3221`.

The corrected [construction](H021-structured-lattice-generator.md) now uses
stored uncapped prefix predecessors for arbitrary box minimization. Capped
suffix recovery by minimizing transitions is restricted to minimum <=E;
this includes the global-minimum choice E=T². The coordinator checked the
review's analytic counterexample k=1,f=a=1,E=1,T>=3: capped terminal costs
are all 2, incorrectly preferring x=0, whereas the box objective is minimized
at x=1. Prefix recovery was correct already. Enumeration below E is unchanged.

The report also clarifies the reviewed implementation obligations:
predecessor rescanning needs all relevant prefix rows, not two rolling rows;
unit rows require gcd(u,N)=gcd(w,N)=1; gcd=N is neither a split nor a unit;
and retained valuations are additional to dense parity/dependency storage.
These are local scope repairs, not new algorithms.

## Accepted scope

For F(e)=sum f_j²e_j²+(sum a_j e_j-T)² with positive integer f_j,
the DP is exact over its finite box, and E=T² covers every global minimizer.
The suffix DFS gives complete, unique low-energy enumeration with charged
worst-case delay, including first and final output. Counting/unranking pays
the energy coordinate and count widths. Uniform rank rejection has expected
cost; a cap explicitly permits failure.

Prime/log construction needs no factors. The bounded-error rational-log rule
is a changed generator, not exact nearest rounding from the source paper.
Polynomial time applies when the numerical ranges are polynomial in input
length; polynomial bit lengths of huge ranges are insufficient. Indexed-memory
and conservative tape-simulation costs, all output sizes, and precision
refinement costs remain explicit. No transformed LLL domain or tensor-network
sampling distribution is identified with this DP.

Precision inequalities are sufficient guarantees, not necessary lower bounds
on actual cancellation. No inverse-polynomial useful density, rank, proper
square-root split or end-to-end factoring runtime follows. This is a standard
DP construction with no novelty claim. No implementation, finite experiment
or Lean refinement has been supplied.

## Next action

Only proceed to implementation for a named useful-population question or a
focused correctness need. Re-minimizing the same objective, increasing precision,
or sampling without a specified falsifier would not resolve the missing yield
law. A future experiment must freeze the generator, distribution, input family,
budgets and rejection criterion before execution.

No executable or shared Lean changed in this disposition; the prior shared
checks remain the latest checks and were not repeated for document edits.
