# Scope accounting: A is technical; B is now the substantive target

A is unchanged from original-scope.md. Reading the primary GR2021 proof
found its Proposition 12 already subtracts local affine functions and obtains
small-radius derivative approximation; its final section joins the local and
nonlocal operators with equality-set gradient matching. The planar signed-band
premise plus square cutoffs/Poincare supplies the same operation. A proof may
be useful, but it is not nominated as a substantial result. This finding was
made before writing a theorem manuscript, formalization or acceptance claim.

B (full target; fixed before its detailed proof attempt): For every real
f in BV(R^2) and every real sequence f_j in BV(R^2) such that

    ||f_j-f||_1 -> 0 and |Df_j|(R^2) -> |Df|(R^2),

one has

    |D(M f_j)|(R^2) -> |D(M f)|(R^2).

Here BV is inhomogeneous, M averages |f| over ALL centered Euclidean disks,
and derivatives in the conclusion are full vector Radon measures, including
jumps and Cantor parts. Source BV bounds ensure all displayed variations are
finite. Local L1 convergence of M f_j is part of the intended strict-output
interpretation and is proved separately. No common support, sign restriction,
radiality, absence of jumps/Cantor part, smoothness of approximants or
nonvanishing hypothesis is allowed. BV-norm convergence of output derivative
MEASURES is NOT the target (moving jumps would rule that out). Strict-input
convergence is weaker than BV-norm convergence and includes mollification.

The target is neither claimed known open nor asserted true. The likely unpaid
bridge is a SHARP upper passage of output variation at input jump layers.
A constant-C localized variation bound cannot replace coefficient one.
A proof for W11 limits, a flat single jump model, lower semicontinuity alone,
or smooth/common-support inputs does not settle B. If B cannot be proved,
retain it verbatim and report the precise failure; do not nominate A instead.
