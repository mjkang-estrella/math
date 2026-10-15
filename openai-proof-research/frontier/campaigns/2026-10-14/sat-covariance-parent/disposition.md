# Parent disposition of the SAT covariance attempt

Status: original central limit theorem unresolved; technical partials retained,
not independently accepted and not counted. Campaign count is unchanged.

The parent read proposal.md, proofs.md and sources.md in the completed
sat-covariance-discovery directory and reproduced exponent_check.py (exit 0).
The checker verifies powers in analytic majorants; it does not simulate SAT
or prove a CLT. The full target remains every fixed k>=4 for uniform proper
clauses sampled independently with replacement, with finite-size centering
and the pinned linear-order variance.

The attempt localizes expected post-window predictable energy for k>=4 and
reduces Var(Q)=o(n^2), for k>=8, to a pre-window posterior covariance sum.
The unpaid sum still has only an O(n^2) bound; no o(n^2) estimate or saved
power is supplied. Neither the original fluctuation theorem nor its negation
has been proved. The k>=8 reduction is not a solution at the original scope.
The prior cooperative-killing obstruction to a root-collision shortcut remains.

Editorial corrections to the frozen partial, recorded without overwriting it:

- Section 7 incorrectly says s_n is a linear distance before mu. The index
  s_n itself is Theta(n), whereas mu-s_n=w_n+O(1), with
  w_n=ceil(sqrt(n)(log n)^2)=o(n). Subsequent formulas use this correct gap.
- Lemma 3 ends with (U_k+delta)n+1 for a statement without +1. Apply the
  first-moment argument with delta/2 to obtain its stated eventual bound.
- Section 9's pointwise bound for E_Y|U|^4 needs E_Y also on the first
  term 8|T_0-nu|^4. Taking the displayed outer expectation then yields
  the intended bound by conditional Jensen, since A is prefix measurable.

These local corrections do not pay the missing covariance saving. A future
attempt must carry the full unpaid target and these corrections forward.
