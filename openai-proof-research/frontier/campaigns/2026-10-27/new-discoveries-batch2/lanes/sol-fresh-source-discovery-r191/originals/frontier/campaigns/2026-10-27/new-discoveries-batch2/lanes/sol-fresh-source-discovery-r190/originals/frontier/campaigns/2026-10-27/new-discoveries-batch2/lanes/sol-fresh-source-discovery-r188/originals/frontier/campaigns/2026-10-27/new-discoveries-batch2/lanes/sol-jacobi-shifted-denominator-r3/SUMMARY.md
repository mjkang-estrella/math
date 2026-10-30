# Handback: full law unresolved; credit 0

2026-10-28. Solo; no children; assigned-lane writes only.

The requested all-order shifted denominator exponent is **not proved**.
No `PROOF.md`, Lean result, paper, acceptance, or discovery credit is claimed.

A direct formal differential equation for the literal Definition 2.1 series was
derived, without assuming analytic phase identification. Its Riccati recurrence
proves the pure top-coefficient formula (primary equation (14)) at all orders,
as well as even-index reality and the relevant degree bound. The top coefficient
has valuation `-2r-v2((r-1)!)`, so attainment is now supplied by an ordinary proof.
Full details and qualifications: `discovery.md`.

The missing statement is exactly

    (r-1)! J(s_(2r-1)) in 2^(2r-2) Z_(2)[u,v] for every r>=1,

where `s_1=V`, `s_(n+1)=-D s_n-sum_(a+b=n)s_a s_b`,
`V=u(1+t^2)+v(1+t^(-2))`, `D=-(1+t^2)d/dt`, and `J` takes the unique odd
Laurent primitive under `D` and evaluates it at `t=1`.
This is the all-coefficient upper bound; the central cancellation remains open.

Mandatory falsifiers: already at `r=2`, the primitive's `u^2` term is
`t+t^3/3`; its terms have valuation zero but their midpoint sum has valuation two.
Also `sum_(j=0)^3 binom(3,j)/(2j+3)=464/315` refutes an overly broad shifted-moment
valuation claim. These block two natural shortcuts, not the source law.

Reproduce: `python3 check.py`. Actual `checks.json` compares the direct source and
Riccati constructions through `n=9`, checks the curve ODE through `s=4`, and checks
the new recurrence through `r=8`. A 500 MiB process limit is imposed. These tests
do not replace an all-order proof. No Lean investment was justified.

The current source is 2608.23006v2 (2026-10-05); companion 2609.29531v2
(2026-10-14) already proves the original-variable law. Current GitHub registry
heads and relevant untruncated subtrees, catalogue bodies, and MathDB 391922 were
screened; no shifted-law counterpart was located in the bounded inspection.
See `source/registry-screen.md`, retrieval receipts and `provenance.json` for
chronology, URLs, hashes, and material coverage limits. No worldwide-priority claim.
