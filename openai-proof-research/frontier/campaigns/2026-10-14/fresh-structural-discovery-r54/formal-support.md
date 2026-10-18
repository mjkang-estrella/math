# Feasible formal support and boundaries

No Lean theorem or formal verification is claimed. The exact girth metric
argument can be formalized using finite simple graphs, cycle-girth bounds,
nonnegative shortest paths and the elementary finite path-flow LP weak dual.
The independent primal proof avoids strong LP duality. The K_{2,3} quadratic
form is exact rational/integer algebra and is checked computationally.

checks/exact_examples.py exhaustively checks the stated finite families and
reproduces edge distances and the dual quotient. It does not implement a
general multicommodity LP, verify all graphs, prove an asymptotic upper bound,
or establish novelty. The universal arguments are in working.md.

The strict verifier establishes exact files/directories, payload hashes,
canonical source identities and primary PDF/text identities against an
external caller-supplied manifest hash. Those are integrity controls, not
mathematical proof, source truth audit, contribution review or acceptance.
