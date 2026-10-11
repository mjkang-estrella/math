# C171 reference-anchor convention failure

The added coordinate reconstruction initially assumed `weight_checks.C0`
was the Hamiltonian cycle to which the prescribed facial square switch
was applied. It is the functional's reference cycle, not that cycle.
This caused `mandatory-attempt-03` to fail with an empty JSON payload.
All three source stages and the exact assertion stderr are retained.

The corrected check constructs the actual pre-switch cycle as the
symmetric difference of F with the prescribed face `[5,7,3,1]`,
proves it belongs to the independently enumerated Hamiltonian family,
and switches that face to recover F coordinatewise. Weight evaluations
still use the actual functional reference C0. F and T remain distinct,
with values +1/14 and -1/2. No mathematical counterexample is claimed.
