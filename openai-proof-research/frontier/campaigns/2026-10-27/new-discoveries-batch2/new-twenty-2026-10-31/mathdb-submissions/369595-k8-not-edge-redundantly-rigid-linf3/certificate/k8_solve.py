#!/usr/bin/env python3
"""Solve cert/k8.cnf with CaDiCaL 1.9.5 (PySAT) and write a DRAT proof.
Usage: k8_solve.py <cnf> <drat-out>
The proof is untrusted; it is converted to LRAT by drat-trim and then checked in Lean."""
import sys, time
from pysat.formula import CNF
from pysat.solvers import Solver
cnf = CNF(from_file=sys.argv[1])
t = time.monotonic()
with Solver(name='cadical195', bootstrap_with=cnf.clauses, with_proof=True) as s:
    res = s.solve()
    assert res is False, res
    proof = s.get_proof()
open(sys.argv[2], 'w').write('\n'.join(proof) + '\n')
print('UNSAT', len(proof), 'proof lines', f'{time.monotonic()-t:.2f}s')
