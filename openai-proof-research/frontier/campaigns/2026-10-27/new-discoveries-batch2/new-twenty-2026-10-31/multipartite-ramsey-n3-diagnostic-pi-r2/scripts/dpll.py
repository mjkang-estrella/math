#!/usr/bin/env python3
"""Bounded deterministic DPLL for the MathDB 359209 n=3,s=4 diagnostic CNF.

Budgets (per task): CPU <= 120 s, wall <= 140 s, <=2 CPUs (taskset applied by
runner), AS <= 6 GiB (ulimit by runner). Stops at first SAT / certified UNSAT /
cap. Every decided literal is recorded; a SAT model is the 48-bit witness.

UNSAT status is unverified: this draft does NOT implement proof logging.
A return of None is not an accepted UNSAT certificate. SAT must be independently
validated against all graph-pair constraints.
"""
import json, sys, time, os, resource

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def read_cnf(path):
    n, clauses = None, []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in 'cp%':
                if line.startswith('p'):
                    n = int(line.split()[2])
                continue
            lits = [int(x) for x in line.split() if int(x) != 0]
            clauses.append(tuple(sorted(lits)))
    return n, clauses

def dpll(n, clauses, wall_deadline):
    # assign: dict var -> bool. trail for the trace.
    sys.setrecursionlimit(100000)
    node_count = 0
    unit_props = 0

    def propagate(assign, clauses):
        """Unit propagation to fixpoint. Returns (assign, ok, units)."""
        nonlocal unit_props
        assign = dict(assign)
        units = []
        while True:
            # collect unit clauses under current partial assignment
            found = None
            for c in clauses:
                unassigned = []
                sat = False
                for l in c:
                    v = abs(l); val = assign.get(v)
                    if val is None:
                        unassigned.append(l)
                    elif (l > 0) == val:
                        sat = True; break
                if sat: continue
                if not unassigned:
                    return assign, False, units  # conflict
                if len(unassigned) == 1:
                    found = unassigned[0]; break
            if found is None:
                return assign, True, units
            v = abs(found)
            if v in assign: return assign, False, units
            assign[v] = found > 0
            units.append(found)
            unit_props += 1
            if time.time() > wall_deadline:
                raise TimeoutError

    def solve(assign, clauses):
        nonlocal node_count
        node_count += 1
        assign, ok, units = propagate(dict(assign), clauses)
        if not ok: return None
        # pick unassigned var in most clauses (2-clause-ish heuristic, deterministic tie-break by var id)
        best_v, best_score = None, -1
        counts = {}
        for c in clauses:
            for l in c:
                v = abs(l)
                if v not in assign:
                    counts[v] = counts.get(v, 0) + 1
        if not counts:
            return dict(assign)  # all clauses satisfied? need check
        # verify all clauses satisfied
        for c in clauses:
            sat = any((l > 0) == assign[abs(l)] for l in c if abs(l) in assign)
            if not sat: break
        else:
            return dict(assign)
        best_v = min(counts, key=lambda v: (-counts[v], v))
        for val in (True, False):
            if time.time() > wall_deadline: raise TimeoutError
            a2 = dict(assign); a2[best_v] = val
            r = solve(a2, clauses)
            if r is not None: return r
        return None

    return solve({}, clauses), node_count

if __name__ == '__main__':
    t0 = time.time()
    n, clauses = read_cnf(os.path.join(BASE, 'ramsey_n3_s4.cnf'))
    assert n == 48 and len(clauses) == 2400
    deadline = time.time() + 110
    try:
        model, nodes = dpll(n, clauses, deadline)
    except TimeoutError:
        model, nodes = 'TIMEOUT', -1
    wall = time.time() - t0
    cpu = resource.getrusage(resource.RUSAGE_SELF).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_stime
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0  # MiB
    out = {'wall_s': round(wall, 3), 'cpu_s': round(cpu, 3), 'peak_rss_MiB': round(peak, 1), 'nodes': nodes}
    if isinstance(model, dict):
        model = {v: model.get(v, False) for v in range(1, 49)}
        bits = dict(model)
        out['result'] = 'SAT'; out['witness_bits'] = bits
        # verify model satisfies all clauses
        okall = all(any((l > 0) == model[abs(l)] for l in c) for c in clauses)
        out['model_satisfies_cnf'] = okall
    else:
        out['result'] = 'UNKNOWN_TIMEOUT' if model == 'TIMEOUT' else 'UNVERIFIED_UNSAT'
    with open(os.path.join(BASE, 'solver-result.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != 'witness_bits'}, indent=1))
