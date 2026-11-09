"""Independent CNF for 'there is a 2-colouring of K_n with no colour-1 cyclic S_a^sc and no colour-2 cyclic P_b^mon'.
Literal source definition: phi(i) = s[(i - t) mod k] for sorted k-subsets s and rotations t.
Variable x(u,v) true = colour 2.  usage: cnf.py a b n out.cnf"""
import sys, itertools
a, b, n, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
idx = {}
for u, v in itertools.combinations(range(n), 2): idx[(u, v)] = idx[(v, u)] = len(idx) // 2 + 1
star = [(0, i) for i in range(1, a)]
path = [(i, i + 1) for i in range(b - 1)]
def tuples(k):
    for s in itertools.combinations(range(n), k):
        for t in range(k):
            yield [s[(i - t) % k] for i in range(k)]
cl = set()
for phi in tuples(a): cl.add(tuple(sorted(idx[(phi[u], phi[v])] for u, v in star)))
for phi in tuples(b): cl.add(tuple(sorted(-idx[(phi[u], phi[v])] for u, v in path)))
with open(out, 'w') as f:
    f.write(f'p cnf {n*(n-1)//2} {len(cl)}\n')
    for c in sorted(cl): f.write(' '.join(map(str, c)) + ' 0\n')
