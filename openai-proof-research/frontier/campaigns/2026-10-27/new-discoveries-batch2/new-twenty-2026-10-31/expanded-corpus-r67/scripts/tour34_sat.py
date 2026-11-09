# Diagnostic for MathDB 372373 (Conjecture 23 of arXiv:2601.00144): does some n-vertex (3,4)-tournament
# (exactly 4 of 6 orderings of every 3-set are edges) lack a spanning tight path?  Writes a DIMACS CNF;
# SAT <=> counterexample exists.  Symmetry breaking: none (sound for both answers).
import itertools, sys, pathlib
n = int(sys.argv[1]); out = pathlib.Path(sys.argv[2])
var = {}
for t in itertools.permutations(range(n), 3): var[t] = len(var) + 1
cl = []
for S in itertools.combinations(range(n), 3):
    xs = [var[p] for p in itertools.permutations(S)]
    cl += [[a, b, c] for a, b, c in itertools.combinations(xs, 3)]          # at least 4 true
    cl += [[-y for y in c] for c in itertools.combinations(xs, 5)]          # at most 4 true
with out.open('w') as f:
    f.write(f'p cnf {len(var)} {len(cl) + (1 if n < 3 else 0) * 0 + __import__("math").factorial(n)}\n')
    for c in cl: f.write(' '.join(map(str, c)) + ' 0\n')
    for p in itertools.permutations(range(n)):
        f.write(' '.join(str(-var[p[i:i + 3]]) for i in range(n - 2)) + ' 0\n')
print('vars', len(var), 'clauses', len(cl) + __import__('math').factorial(n))
