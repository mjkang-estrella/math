# Count instances that propfactor_tight_milp.py skipped (empty or >90 edges) for given seed/trials/mode (generation only).
import sys
sys.path.insert(0, sys.argv[4])
from propfactor_tight_milp import gen
seed, trials, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sk = 0; ks = {}
for t in range(trials):
    a, b, E, p, N = gen(seed * 10**7 + t, mode == 'simple')
    if not E or len(E) > 90: sk += 1
    else: ks[len(p)] = ks.get(len(p), 0) + 1
print({'seed': seed, 'mode': mode, 'trials': trials, 'skipped': sk, 'decided_by_milp': trials - sk, 'by_k': ks})
