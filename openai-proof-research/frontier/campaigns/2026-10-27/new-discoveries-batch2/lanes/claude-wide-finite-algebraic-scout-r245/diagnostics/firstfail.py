"""For every checked non-cograph Laplacian-integral graph (n<=9), record which
irreps (ordered lexicographically decreasing) carry non-integral eigenvalues."""
import json, sys, collections, pathlib
import numpy as np
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from intcay import partitions, irrep_transpositions, D
out = {}
for n in range(6, 10):
    files = [D / f'intcay-result{n}.json'] if n < 9 else sorted(D.glob('intcay-result9-L*.json'))
    graphs = []
    for f in files:
        st = json.loads(f.read_text())
        if 'checked_noncographs' in st:
            graphs += st['checked_noncographs']
    if n < 9:  # older result files lack the list; recompute it from the level-free files
        from intcay import lap_integral, is_cograph
        import itertools
        full = n * (n - 1) // 2
        graphs = []
        for code in json.loads((D / f'graphs{n}.json').read_text()):
            code = tuple(map(tuple, code))
            for edges in (code, tuple(e for e in itertools.combinations(range(n), 2) if e not in set(code))):
                if len(edges) * 2 == full and edges != code:
                    continue
                if lap_integral(n, edges) and not is_cograph(n, edges):
                    graphs.append(edges)
    shapes = sorted(partitions(n), reverse=True)
    reps = {s: irrep_transpositions(s) for s in shapes if max(len(s), s[0]) > 0}
    first = collections.Counter(); bad_sets = collections.Counter()
    for edges in graphs:
        bad = []
        for s in shapes:
            M = sum(reps[s][(a + 1, b + 1)] for a, b in edges)
            ev = np.linalg.eigvalsh(M)
            if np.max(np.abs(ev - np.round(ev))) > 1e-6:
                bad.append(s)
        first[str(bad[0])] += 1
        bad_sets[str(bad[:3])] += 1
    out[n] = {'graphs': len(graphs), 'first_failing_irrep': dict(first)}
    print(n, len(graphs), dict(first))
(D / 'firstfail.json').write_text(json.dumps(out, indent=1))
