"""List the n=9 Laplacian-integral non-cographs whose (7,2) block is integral."""
import json, sys, pathlib
import numpy as np
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from intcay import irrep_transpositions, D
reps = {s: irrep_transpositions(s) for s in [(7, 2), (7, 1, 1), (6, 3), (8, 1)]}
for f in sorted(D.glob('intcay-result9-L*.json')):
    for edges in json.loads(f.read_text())['checked_noncographs']:
        def ok(s):
            ev = np.linalg.eigvalsh(sum(reps[s][(a + 1, b + 1)] for a, b in edges))
            return bool(np.max(np.abs(ev - np.round(ev))) < 1e-6)
        if ok((7, 2)):
            L = np.zeros((9, 9))
            for a, b in edges:
                L[a, a] += 1; L[b, b] += 1; L[a, b] -= 1; L[b, a] -= 1
            print(json.dumps({'edges': edges, 'm': len(edges), 'degrees': sorted(int(L[i, i]) for i in range(9)),
                              'laplacian_spectrum': sorted(int(round(v)) for v in np.linalg.eigvalsh(L)),
                              'integral': {str(s): ok(s) for s in reps}}))
