# Reviewer differential test (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Compare reviewer count recursion with the author's frozen compute() on random
inputs (read-only import by path). Agreement is consistency evidence only."""
import importlib.util, json, random, sys
from pathlib import Path
from rc_counts import counts, make_rho
AUTH = Path(sys.argv[1]) / 'check-new-interfaces.py'
spec = importlib.util.spec_from_file_location('author_ci', AUTH)
mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
INV = [{'a':'a','b':'b'},{'a':'b','b':'a'},{'a':'a','b':'b','c':'c'},{'a':'b','b':'a','c':'c'},{'a':'b','b':'a','c':'d','d':'c'}]
rng = random.Random(int(sys.argv[2])); n = 0
for trial in range(int(sys.argv[3])):
    cm = INV[trial % len(INV)]; rho = make_rho(cm); al = sorted(cm)
    X = ''.join(rng.choice(al) for _ in range(rng.randrange(1, 4)))
    tx = (X + rho(X)) * 6 if rng.randrange(2) else ''.join(rng.choice(al) for _ in range(14))
    words = []
    for _ in range(rng.randrange(1, 4)):
        a = rng.randrange(len(tx) - 2); words.append(tx[a:a + rng.randrange(2, 10)])
    mine = counts(words, cm, 'broad')['m']
    theirs = mod.compute(words, cm, True)[3]
    mine = {k: v for k, v in mine.items() if k}
    assert mine == theirs, (words, cm)
    n += 1
print(json.dumps(dict(agree=n)))
