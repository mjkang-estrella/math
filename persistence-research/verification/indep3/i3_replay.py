# Agent E2: coverage replay.  Every brute-force member with >= 3 digits must lie in a NON-dead configuration; report which cert domain records it.
import json, sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i3_enum import *
mem = {}
for p, L, s in json.load(open('i3_brute_300.json')): mem.setdefault(p, []).append(int(s))
mem[15] = json.load(open('i3_brute15_300.json'))
gt = {12:[126,162,216,1134,13122],14:[27,72],15:[35,135,315],16:[28,128,144,224,441],18:[36,63,192,1323],24:[64,243,324,432,4116],32:[48,84],42:[1176,1372,131712],21:[],81:[]}
ok = True
for T in TARGETS:
    if sorted(mem.get(T, [])) != gt[T]: print('GROUND TRUTH MISMATCH', T, mem.get(T), gt[T]); ok = False
    cf = configs(T)
    for n in mem.get(T, []):
        s = str(n)[::-1]; L = len(s)
        if L < 3: print(T, n, 'L<3 (brute-force region only)'); continue
        digs = [int(c) for c in s]
        S_low = sum((d - 1) * 10 ** p for p, d in enumerate(digs[:3]))
        far = tuple(sorted(9 * (d - 1) for d in digs[3:] if d != 1))
        key = (S_low, far); v = cf.get(key)
        assert v is not None, (T, n, key)
        prod = 1
        for d in digs: prod *= d
        assert prod == T
        print(T, n, 'S_low', S_low, 'far A', far, 'dead_weak', v['dead_weak'], 'dead_strong', v['dead_strong'])
        if v['dead_weak']: ok = False; print('   !!! member in a parity-dead config')
print('REPLAY', 'OK' if ok else 'FAIL')
