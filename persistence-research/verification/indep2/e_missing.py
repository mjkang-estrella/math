import json, glob, os, collections, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e_enum import *
C = '../glm/L2c/'
certs = {}
for f in sorted(glob.glob(C + 'cert_t*.jsonl')):
    certs[os.path.basename(f)] = json.loads(open(f).readline())
bykey = collections.defaultdict(list)
for f, m in certs.items(): bykey[(m['K'], tuple(m['coefs']), m['target'])].append((f, m))
missing = {}   # (T,K',coefs,qmin) -> list of configs
other_missing = []
tot_need = collections.Counter(); found = collections.Counter()
for T in TARGETS:
    for k, v in configs(T).items():
        if v['dead40'] or len(k[1]) >= 3: continue
        for (Kp, F, qmin, fixed) in slices(9 * k[0] - 1, k[1]):
            for pm in (perms(F) if F else [()]):
                tot_need[T] += 1
                good = [1 for f, m in bykey.get((Kp, tuple(pm), T), []) if m['qmin'] <= qmin and m['qmin'] > v2(Kp) and m['root']['m'] == 1]
                if good: found[T] += 1
                else:
                    kk = (T, Kp, tuple(pm), qmin)
                    missing.setdefault(kk, []).append((k, fixed))
                    if len(set(F)) < 2 or not bykey.get((Kp, tuple(reversed(pm)), T)): other_missing.append((kk, k))
print('need', dict(tot_need), 'found', dict(found))
print('distinct missing (T,K,coefs,qmin):', len(missing))
print('missing whose reverse-ordered sibling is NOT certified either / or F not 2-distinct:', len(other_missing), other_missing[:10])
for kk in sorted(missing): print(kk, missing[kk][:2])
json.dump([[list(map(lambda x: list(x) if isinstance(x,tuple) else x, kk)), len(v)] for kk, v in missing.items()], open('e_missing.json', 'w'))
