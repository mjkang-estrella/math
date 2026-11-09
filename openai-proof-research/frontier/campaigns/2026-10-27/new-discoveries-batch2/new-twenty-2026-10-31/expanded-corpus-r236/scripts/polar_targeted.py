"""Targeted census for Conjecture 1 of arXiv:2104.07852 (uniqueness of cograph minimal (inf,k)-polar obstructions
of type (c,i), 1 <= i <= c-2 <= k).  By the source's Lemma 5 (items 4,5), such an obstruction has the form
G = iK1 + tK2 + H with H connected (H = K2 allowed only as one more K2 component), c = i + t + 1.
We enumerate ALL connected cographs H with 2 <= |H| <= HMAX (canonical cotrees), every k <= KMAX, every
(c,i) in range, and test minimality exactly with the cotree DP of polar_cographs.py (imported by path).
Also compares each found obstruction with the predicted graph
  P(k,c,i) = iK1 + (c-i-1)K2 + X,  X = K_{i,i} (c=k+2), 2K1 (+) (K2 + iK1) (c=k+1),
                                   K1 (+) ((k-c+2)K2 + iK1) (c<=k).
Usage: polar_targeted.py HMAX KMAX OUT_JSON SCRIPTDIR"""
import sys, json, importlib.util, itertools
HMAX, KMAX, OUT, SD = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
sys.argv = ['polar_cographs.py', str(HMAX), '0', '0', '/dev/null']
spec = importlib.util.spec_from_file_location('pc', SD + '/polar_cographs.py')
# polar_cographs runs a census on import; with KMAX=0 and BRUTE=0 it is cheap but writes to /dev/null only.
pc = importlib.util.module_from_spec(spec); spec.loader.exec_module(pc)
pc.CAP = 10 ** 6; pc.states.cache_clear()   # no clique-count cap in this run
V, mk, polar_inf, polar_one, deletions, show = pc.V, pc.mk, pc.polar_inf, pc.polar_one, pc.deletions, pc.show
K2 = ('J', (V, V))
def union(parts): return mk('U', parts)
def join(parts): return mk('J', parts)
def predicted(k, c, i):
    if c == k + 2:
        X = join([union([V] * i), union([V] * i)]) if i >= 2 else K2
    elif c == k + 1:
        X = join([union([V, V]), union([K2] + [V] * i)])
    else:
        X = join([V, union([K2] * (k - c + 2) + [V] * i)])
    return union([V] * i + [K2] * (c - i - 1) + [X])
def is_min_obs(g, k):
    return (not polar_inf(g, k)) and all(d is None or polar_inf(d, k) for d in pc.deletions(g))
res = {}; mismatches = []
Hs = [h for n in range(2, HMAX + 1) for h in pc.conn[n]]
print('connected H count', len(Hs), flush=True)
for k in range(1, KMAX + 1):
    for c in range(3, k + 3):
        for i in range(1, c - 1):
            t = c - i - 1
            found = []
            for h in Hs:
                g = union([V] * i + [K2] * t + [h])
                if is_min_obs(g, k):
                    found.append(show(g))
            p = predicted(k, c, i)
            pmin = is_min_obs(p, k)
            res[f'k={k} type=({c},{i})'] = {'found': found, 'predicted': show(p), 'predicted_is_min_obs': pmin,
                                            'predicted_order': pc.size(p), 'search_order_max': i + 2 * t + HMAX}
            ok = pmin and found == [show(p)] if pc.size(p) <= i + 2 * t + HMAX else pmin and len(found) == 0
            if not ok:
                mismatches.append(f'k={k} ({c},{i})')
            print(f'k={k} (c,i)=({c},{i}) found={len(found)} predicted_min={pmin} predicted_order={pc.size(p)} '
                  f'covered_order<={i + 2 * t + HMAX} ok={ok}', flush=True)
json.dump({'HMAX': HMAX, 'KMAX': KMAX, 'results': res, 'mismatches': mismatches}, open(OUT, 'w'), indent=1)
print('mismatches', mismatches)
