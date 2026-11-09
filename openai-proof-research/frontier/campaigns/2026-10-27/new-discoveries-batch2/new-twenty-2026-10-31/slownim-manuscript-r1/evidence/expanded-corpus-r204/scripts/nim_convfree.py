"""Search for convention-free one-shot GM deviations in exact slow NIM(n,n-1), l players: x0 contains a multiple of l;
the first mover P0 makes a non-GM first move, then everyone (P0 included) plays GM; in both plays no GM mover ever faces a
position without a multiple of l (so the 'keep largest' clause is never invoked), and P0's payoff strictly improves
(lose->win, or win->win shorter, or lose->lose longer).  usage: nim_convfree.py n l B"""
import sys, itertools, json
n, l, B = map(int, sys.argv[1:4])
def terminal(x): return sum(1 for v in x if v <= 0) >= 2
def legal(x, i): return all(x[j] > 0 for j in range(n) if j != i)
def apply(x, i): return tuple(sorted(x[j] - (j != i) for j in range(n)))
def gmplay(x, t0):
    t = t0
    while not terminal(x):
        if not any(v % l == 0 for v in x): return None
        keep = min(v for v in x if v % l == 0); x = apply(x, x.index(keep)); t += 1
    return t
def key(win, L): return (1, -L) if win else (0, L)
found = []
for x0 in itertools.combinations_with_replacement(range(B + 1), n):
    if terminal(x0) or not any(v % l == 0 for v in x0): continue
    G = gmplay(x0, 0)
    if G is None: continue
    gk = key(G % l != 0, G)
    gi = x0.index(min(v for v in x0 if v % l == 0))
    for i in range(n):
        if not legal(x0, i) or x0[i] == x0[gi]: continue
        D = gmplay(apply(x0, i), 1)
        if D is None: continue
        dk = key(D % l != 0, D)
        if dk > gk:
            found.append(dict(x0=x0, dev_keep=x0[i], gm_len=G, gm_loser=G % l, dev_len=D, dev_loser=D % l,
                              type='L2W' if G % l == 0 else ('SHORT' if D % l != 0 else 'LONG')))
found.sort(key=lambda d: (sum(d['x0']), d['x0']))
print(json.dumps(dict(n=n, l=l, B=B, count=len(found), smallest=found[:6], L2W=[f for f in found if f['type'] == 'L2W'][:6])))
