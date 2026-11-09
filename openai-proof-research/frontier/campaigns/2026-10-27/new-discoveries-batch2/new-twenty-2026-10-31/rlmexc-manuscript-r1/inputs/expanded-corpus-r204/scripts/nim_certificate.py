"""Certificate for the refutation of the GM-strategy Nash-equilibrium conjecture for exact slow NIM(n,n-1)
(Gurvich-Naumova, arXiv:2311.03257 Conj. 1 = arXiv:2312.08382 Conj. 1; MathDB 360653 / 361128).
Part A: instance n=3, l=3, x0=(4,4,5), player P0 (= 'player 1' in 1-based naming) moves first.
Part B: convention-free instance n=3, l=3, x0=(5,5,6): every position at which a non-deviating player moves
        contains a multiple of l, so the 'no multiple -> keep largest' clause is never used.
Every move is checked for legality (the reduced n-1 entries are positive) and every GM move is recomputed."""
import json
def terminal(x): return sum(1 for v in x if v <= 0) >= 2
def legal(x, i): return all(x[j] > 0 for j in range(len(x)) if j != i)
def apply(x, i): return tuple(sorted(x[j] - (j != i) for j in range(len(x))))
def gm_index(x, l):
    mult = [v for v in x if v % l == 0]
    keep = min(mult) if mult else max(x)
    return max(i for i in range(len(x)) if x[i] == keep), bool(mult)   # rightmost minimal multiple
def run(x0, l, deviator, dev_moves):
    """dev_moves: dict position -> kept value used by the deviator at that position (else GM)."""
    x, t, rows = tuple(sorted(x0)), 0, []
    while not terminal(x):
        p = t % l
        if p == deviator and x in dev_moves:
            i = x.index(dev_moves[x]); used_conv = None; who = 'deviation'
        else:
            i, has_mult = gm_index(x, l); used_conv = not has_mult; who = 'GM'
        assert legal(x, i)
        rows.append(dict(t=t, mover=p, position=x, keeps=x[i], rule=who, convention_used=used_conv))
        x = apply(x, i); t += 1
    rows.append(dict(t=t, mover=t % l, position=x, terminal=True))
    return dict(length=t, loser=t % l, play=rows)
def payoff(res, player, l, C):
    L = res['length']; return -(C - L) if res['loser'] == player else (C - L) / (l - 1)
out = {}
# Part A
gmA = run((4, 4, 5), 3, 0, {}); devA = run((4, 4, 5), 3, 0, {(4, 4, 5): 4})
assert gmA['length'] == 6 and gmA['loser'] == 0 and devA['length'] == 5 and devA['loser'] == 2
C = 7   # any C > 6 (sum 13, each move removes 2, so every play from (4,4,5) has length <= 6)
out['A'] = dict(n=3, l=3, x0=(4, 4, 5), C_example=C, gm=gmA, deviation=devA,
                payoff_gm=payoff(gmA, 0, 3, C), payoff_dev=payoff(devA, 0, 3, C))
# Part B: x0=(5,5,6), l=3.  The all-GM play never meets a position without a multiple of l.  The deviator's guaranteed
# value is computed by min-max: at positions WITHOUT a multiple of l, a non-deviating player's move is chosen
# adversarially among ALL legal moves (so the result holds for every completion of the GM rule); at positions with a
# multiple, the GM move is forced.
import functools
l = 3
def moves(x): return sorted({apply(x, i) for i in range(len(x)) if legal(x, i)})
def val(win, r): return (1, -r) if win else (0, r)
@functools.lru_cache(None)
def guar(x, p):
    if terminal(x): return val(p != 0, 0), 0, p
    if p == 0: nxt, agg = moves(x), max
    elif not any(v % l == 0 for v in x): nxt, agg = moves(x), min
    else: nxt, agg = [apply(x, gm_index(x, l)[0])], max
    c = []
    for y in nxt:
        k, r, los = guar(y, (p + 1) % l); c.append((val(los != 0, r + 1), r + 1, los))
    return agg(c)
x0 = (5, 5, 6); gmB = run(x0, l, 0, {})
gm_conv_free = all(r.get('convention_used') is False for r in gmB['play'] if r.get('rule') == 'GM')
gk = val(gmB['loser'] != 0, gmB['length']); bk, br, bl = guar(x0, 0)
assert gm_conv_free and bk > gk
# one optimal deviator move tree is not unique; record the deviator's first move(s) achieving the guarantee
firsts = [x0[i] for i in range(3) if legal(x0, i) and val(guar(apply(x0, i), 1)[2] != 0, guar(apply(x0, i), 1)[1] + 1) == bk]
out['B'] = dict(n=3, l=3, x0=x0, gm=gmB, gm_convention_free=gm_conv_free, gm_value=gk,
                deviator_guaranteed_value=bk, guaranteed_len=br, guaranteed_loser=bl, optimal_first_keeps=firsts,
                note='value (1,-L) = win with play length L; the deviator (P0) wins in the all-GM play with length 8 and can force a win with length 7 against every completion of the GM rule')
print(json.dumps(out, indent=1, default=list))
