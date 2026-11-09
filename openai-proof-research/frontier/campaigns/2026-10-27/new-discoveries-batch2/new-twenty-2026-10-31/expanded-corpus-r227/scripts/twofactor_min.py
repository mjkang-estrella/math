"""365134 structure probe: over all cubic (multi)graphs on Hamilton path 0..n-1 (labelled completions),
min number of cycles in a 2-factor; report graphs whose every 2-factor has >= 3 cycles (Theorem 4 of
the source then does not apply), split by 3-edge-colourability.
Usage: twofactor_min.py LANE N MULTI CHUNK NCH"""
import sys, json, pathlib
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N
from hpgen import completions
n = int(sys.argv[2]); multi = sys.argv[3] == '1'; chunk = int(sys.argv[4]); nch = int(sys.argv[5])
hist = {}; bad = []; badnc = 0
for extra in completions(n, multi, chunk, nch):
    E = [(i, i + 1) for i in range(n - 1)] + extra
    inc = N.adjacency(n, E); best = 99; colourable = False
    for F in N.perfect_matchings(n, E, inc):
        cyc = N.cycles_of(n, E, inc, set(F))
        best = min(best, len(cyc))
        if all(len(C) % 2 == 0 for C in cyc): colourable = True
        if best <= 2 and colourable: break
    if not colourable and not N.bridgeless(n, E):
        hist['bridged'] = hist.get('bridged', 0) + 1; continue
    key = f'{min(best, 3)}{"c" if colourable else "n"}'
    hist[key] = hist.get(key, 0) + 1
    if best >= 3 and not colourable:
        badnc += 1
        if len(bad) < 5: bad.append(E)
print(json.dumps({'n': n, 'multi': multi, 'chunk': chunk, 'nch': nch, 'hist(min cycles capped 3; c=colourable, n=not)': hist,
                  'noncolourable_with_all_2factors_ge3_cycles': badnc, 'examples': bad}))
