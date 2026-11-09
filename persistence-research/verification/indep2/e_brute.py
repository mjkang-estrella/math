# Agent E: lattice brute force.  All n = 2^i 3^j 7^k < 10^LMAX (5-free), digit product read off str(n).
import sys, json
from multiprocessing import Pool
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
LIM = 10 ** LMAX
TGT = {}
for p in (12, 14, 16, 18, 21, 24, 32, 42, 81, 112, 14112, 111132):
    e = [0, 0, 0]; x = p
    for idx, q in enumerate((2, 3, 7)):
        while x % q == 0: x //= q; e[idx] += 1
    assert x == 1; TGT[tuple(e)] = p
def work(j):
    out = []; base3 = 3 ** j; cnt = 0
    if base3 >= LIM: return out, 0
    b = base3; 
    while b < LIM:
        n = b
        while n < LIM:
            s = str(n); cnt += 1
            if '0' not in s and '5' not in s:
                c = s.count
                c2, c3, c4, c6, c7, c8, c9 = c('2'), c('3'), c('4'), c('6'), c('7'), c('8'), c('9')
                e = (c2 + 2 * c4 + c6 + 3 * c8, c3 + c6 + 2 * c9, c7)
                if e in TGT and len(s) > 1: out.append((TGT[e], len(s), s))
            n *= 2
        b *= 7
    return out, cnt
if __name__ == '__main__':
    res = []
    with Pool(30) as P:
        tot = 0
        for r, c in P.imap_unordered(work, range(int(LMAX * 2.1) + 2), chunksize=1): res.extend(r); tot += c
    print('numbers 2^i3^j7^k < 10^%d scanned:' % LMAX, tot)
    res.sort(key=lambda t: (t[0], t[1], t[2]))
    json.dump(res, open(f'e_brute_{LMAX}.json', 'w'))
    for p, L, s in res:
        if p in (112, 14112, 111132): print(p, L, s)
    print('total level1-type members found', len(res))
