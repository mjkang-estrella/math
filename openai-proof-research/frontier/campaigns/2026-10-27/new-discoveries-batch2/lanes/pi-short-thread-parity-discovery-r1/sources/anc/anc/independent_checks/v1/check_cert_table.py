"""Compute z0(x,y) = least z0 with g(S(x,y,z)) = z mod 2 for z0<=z<=ZMAX using the referee's C++ solver,
and compare with Table tab:cert (and tab:families)."""
import subprocess, sys, resource
ZMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 600

rows = {
 1: {3: 14, 5: 28, 7: 34, 9: 56, 11: 22, 13: 68},
 2: {3: 14, 4: 1, 5: 28, 6: 1, 7: 34, 8: 4, 9: 56, 10: 4, 11: 22, 12: 8, 13: 68, 14: 8},
 3: {4: 15, 5: 26, 6: 13, 7: 32, 8: 15, 9: 54, 10: 25, 11: 10, 12: 23, 13: 66, 14: 29},
 4: {5: 30, 6: 16, 7: 34, 8: 16, 9: 58, 10: 24, 11: 25, 12: 24, 13: 70, 14: 32},
 5: {6: 26, 7: 34, 8: 29, 9: 50, 10: 27, 11: 21, 12: 28, 13: 64, 14: 31},
 6: {7: 30, 8: 16, 9: 54, 10: 28, 11: 29, 12: 30, 13: 62, 14: 28},
 7: {8: 31, 9: 32, 10: 29, 11: 21, 12: 28, 13: 64, 14: 33},
 8: {9: 52, 10: 32, 11: 26, 12: 34},
 9: {10: 54, 11: 54, 12: 53},
 10: {11: 33, 12: 32},
 11: {12: 40},
}
x2 = "15:74 16:12 17:112 18:12 19:30 20:16 21:44 22:16 23:50 24:20 25:136 26:20 27:38 28:24 29:148 30:24 31:154 32:28 33:224 34:28 35:46 36:32 37:60 38:32 39:66 40:36"
for tok in x2.split():
    y, z0 = map(int, tok.split(':'))
    rows[2][y] = z0
pairs = sorted((x, y) for x in rows for y in rows[x])
print('pairs in Table tab:cert:', len(pairs))

resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
bad = 0
out = []
for (x, y) in pairs:
    res = subprocess.run(['nice', './spider3', str(x), str(y), str(ZMAX)], capture_output=True, text=True, check=True)
    g = [None] + list(map(int, res.stdout.split('\n')[0].split()[1:]))
    viol = [z for z in range(1, ZMAX + 1) if g[z] != z % 2]
    z0 = max(viol) + 1 if viol else 1
    ok = z0 == rows[x][y]
    bad += not ok
    out.append('(%d,%d): z0=%d table=%d %s  maxg=%d' % (x, y, z0, rows[x][y], 'OK' if ok else '*** MISMATCH', max(g[1:])))
    print(out[-1], flush=True)
print('mismatches:', bad)
