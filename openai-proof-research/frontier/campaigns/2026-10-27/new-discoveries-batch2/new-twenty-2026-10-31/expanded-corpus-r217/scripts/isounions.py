import sys, itertools, importlib.util, pathlib
spec = importlib.util.spec_from_file_location('isogame', str(pathlib.Path(sys.argv[0]).resolve().parent / 'isogame.py'))
iso = importlib.util.module_from_spec(spec); spec.loader.exec_module(iso)
sys.setrecursionlimit(10000)
def path(n):
    a=[0]*n
    for i in range(n-1): a[i]|=1<<(i+1); a[i+1]|=1<<i
    return a
def cyc(n):
    a=path(n); a[0]|=1<<(n-1); a[n-1]|=1; return a
comps = {'P5':path(5), 'X5':[20,24,17,2,7], 'P3':path(3), 'C3':cyc(3), 'P6':path(6), 'C6':cyc(6), 'P4':path(4)}
def union(gs):
    adj=[]; off=0
    for g in gs:
        n=len(g); adj += [m<<off for m in g]; off+=n
    return off, adj
names=['P5','X5','P3','C3','P6','C6','P4']
for k in (2,3):
    for combo in itertools.combinations_with_replacement(names,k):
        if not any(c in ('P5','X5') for c in combo): continue
        n, adj = union([comps[c] for c in combo])
        if n > 15: continue
        d, s = iso.solve(n, adj)
        flag = 'VIOLATION' if 3*d > 2*n else ''
        print(combo, 'n', n, 'D', d, 'S', s, 'bound', round(2*n/3,2), flag, flush=True)
