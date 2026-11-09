import sys, pathlib, itertools
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import castel3 as C
cube = [p for p in itertools.product((-1, 1), repeat=3)]
print('cube', C.analyse(cube), 'expect b=26 c=1 vol6=48')
ex35 = [(-1,-1,1),(2,-1,1),(-1,2,1),(-1,-1,-1),(2,-1,-1),(-1,2,-1)]
print('ex3.5', C.analyse(ex35), 'expect b=29 c=1 vol6=54')
for c in (1, 2, 3):
    w = (-1, -1, 0)
    Q = [(1,0,0),(0,1,0),w,(1,0,c+1),(0,1,c+1),(w[0],w[1],c+1)]
    r = C.analyse(Q); print('Q(c)', c, r, 'expect b', 3*c+8, 'castelnuovo', r[2] == 3*r[1] + 2*r[0] - 7)
for c, n in ((2, 0), (2, 3), (3, 5)):
    d = 3
    P = [(0,0,0),(1,0,0),(0,1,0),(n,n,n+1),(c*d,c*d,c*d+1)]
    r = C.analyse(P); print('P_cd(n)', c, n, r, 'expect b', c*d-n+d+1, 'castelnuovo', r[2] == 3*r[1] + 2*r[0] - 7)
