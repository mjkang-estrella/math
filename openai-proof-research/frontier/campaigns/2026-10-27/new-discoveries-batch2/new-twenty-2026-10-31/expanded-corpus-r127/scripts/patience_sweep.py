# Sweep all evaluations (a_1..a_n), a_i>=1, n fixed, sum <= Lmax: diameter of the K(rps) component vs n-1 and 2n-4.
import sys, json, time, itertools, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from patience import component
from math import factorial
def evals(n,L):
    if n==0:
        if L==0: yield ()
        return
    for a in range(1,L-n+2):
        for r in evals(n-1,L-a): yield (a,)+r
n=int(sys.argv[1]); Lmin=int(sys.argv[2]); Lmax=int(sys.argv[3]); maxwords=int(sys.argv[4]); t0=time.time()
for L in range(Lmin,Lmax+1):
    for ev in evals(n,L):
        nw=factorial(L)
        for a in ev: nw//=factorial(a)
        if nw>maxwords: continue
        v,d=component(ev)
        print(json.dumps({'n':n,'evaluation':ev,'words':nw,'vertices':v,'diameter':d,'below_n_minus_1':d is not None and d<n-1,'above_2n_minus_4':d is not None and d>2*n-4}),flush=True)
        if time.time()-t0>105: print(json.dumps({'stopped_time':True,'at':ev})); sys.exit()
print(json.dumps({'done':True}))
