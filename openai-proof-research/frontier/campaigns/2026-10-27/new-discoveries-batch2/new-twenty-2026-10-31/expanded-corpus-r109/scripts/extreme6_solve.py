# Numerical extremality test for filtered six-sets (diagnostic): find unimodular masses u (u_0=1) with
# sum_{a-b=d} u_a conj(u_b) = 0 for all nonzero d in Z_n. Random multistart least squares.
import sys, json, numpy as np
from scipy.optimize import least_squares
rng=np.random.default_rng(109)
def classes(n,E):
    cl={}
    for i,a in enumerate(E):
        for j,b in enumerate(E):
            if i!=j: cl.setdefault((a-b)%n,[]).append((i,j))
    # keep one representative of {d,-d}
    keep=[cl[d] for d in sorted(cl) if d<=(n-d)%n or (n-d)%n not in cl]
    return keep
def solve(n,E,starts=int(__import__("os").environ.get("STARTS","60"))):
    cl=classes(n,E)
    I=np.array([i for c in cl for i,j in c]); J=np.array([j for c in cl for i,j in c])
    G=np.array([k for k,c in enumerate(cl) for _ in c]); K=len(cl)
    def res(th):
        t=np.concatenate([[0.0],th]); v=np.exp(1j*(t[I]-t[J]))
        s=np.zeros(K,complex); np.add.at(s,G,v)
        return np.concatenate([s.real,s.imag])
    best=(1e9,None)
    for _ in range(starts):
        x0=rng.uniform(0,2*np.pi,5); sol=least_squares(res,x0,xtol=1e-14,ftol=1e-14,gtol=1e-14)
        c=float(np.sum(sol.fun**2))
        if c<best[0]: best=(c,sol.x)
        if c<1e-20: break
    return best
out=[]
lines=[l for l in open(sys.argv[1]) if l.startswith('SET')]
lo,hi=int(sys.argv[3]),int(sys.argv[4])
for line in lines:
    if not lo<=int(line.split()[1])<=hi: continue
    if not line.startswith('SET'): continue
    v=list(map(int,line.split()[1:])); n,E=v[0],v[1:]
    c,x=solve(n,E)
    rec={'n':n,'E':E,'min_cost':c,'phases_over_2pi':None if x is None else [0.0]+list((x/(2*np.pi))%1)}
    out.append(rec)
    if c<1e-12: print('EXTREME?',n,E,c,[round(t,6) for t in rec['phases_over_2pi']],flush=True)
json.dump(out,open(sys.argv[2],'w'),indent=1)
print('tested',len(out),'numerically extreme',sum(r['min_cost']<1e-12 for r in out))
