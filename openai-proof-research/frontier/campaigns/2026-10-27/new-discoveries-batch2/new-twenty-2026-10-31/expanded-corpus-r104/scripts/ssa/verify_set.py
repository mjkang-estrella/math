import sys,numpy as np,json
m=5; al='ACGT'; comp={'A':'T','T':'A','C':'G','G':'C'}
def rc(w): return ''.join(comp[c] for c in reversed(w))
def rho(S):
    S=sorted(S); idx={w:i for i,w in enumerate(S)}; n=len(S); A=np.zeros((n,n))
    for w in S:
        for c in al:
            y=w[1:]+c
            if y in idx: A[idx[w],idx[y]]=1
    ev=np.linalg.eigvals(A); return max(abs(ev)), A
def check_valid(S):
    S=set(S); assert all(rc(w)!=w for w in S)
    assert not any(rc(w) in S for w in S); return len(S)
log=sys.argv[1]
S=[l for l in open(log) if l.startswith('SET ')][0].split()[1:]
print('size',check_valid(S)); r,_=rho(S); print('rho',r,'rate',np.log2(r))
import itertools
TC=[''.join(t) for t in itertools.product(al,repeat=m) if sum(c in 'TC' for c in t)>m/2]
print('TC size',check_valid(TC)); r2,_=rho(TC); print('TC rho',r2,np.log2(r2))
