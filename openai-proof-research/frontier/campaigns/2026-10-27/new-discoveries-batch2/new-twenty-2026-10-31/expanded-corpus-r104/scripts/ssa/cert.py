# Build exact integer Collatz-Wielandt certificates for m=5.
# Lower: for w in S, q*sum_{c: shift(w,c) in S} v(shift) >= p*v(w)  (lambda=p/q)
# Upper: for w in TC, q*sum_{c: shift(w,c) in TC} u(shift) <= p*u(w), u>0  (mu=p/q)
import itertools,json,numpy as np,sys,hashlib
from fractions import Fraction
D=sys.argv[1]
al='ACGT'; comp={'A':'T','T':'A','C':'G','G':'C'}
rc=lambda w:''.join(comp[c] for c in reversed(w))
words=[''.join(t) for t in itertools.product(al,repeat=5)]
S=set(open(D+'/outputs/ssa5-best-set.txt').read().split())
TC={w for w in words if sum(c in 'TC' for c in w)>=3}
for X in (S,TC):
    assert len(X)==512 and all(rc(w) not in X for w in X) and all((w in X) or (rc(w) in X) for w in words)
succ=lambda w:[w[1:]+c for c in al]
def mat(X):
    L=sorted(X); ix={w:i for i,w in enumerate(L)}; A=np.zeros((len(L),len(L)))
    for w in L:
        for y in succ(w):
            if y in X: A[ix[w],ix[y]]=1
    return L,ix,A
LS,ixS,AS=mat(S); LT,ixT,AT=mat(TC)
ev,evec=np.linalg.eig(AS); k=np.argmax(ev.real); rhoS=ev[k].real; v=np.abs(evec[:,k].real); v/=v.max()
rhoT=max(abs(np.linalg.eigvals(AT)))
lam=Fraction(1299,400); mu=Fraction(649,200)
print('rhoS',rhoS,'rhoT',rhoT,'lam',float(lam),'mu',float(mu)); assert rhoT<mu<lam<rhoS
K=10**6
vi={w:int(np.floor(K*v[ixS[w]])) for w in LS}
changed=True; rounds=0
while changed:
    changed=False; rounds+=1
    for w in LS:
        s=sum(vi[y] for y in succ(w) if y in S)
        if lam.denominator*s < lam.numerator*vi[w]:
            vi[w]=(lam.denominator*s)//lam.numerator; changed=True
assert all(lam.denominator*sum(vi[y] for y in succ(w) if y in S) >= lam.numerator*vi[w] for w in LS)
print('lower rounds',rounds,'sum',sum(vi.values()),'max',max(vi.values()),'zeros',sum(1 for x in vi.values() if x==0))
u=np.linalg.solve(float(mu)*np.eye(len(LT))-AT,np.ones(len(LT))); assert (u>0).all()
Ku=10**3
ui={w:int(np.ceil(Ku*u[ixT[w]])) for w in LT}
ok=all(mu.denominator*sum(ui[y] for y in succ(w) if y in TC) <= mu.numerator*ui[w] for w in LT)
print('upper ok',ok,'min',min(ui.values()),'max',max(ui.values()),'sum',sum(ui.values()))
assert ok
out=dict(lam=[lam.numerator,lam.denominator],mu=[mu.numerator,mu.denominator],S=sorted(S),v=vi,u=ui,rhoS_float=float(rhoS),rhoTC_float=float(rhoT))
s=json.dumps(out,indent=1,sort_keys=True); open(D+'/outputs/ssa5-certificate.json','w').write(s+'\n')
print('sha256',hashlib.sha256((s+'\n').encode()).hexdigest())
