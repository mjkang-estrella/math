# Validate crystal2 against paper Theorem 6.6 / Corollary 6.8: K_{lam,mu}(t) = sum_{alpha in S^{id}, phi_i(alpha)=0 all i} t^{|alpha|}
import sys, json, itertools
sys.path.insert(0, __import__('os').path.dirname(__file__))
from crystal2 import Model
n=int(sys.argv[1]); maxsize=int(sys.argv[2])
M=Model(n); rho=list(range(n-1,-1,-1))
def KF(lam,mu):
    # alternating formula over W=S_n
    out={}
    for w in itertools.permutations(range(n)):
        sgn=1
        for i in range(n):
            for j in range(i+1,n):
                if w[i]>w[j]: sgn=-sgn
        v=[lam[w[i]]+rho[w[i]] for i in range(n)]   # w(lam+rho): coordinate i gets (lam+rho)_{w(i)}
        g=[v[i]-mu[i]-rho[i] for i in range(n)]
        if sum(g)!=0: continue
        for al in M.kostant(g):
            t=sum(al); out[t]=out.get(t,0)+sgn
    return {k:v for k,v in sorted(out.items()) if v}
def FP(lam,mu):
    g=[lam[i]-mu[i] for i in range(n)]; out={}
    k=[lam[i]+rho[i]-lam[i+1]-rho[i+1] for i in range(n-1)]
    for al in M.kostant(g):
        if all(M.epow(al,i,k[i-1]) is None for i in range(1,n)):
            t=sum(al); out[t]=out.get(t,0)+1
    return dict(sorted(out.items()))
def parts(total,n):
    for c in itertools.combinations_with_replacement(range(total,-1,-1),n):
        if sum(c)==total and list(c)==sorted(c,reverse=True): yield list(c)
ok=0;bad=[];tested=0
for total in range(1,maxsize+1):
    P=list(parts(total,n))
    for lam in P:
        for mu in P:
            # dominance lam >= mu
            if not all(sum(lam[:i])>=sum(mu[:i]) for i in range(1,n+1)): continue
            tested+=1
            a=KF(lam,mu); b=FP(lam,mu)
            if a==b: ok+=1
            else: bad.append(dict(lam=lam,mu=mu,KF=a,FP=b))
print(json.dumps(dict(n=n,maxsize=maxsize,tested=tested,ok=ok,bad_count=len(bad),bad_first=bad[:5])))
