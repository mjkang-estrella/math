import sys, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
from crystal2 import Model
n=int(sys.argv[1]); S=int(sys.argv[2]); M=Model(n)
def comps(t,k):
    if k==1: yield (t,); return
    for a in range(t+1):
        for r in comps(t-a,k-1): yield (a,)+r
def eps(x,i):
    c=0
    while True:
        x,_=M.e(x,i)
        if x is None: return c
        c+=1
def walk(x,seq):
    for j in seq:
        x,_=M.e(x,j)
        if x is None: return None
    return x
st=dict(n=n,maxsize=S,instances=0,thm53_fail=0,case2a=0,case2b=0,bd_then_blocked=0,bd_any=0)
ex=[]
for size in range(1,S+1):
    for al in comps(size,len(M.roots)):
        g=M.weight(al)
        for i in range(1,n-1):
            ei,ej=eps(al,i),eps(al,i+1)
            for ki in range(max(1,g[i-1]-g[i]+1),ei+1):
                for kj in range(max(1,g[i]-g[i+1]+1),ej+1):
                    st['instances']+=1
                    A={}
                    for (a,b,ka,kb) in ((i,i+1,ki,kj),(i+1,i,kj,ki)):
                        A[(a,b)]=eps(walk(al,[b]*kb),a)<ka+kb
                    nA=sum(A.values())
                    if nA==2:
                        st['thm53_fail']+=1; st.setdefault('both_2a',0); st['both_2a']+=1
                        if len(ex)<5: ex.append(dict(kind='both orders in 2a',alpha={f'{r[0]},{r[1]}':c for c,r in zip(al,M.roots) if c},i=i,k_i=ki,k_i1=kj))
                    for (a,b,ka,kb) in ((i,i+1,ki,kj),(i+1,i,kj,ki)):
                        if A[(a,b)]:
                            st['case2a']+=1
                            ok=(walk(al,[b]*kb+[a]*(ka+kb)) is None and walk(al,[b]*kb+[a]*(ka+kb)+[b]*ka) is None
                                and walk(al,[a]*ka+[b]*(ka+kb)+[a]*kb) is None and walk(al,[a]*ka+[b]*(ka+kb)) is not None)
                        elif nA==0:
                            st['case2b']+=1
                            p_=walk(al,[b]*kb+[a]*(ka+kb)+[b]*ka); q=walk(al,[a]*ka+[b]*(ka+kb)+[a]*kb)
                            ok=(p_ is not None and p_==q)
                        else: ok=True
                        if not ok:
                            st['thm53_fail']+=1
                            if len(ex)<5: ex.append(dict(kind='2a' if A[(a,b)] else '2b',alpha={f'{r[0]},{r[1]}':c for c,r in zip(al,M.roots) if c},i=a,j=b,k_i=ka,k_j=kb))
                    for seq in ([i]*ki+[i+1]*(ki+kj)+[i]*kj,[i+1]*kj+[i]*(ki+kj)+[i+1]*ki):
                        x=al; flag=False; flag2=False
                        for j in seq:
                            bd=M.BD(x,i,i+1)
                            y,bl=M.e(x,j)
                            if bd: flag=True
                            if bd and y is not None:
                                z_other=[o for o in (i,i+1) if o!=j][0]
                                if M.e(y,z_other)[1]: flag2=True
                            if y is None: break
                            x=y
                        st['bd_any']+=flag; st['bd_then_blocked']+=flag2
    print(json.dumps(dict(size=size,**st)),flush=True)
print(json.dumps(dict(final=st,thm53_fail_examples=ex)))
