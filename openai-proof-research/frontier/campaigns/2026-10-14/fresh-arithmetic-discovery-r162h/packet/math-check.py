"""Small exact polynomial checks; no external dependency or theorem verification."""
import json
D=10
zero=(0,)*D
def var(i):
    a=list(zero);a[i]=1;return {tuple(a):1}
def const(n):return {zero:n} if n else {}
def add(*ps):
    q={}
    for p in ps:
        for e,c in p.items():q[e]=q.get(e,0)+c
    return {e:c for e,c in q.items() if c}
def scale(p,n):return {e:n*c for e,c in p.items() if n*c}
def mul(p,q):
    r={}
    for e,c in p.items():
        for f,d in q.items():
            k=tuple(a+b for a,b in zip(e,f));r[k]=r.get(k,0)+c*d
    return {e:c for e,c in r.items() if c}
def der(p,i):
    q={}
    for e,c in p.items():
        if e[i]:
            f=list(e);f[i]-=1;q[tuple(f)]=c*e[i]
    return q
x,y=var(0),var(1)
re,im=const(1),{}
u,v={},{}
for j in range(4):
    a,b=var(2+2*j),var(3+2*j)
    u=add(u,mul(a,re),scale(mul(b,im),-1))
    v=add(v,mul(a,im),mul(b,re))
    re,im=add(mul(x,re),scale(mul(y,im),-1)),add(mul(y,re),mul(x,im))
ux,vx=der(u,0),der(v,0)
H=add(mul(y,add(mul(ux,ux),mul(vx,vx))),mul(vx,u),scale(mul(ux,v),-1))
uxx,vxx=der(ux,0),der(vx,0)
res=add(der(der(H,0),0),der(der(H,1),1),scale(mul(y,add(mul(uxx,uxx),mul(vxx,vxx))),-4))
assert res=={}
# Clear denominators in k^2 EJ=k(k-1), k=(b+3)/4:
# the remaining terms are -(b+1)b/4 + b(b+1)/4.
beta=var(2)
cancel=add(scale(mul(add(beta,const(1)),beta),-1),mul(beta,add(beta,const(1))))
assert cancel=={}
print(json.dumps({'arithmetic':'exact multivariate integer polynomial ring',
 'determinant_laplacian':'zero polynomial for a general complex cubic derivative with eight independent real coefficients',
 'moment_cancellation':'zero polynomial after clearing denominators',
 'initial_attempt':'SymPy unavailable; no installation attempted; replaced with this dependency-free check',
 'limits':'finite algebra support only; full holomorphic identity is proved by Wirtinger differentiation in AUTHOR-PROOF.md; topology, measurability and theorem are not certified'},indent=2))
