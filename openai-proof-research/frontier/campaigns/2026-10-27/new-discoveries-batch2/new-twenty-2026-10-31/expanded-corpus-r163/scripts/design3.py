# 336565: is the GA_1(2^m)-orbit of B2={u: Tr(u^3+u)=1} a 3-design?  (char 2: u^3-u = u^3+u)
# By 2-transitivity of GA_1(q), 3-design <=> N(u)=#{(x,d): f(x)f(x+d)f(x+ud)=1} is constant for u not in {0,1}.
# N(u) = q^{-1} sum_g F((1+u)g)F(ug)F(g), F = Walsh transform of the 0/1 indicator.
import sys
PRIM={3:0b1011,4:0b10011,8:0b100011101,12:0b1000001010011,5:0b100101,6:0b1000011,7:0b10000011,9:0b1000010001,10:0b10000001001,11:0b100000000101,13:0b10000000011011,14:0b100000000101011}
m=int(sys.argv[1]); q=1<<m; poly=PRIM[m]
exp=[0]*(2*q); log=[0]*q; x=1
for i in range(q-1):
    exp[i]=x; log[x]=i; x<<=1
    if x&q: x^=poly
for i in range(q-1,2*q): exp[i]=exp[i-(q-1)]
assert len(set(exp[:q-1]))==q-1, 'poly not primitive'
def mul(a,b): return 0 if a==0 or b==0 else exp[log[a]+log[b]]
def tr(a):
    t=0; y=a
    for _ in range(m): t^=y; y=mul(y,y)
    return t
TR=[tr(a) for a in range(q)]; assert set(TR)<={0,1}
f=[TR[mul(mul(u,u),u)^u] for u in range(q)]
k=sum(f)
# fast Walsh-Hadamard: Tr(a x) is a linear functional; use the dual basis trick: F(a)=sum_x f(x)(-1)^{Tr(ax)}
# compute via WHT in the coordinates of the trace-dual basis: build matrix of Tr(e_i * e_j)
# simpler: F(a) for all a by WHT over bit-coordinates: g(v)=sum_x f(x)(-1)^{<v,x>}, then F(a)=g(L(a)) where L(a)_j=Tr(a*2^j)
g=[1-2*0 for _ in range(q)]
g=[f[x] for x in range(q)]
h=1
while h<q:
    for i in range(0,q,2*h):
        for j in range(i,i+h):
            a,b=g[j],g[j+h]; g[j]=a+b; g[j+h]=a-b
    h*=2
L=[0]*q
for a in range(q):
    v=0
    for j in range(m):
        if TR[mul(a,1<<j)]: v|=1<<j
    L[a]=v
F=[g[L[a]] for a in range(q)]
vals={}
for u in range(2,q):
    s=0; u1=u^1
    for gg in range(q):
        s+=F[mul(u1,gg)]*F[mul(u,gg)]*F[gg]
    assert s%q==0
    vals.setdefault(s//q,0); vals[s//q]+=1
print('m',m,'k',k,'N(u) value multiset',vals, '3-design' if len(vals)==1 else 'NOT a 3-design')
