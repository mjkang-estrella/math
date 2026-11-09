# Numerically audits each step of the ordinary proof for 336565 (diagnostic only).
import sys, random
PRIM={3:0b1011,4:0b10011,5:0b100101,6:0b1000011,7:0b10000011,8:0b100011101,9:0b1000010001,10:0b10000001001}
def field(m):
    q=1<<m; poly=PRIM[m]; exp=[0]*(2*q); log=[0]*q; x=1
    for i in range(q-1):
        exp[i]=x; log[x]=i; x<<=1
        if x&q: x^=poly
    for i in range(q-1,2*q): exp[i]=exp[i-(q-1)]
    mul=lambda a,b: 0 if a==0 or b==0 else exp[log[a]+log[b]]
    inv=lambda a: exp[(q-1-log[a])%(q-1)]
    def tr(a):
        t=0;y=a
        for _ in range(m): t^=y; y=mul(y,y)
        return t
    return q,mul,inv,[tr(a) for a in range(q)]
random.seed(1)
for m in sorted(PRIM):
    q,mul,inv,TR=field(m)
    cube=lambda a: mul(mul(a,a),a)
    Q=lambda x: TR[cube(x)^x]
    chi=[1-2*Q(x) for x in range(q)]
    s=sum(chi); k=sum(1 for x in range(q) if Q(x)==1)
    # Step A (corrected): Q(x)+Q(x+d)+Q(x+ud) = Q(x+e)+Tr(a e^3), e=(1+u)d, a=u/(1+u)^2
    ok=True
    for _ in range(3000):
        x,d=random.randrange(q),random.randrange(q); u=random.randrange(2,q)
        e=mul(1^u,d); a=mul(u, inv(mul(1^u,1^u)))
        lhs=Q(x)^Q(x^d)^Q(x^mul(u,d)); rhs=Q(x^e)^TR[mul(a,cube(e))]
        ok&= lhs==rhs
    # Step B: c+1 = u/(1+u)^2
    okB=all((mul(1^u^mul(u,u),inv(mul(1^u,1^u)))^1)==mul(u,inv(mul(1^u,1^u))) for u in range(2,q))
    # Step C: s^2 = q * sum_{e in GF(4) cap GF(q)} (-1)^{Tr(e^3+e)}
    fixed=[e for e in range(q) if mul(mul(e,e),mul(e,e))==e]
    okC= s*s == q*sum(1-2*TR[cube(e)^e] for e in fixed)
    # Step D: T(u) = s * sum_e (-1)^{Tr(u e^3/(1+u)^2)} and N(u) = (q^2-3qs+3s^2-T(u))/8 equals the direct count, for a few u
    okD=True; Tvals=set()
    for u in random.sample(range(2,q),min(6,q-2)):
        a=mul(u,inv(mul(1^u,1^u)))
        T=s*sum(1-2*TR[mul(a,cube(e))] for e in range(q)); Tvals.add(T)
        if q<=256:
            Tdir=sum(chi[x]*chi[x^d]*chi[x^mul(u,d)] for x in range(q) for d in range(q))
            Ndir=sum(1 for x in range(q) for d in range(q) if Q(x) and Q(x^d) and Q(x^mul(u,d)))
            okD&= (T==Tdir) and (8*Ndir==q*q-3*q*s+3*s*s-T)
    print(f"m={m} k={k} s={s} stepA={ok} stepB={okB} stepC={okC} (|GF4capGFq|={len(fixed)}) stepD={okD} T(u) sample values={sorted(Tvals)}")
