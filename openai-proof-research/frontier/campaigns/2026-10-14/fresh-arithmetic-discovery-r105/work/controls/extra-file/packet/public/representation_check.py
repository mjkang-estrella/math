#!/usr/bin/env python3
"""Bounded arithmetic diagnostics only; no proof or contribution gate. No writes."""
import json,itertools

def rank2(rows):
    piv={}
    for x in rows:
        while x:
            b=x.bit_length()-1
            if b in piv:x^=piv[b]
            else:piv[b]=x;break
    return len(piv)

def compose(a,b):
    p,s=a;q,t=b
    return (tuple(p[q[i]] for i in range(len(p))),tuple(t[i]^s[q[i]] for i in range(len(p))))
def inverse(a):
    p,s=a;q=[0]*len(p);t=q.copy()
    for i,j in enumerate(p):q[j]=i;t[j]=s[i]
    return tuple(q),tuple(t)
def comm(a,b):return compose(compose(compose(a,b),inverse(a)),inverse(b))

def ring_case(mod,ell):
    h=mod.bit_length()-1;n=1<<h
    def mul(a,b):
        x=0
        while b:
            if b&1:x^=a
            b>>=1;a<<=1
            if a&n:a^=mod
        return x
    t=2 if h>1 else mod&1
    tinv=next(a for a in range(n) if mul(a,t)==1)
    def power(r):
        a=t if r>=0 else tinv;v=1
        for _ in range(abs(r)):v=mul(v,a)
        return v
    def chi(a):return (a&ell).bit_count()%2
    pts=list(itertools.product(range(n),repeat=3));idx={x:i for i,x in enumerate(pts)};d=len(pts)
    ident=(tuple(range(d)),(0,)*d)
    def op(fun,phase=lambda x:0):return tuple(idx[fun(x)] for x in pts),tuple(phase(x) for x in pts)
    def add(x,i,a):y=list(x);y[i]^=a;return tuple(y)
    def U(i,r):return op(lambda x:add(x,i,power(r)))
    def V(i,r):return op(lambda x:x,lambda x:chi(mul(power(r),x[i])))
    def W(i,j,r):return op(lambda x:add(x,j,mul(power(r),x[i])))
    def T(i):
        def f(x):y=list(x);y[i]=mul(tinv,y[i]);return tuple(y)
        return op(f)
    tests=0
    def eq(a,b):
        nonlocal tests
        assert a==b;tests+=1
    rs=range(-1,2)
    for i in range(3):
        for r in rs:
            eq(compose(U(i,r),U(i,r)),ident)
            for s in rs:
                neg=chi(power(r+s))
                eq(comm(U(i,r),V(i,s)),(ident[0],(neg,)*d))
                eq(comm(U(i,r),U(i,s)),ident)
        for j in range(3):
            eq(comm(T(i),T(j)),ident)
            for r in rs:
                eq(compose(compose(T(i),U(j,r)),inverse(T(i))),U(j,r-(i==j)))
                eq(compose(compose(T(i),V(j,r)),inverse(T(i))),V(j,r+(i==j)))
            if i==j:continue
            for r in rs:
                for s in rs:
                    eq(comm(U(i,r),U(j,s)),ident)
                    eq(comm(V(i,r),V(j,s)),ident)
                    eq(comm(U(i,r),V(j,s)),ident)
                    eq(comm(U(i,r),W(i,j,s)),U(j,r+s))
                    eq(comm(W(i,j,s),V(j,r)),V(i,r+s))
                    for a in range(3):
                        if a!=i:eq(comm(W(i,j,s),U(a,r)),ident)
                        if a!=j:eq(comm(W(i,j,s),V(a,r)),ident)
                for a in range(3):
                    eq(compose(compose(T(a),W(i,j,r)),inverse(T(a))),W(i,j,r+(a==i)-(a==j)))
    gram=[sum(chi(mul(1<<i,1<<j))<<j for j in range(h)) for i in range(h)]
    assert rank2(gram)==h
    return dict(modulus_binary=bin(mod),ell_mask=ell,h=h,dimension=d,relation_checks=tests,nondegenerate_pairing=True)

def main():
    cases=[ring_case(0b11,1),ring_case(0b101,2),ring_case(0b1001,4),ring_case(0b1011,4)]
    count=0
    for p in range(1,7):
        for c in itertools.product([0,1],repeat=p):
            h=rank2([sum(c[(i+j)%p]<<j for j in range(p)) for i in range(p)])
            if any(c):assert c.index(1)+1<=h
            else:assert h==0
            count+=1
    impulses=[]
    for m in range(1,13):
        c=[0]*(m-1)+[1]
        h=rank2([sum(c[(i+j)%m]<<j for j in range(m)) for i in range(m)])
        assert h==m;impulses.append(dict(m=m,h=h,minimum_dimension=2**(3*m)))
    print(json.dumps(dict(label='finite arithmetic diagnostics only',cases=cases,binary_periodic_sequences=count,impulses=impulses),indent=2))
if __name__=='__main__':main()
