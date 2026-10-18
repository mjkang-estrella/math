#!/usr/bin/env python3
"""Finite diagnostic of all principal congruences; not a proof of the theorem."""
import itertools,json

def prime(p):
    return p >= 2 and all(p % d for d in range(2,int(p**.5)+1))

def closure(m,ops,a,b):
    parent=list(range(m))
    def find(x):
        while x != parent[x]:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    stack=[(a,b)]
    while stack:
        x,y=stack.pop();x=find(x);y=find(y)
        if x==y:continue
        parent[y]=x
        stack.extend((op[x],op[y]) for op in ops)
    return [find(x) for x in range(m)]

def check(n,ops):
    s=1+len(ops)+2*(n-1)
    slots=[0]+[3**i for i in range(s-1)]
    p=2*max(slots)+1
    while not prime(p):p+=1
    differences=[(x-y)%p for x in slots for y in slots if x!=y]
    if len(set(differences))!=len(differences):raise ValueError('non-Sidon slots')
    maps=[list(range(n))]+list(ops)+[[a]*n for a in range(1,n) for _ in range(2)]
    g={i:f for i,f in zip(slots,maps)}
    # index i*n+a
    c=[((i+1)%p)*n+a for i in range(p) for a in range(n)]
    e=[g.get(i,[0]*n)[a] for i in range(p) for a in range(n)]
    if any(e[e[x]]!=e[x] for x in range(n*p)):raise ValueError('not idempotent')
    count=0
    for x in range(n*p):
        for y in range(x,n*p):
            actual=closure(n*p,[c,e],x,y)
            if x//n != y//n:
                expected=[0]*(n*p)
            else:
                base=closure(n,ops,x%n,y%n)
                expected=[(i,base[a]) for i in range(p) for a in range(n)]
            forward={};backward={}
            for a,b in zip(actual,expected):
                if a in forward and forward[a]!=b:raise ValueError(('extra pair',n,ops,x,y))
                if b in backward and backward[b]!=a:raise ValueError(('missing pair',n,ops,x,y))
                forward[a]=b;backward[b]=a
            count+=1
    return {'n':n,'operations':ops,'prime':p,'carrier':n*p,'principal_generators_checked':count}

if __name__=='__main__':
    cases=[(1,[]),(2,[]),(3,[])]+[(2,[list(f)]) for f in itertools.product(range(2),repeat=2)]
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_ONLY','cases':[check(n,ops) for n,ops in cases]},indent=2))
