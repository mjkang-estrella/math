#!/usr/bin/env python3
"""Exact finite coefficient diagnostic; not a mathematical or contribution gate."""
import json
N=5  # X,Y,Z,a,b
ZERO=(0,)*N

def const(n): return {ZERO:n} if n else {}
def var(i):
    e=list(ZERO); e[i]=1
    return {tuple(e):1}
def add(*ps):
    out={}
    for p in ps:
        for e,c in p.items(): out[e]=out.get(e,0)+c
    return {e:c for e,c in out.items() if c}
def scale(p,k): return {e:c*k for e,c in p.items() if c*k}
def mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            g=tuple(x+y for x,y in zip(e,f)); out[g]=out.get(g,0)+c*d
    return {e:c for e,c in out.items() if c}
def powr(p,k):
    out=const(1)
    for _ in range(k): out=mul(out,p)
    return out
X,Y,Z,a,b=map(var,range(N))
def f(t): return add(powr(t,3),mul(a,t),b)
diff=add(X,scale(Y,-1)); diff2=powr(diff,2)
middle=add(mul(add(X,Y),add(mul(X,Y),a)),scale(b,2))
f3=add(mul(diff2,powr(Z,2)),scale(mul(middle,Z),-2),powr(add(mul(X,Y),scale(a,-1)),2),scale(mul(b,add(X,Y)),-4))
lhs=add(powr(add(f(X),f(Y),scale(mul(add(Z,X,Y),diff2),-1)),2),scale(mul(f(X),f(Y)),-4))
residual=add(lhs,scale(mul(diff2,f3),-1))
if residual: raise SystemExit('nonzero formal coefficient residual')
# A wrong product in place of the last sum must be detected.
wrong=add(f3,scale(mul(b,add(X,Y)),4),scale(mul(b,mul(X,Y)),-4))
mutant=add(lhs,scale(mul(diff2,wrong),-1))
if not mutant: raise SystemExit('wrong formula was not distinguished')
print(json.dumps({'diagnostic':'integer polynomial coefficient expansion','variables':['X','Y','Z','a','b'],'residual_terms':len(residual),'printed-product-mutant-residual_terms':len(mutant),'mathematical_gate':False,'scope':'one algebraic identity only'},indent=2))
