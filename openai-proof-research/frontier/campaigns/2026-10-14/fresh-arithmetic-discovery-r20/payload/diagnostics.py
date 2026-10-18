#!/usr/bin/env python3
"""Exact finite-algebra checks for the r20 mixed-transport obstruction.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
No test here proves root closure or disproves periodic-orbit rigidity.
"""
from fractions import Fraction
from itertools import product
import json

VERTICES=('s','f','o')
# (start,end,length): multiplication is in path order, exactly cat:projective-hom.
BASIS=[(v,v,0) for v in VERTICES]+[(v,w,1) for v in VERTICES for w in VERTICES if v!=w]+[(v,v,2) for v in VERTICES]

def mul(a,b):
    if a is None or b is None or a[1]!=b[0]: return None
    if a[2]==0: return b
    if b[2]==0: return a
    if a[2]==b[2]==1 and a[0]==b[1]: return (a[0],a[0],2)
    return None

def zero(m,n): return [[Fraction(0) for _ in range(n)] for _ in range(m)]
def ident(n): return [[Fraction(i==j) for j in range(n)] for i in range(n)]
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def rank(a):
    a=[list(map(Fraction,row)) for row in a]
    if not a:return 0
    r=0
    for c in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        d=a[r][c];a[r]=[v/d for v in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][c]:
                d=a[i][c];a[i]=[u-d*v for u,v in zip(a[i],a[r])]
        r+=1
    return r

def block(a,b,c,d):return [x+y for x,y in zip(a,b)]+[x+y for x,y in zip(c,d)]
def neg(a):return [[-x for x in row] for row in a]
def proj(v):return [a for a in BASIS if a[1]==v]
def action(path):
    src,tgt=proj(path[0]),proj(path[1]);out=zero(len(tgt),len(src))
    for j,a in enumerate(src):
        b=mul(a,path)
        if b is not None:out[tgt.index(b)][j]=1
    return out

def hom_middle(source,target,ds=(),dt=()):
    # Generator tuple: (vertex, cochain placement, internal placement).
    # Differential tuple: (source generator index,target generator index,path).
    spaces=[]
    for length in range(3):
        spaces.append([(i,j,p) for i,s in enumerate(source) for j,t in enumerate(target)
                       for p in BASIS if p==(s[0],t[0],length)])
    differentials=[]
    for length in (0,1):
        mat=zero(len(spaces[length+1]),len(spaces[length]))
        for col,(i,j,p) in enumerate(spaces[length]):
            n=target[j][1]-source[i][1]
            for a,b,q in dt:
                if a==j:
                    path=mul(p,q)
                    if path is not None:mat[spaces[length+1].index((i,b,path))][col]+=1
            for a,b,q in ds:
                if b==i:
                    path=mul(q,p)
                    if path is not None:mat[spaces[length+1].index((a,j,path))][col]-=1 if n%2==0 else -1
        differentials.append(mat)
    d0,d1=differentials
    if d0 and d1:assert mm(d1,d0)==zero(len(d1),len(d0[0]))
    return {'path_space_dimensions':list(map(len,spaces)),
            'linear_differential_ranks':[rank(d0),rank(d1)],
            'h1':len(spaces[1])-rank(d0)-rank(d1),
            'middle_bidegrees':[[target[j][1]-source[i][1],target[j][2]+1-source[i][2]] for i,j,p in spaces[1]]}

def main():
    for a,b,c in product(BASIS,repeat=3):assert mul(mul(a,b),c)==mul(a,mul(b,c))
    I=ident(4);Z=zero(4,4);T=action(('s','s',2));A=action(('s','f',1))
    assert mm(T,T)==Z and mm(A,T)==Z
    d2=block(I,T,neg(I),Z);d1=[row+row for row in A]
    assert mm(d1,d2)==zero(4,8)
    L=block(I,Z,I,I);Linv=block(I,Z,neg(I),I);R=block(I,neg(T),Z,I)
    assert mm(L,Linv)==ident(8)
    assert mm(mm(L,d2),R)==block(I,Z,Z,T)
    assert mm(d1,Linv)==[zr+ar for zr,ar in zip(Z,A)]
    pre_ranks=[rank(d2),rank(d1)];post_ranks=[rank(T),rank(A)]
    pre_h=[8-pre_ranks[0],8-sum(pre_ranks),4-pre_ranks[1]]
    post_h=[4-post_ranks[0],4-sum(post_ranks),4-post_ranks[1]]
    assert pre_h==post_h
    e0=[('f',0,0)];upper_e2=[('s',-2,3)]
    mixed=hom_middle(e0,upper_e2)
    e1=[('s',-1,1),('f',0,0)];delta=[(0,1,('s','f',1))]
    control=hom_middle(e1,e1,delta,delta)
    assert mixed['h1']==1 and mixed['middle_bidegrees']==[[-2,4]]
    assert control['h1']==0
    out={'status':'PASS','field':'Q; all operations exact fractions',
         'algebra':{'vertices':VERTICES,'dimension':len(BASIS),'associativity_triples':len(BASIS)**3,'auxiliary_o_retained':True},
         'cone':{'pre_cancellation_differential_ranks':pre_ranks,'post_cancellation_differential_ranks':post_ranks,'underlying_vector_space_cohomology_dimensions':post_h,'explicit_basis_changes_verified':True},
         'mixed_E0_upper_E2':mixed,'same_transport_E1_control':control,
         'scope':'Checks the displayed finite algebra and Hom obstruction only. No finite periodic orbit is exhibited. No root-closure theorem/counterexample is inferred.'}
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
