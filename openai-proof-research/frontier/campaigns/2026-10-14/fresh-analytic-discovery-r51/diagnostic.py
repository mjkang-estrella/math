#!/usr/bin/env python3
# MIT. Finite arithmetic diagnostics only, never a mathematical proof gate.
from fractions import Fraction as Q
import json,math

def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b)))for j in range(len(b[0]))]for i in range(len(a))]
def power(a,n):
    out=[[Q(i==j)for j in range(len(a))]for i in range(len(a))]
    for _ in range(n):out=mul(out,a)
    return out
def matrix(q):return [[(1+q)/2,(1-q)/2],[(1-q)/2,(1+q)/2]]
def trace(a):return sum(a[i][i]for i in range(len(a)))
for q in [Q(1,3),Q(2,3),Q(3,4)]:
    a=matrix(q)
    assert all(v>0 for row in a for v in row)
    assert all(sum(row)==1 for row in a)
    for m in range(1,21):assert trace(power(a,m))==1+q**m
negative=[]
def reject(label,claim):
    assert not claim,label+' false inference was accepted'
    negative.append(label)
reject('same Perron data determines finite trace',trace(power(matrix(Q(1,3)),5))==trace(power(matrix(Q(2,3)),5)))
# For S_L the energy log L escapes every fixed window, while L exp(-log L)=1 exactly.
for L in [2,4,16,256,65536]:
    assert abs(L*math.exp(-math.log(L))-1)<1e-12
reject('escaping scaled energies force vanishing total trace tail',abs(65536*math.exp(-math.log(65536)))<1e-3)
reject('refined displayed log error vanishes at fixed imbalance',Q(1000000,10)<Q(1,100))
# Bernoulli bound on the displayed cylinder-success lower bound at M=L, eta=1/2.
assert Q(128,2)*Q(1,2)**128<Q(1,10**30)
reject('displayed cylinder lower bound stays positive at fixed aspect ratio',Q(128,2)*Q(1,2)**128>Q(1,10))
# Positive tail-inequality sample with r0=1,r=2,R=3, energies j and unit multiplicities.
lhs=sum(math.exp(-2*j)for j in range(4,101))
rhs=math.exp(-3)*sum(math.exp(-j)for j in range(101))
assert lhs<=rhs
print(json.dumps({'nonproof':True,'matrix_power_checks':60,'negative_inferences_rejected':negative,'tail_sample':'pass'},indent=2))
