"""Exact finite algebraic identities, not a proof of analytic inequalities."""
from fractions import Fraction as Q
from itertools import product
import json
def mean(v):return sum(v,Q(0))/len(v)
def noise(v,r):
    n=(len(v)-1).bit_length()
    for i in range(n):v=[(1+r)/2*v[j]+(1-r)/2*v[j^(1<<i)] for j in range(len(v))]
    return v
def run():
    count={'soft_compression_spectral_accounting':0,'two_corner_slack_composition':0,'tree_telescoping':0,'independent_selector_spectral_bound':0}
    for d in product([Q(-1),Q(-1,3),Q(0),Q(1,2),Q(1)],repeat=4):
      for r in [Q(1,3),Q(2,3)]:
        c=mean(list(map(abs,d)));b=mean(d);e=mean([x*x for x in d])
        td=noise(list(d),r);ta=noise(list(map(abs,d)),r)
        gain=mean([x*x for x in ta])-mean([x*x for x in td])
        assert gain >= (1-r*r)*(c*c-b*b)-r*r*(e-c*c)
        count['soft_compression_spectral_accounting']+=1
    for den in range(2,20):
      for num in range(1,den):
       for plus in range(den-num+1):
        k=Q(num,den);p=Q(plus,den);q=1-k-p;t=k/(k+p);s=k+p
        got=s*t*(1-t)+s*(1-s)*t*t
        assert got == k*p/(k+p)+k*k*q/(k+p)
        assert got >= k*k*(1-k)
        count['two_corner_slack_composition']+=1
    for n in range(1,8):
      phi={i:Q((i*i)%17,11) if i<2**n else Q(0) for i in range(1,2**(n+1))}
      edge={i:Q((i*3)%13,7) for i in range(1,2**n)}
      joins={i:edge[i]+(phi[2*i]+phi[2*i+1])/2-phi[i] for i in edge}
      weights=lambda i:Q(1,2**(i.bit_length()-1))
      assert sum((weights(i)*joins[i] for i in joins),Q(0))==sum((weights(i)*edge[i] for i in edge),Q(0))-phi[1]
      count['tree_telescoping']+=1
    for assignment in product(range(3),repeat=4):
      for signs in product([-1,1],repeat=4):
        fs=[[Q(signs[z]) if assignment[z]==j else Q(0) for z in range(4)] for j in range(3)]
        mu=[mean(f) for f in fs]
        for r in [Q(1,3),Q(2,3)]:
          energy=sum(mean([x*x for x in noise(f,r)]) for f in fs)
          assert energy<=r*r+(1-r*r)*sum(x*x for x in mu)
          assert sum(x*x for x in mu)<=max(map(abs,mu))
          count['independent_selector_spectral_bound']+=1
    return {'status':'PASS','arithmetic':'Fraction and integers only','checks':count,'scope':'finite algebraic identities and rational inequalities only; not analytic, universal-proof, or contribution certification'}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
