"""Finite exact checks only; no external packages, filesystem writes, or network."""
from fractions import Fraction
from math import gcd, isqrt
from collections import Counter

def run():
    counts=Counter()
    # Joint local conditions: individually rooted quadratics need not be joint.
    assert all(any(t*t%m==0 for t in range(m)) for m in range(1,35))
    assert all(any((t-1)**2%m==0 for t in range(m)) for m in range(1,35))
    assert not any(t*t%2==0 and (t-1)**2%2==0 for t in range(2))
    counts['joint_root_obstruction']=1
    assert all(any(((t-j)**4+4)%4 for t in range(4)) for j in [0,1])
    assert all(any(((t-j)**4+4)%4==0 for j in [0,1]) for t in range(4))
    counts['joint_squarefree_obstruction']=1
    # Gauss |G|^2 identity, checked as exact cyclotomic coefficient vectors.
    # For odd m the h-kernel has gcd(b,m) elements, phase a*h+b*h*h.
    for m in range(1,50,2):
      for a in range(m):
       for b in range(m):
        g=gcd(b,m)
        hs=[h for h in range(m) if (2*b*h)%m==0]
        assert len(hs)==g
        phases=Counter((a*h+b*h*h)%m for h in hs)
        if a%g==0:
         assert phases==Counter({0:g})
        else:
         period=g//gcd(a,g)
         expected=Counter({j*(m//period):g//period for j in range(period)})
         assert phases==expected
        counts['odd_modulus_gauss_cases']+=1
    # Exact parabolic lift image and exceptional primitive character at p^2.
    for p in [3,5,7,11,13,17]:
      for q in range(1,p):
       for r in range(p):
        vals={((r+p*t)%(p*p),(q*(r+p*t)**2)%(p*p)) for t in range(p)}
        assert len(vals)==p
        a=(-2*q*r)%(p*p)
        phases={(a*(r+p*t)+q*(r+p*t)**2)%(p*p) for t in range(p)}
        assert len(phases)==1
        counts['nonvanishing_normal_character']=counts['nonvanishing_normal_character']+1
    # Sharp deterministic prediction bound: uniform (x,y), mixture of graph and uniform z.
    for p in [3,5,7]:
      for rho in [Fraction(0),Fraction(1,5),Fraction(1,2),Fraction(1)]:
        probs=[rho+(1-rho)/p]+[(1-rho)/p]*(p-1)
        assert sum(probs)==1
        assert probs[0]==Fraction(1,p)+(1-Fraction(1,p))*rho
        # Conditional nonzero Fourier coefficients are rho times a character.
        assert all(probs[j]-probs[-1]==(rho if j==0 else 0) for j in range(p-1))
        counts['sharp_prediction_mixtures']+=1
    # Chirp extremizer: exponent cancels identically on v=-u.
    for p in [3,5,7,11,13]:
      for c in range(1,p):
       for x in range(p):
        for u in range(p):
         v=(-u)%p
         assert (2*c*u*u+2*c*x*x-c*(x+u)**2-c*(x+v)**2)%p==0
         counts['chirp_phase_identities']+=1
    # Full-set finite checks of the counting/variation bridge with exact alpha(G).
    for N in range(3,11):
      for q in range(1,4):
       for D in range(1,4):
        M=isqrt((N-1)//(q*D*D))
        if M<1:continue
        edges=[(x,x+q*D*D*t*t) for t in range(1,M+1) for x in range(1,N+1-q*D*D*t*t)]
        aset=[{i+1 for i in range(N) if mask>>i&1} for mask in range(1<<N)]
        independence=max(len(A) for A in aset if not any(x in A and y in A for x,y in edges))
        for A in aset:
         a=len(A); E=sum(x in A and y in A for x,y in edges)
         V=sum(x-D not in A for x in A)
         T=sum(x in A and x+D*t in A and y in A for t in range(2,M+1) for x in range(1,N+1-q*D*D*t*t) for y in [x+q*D*D*t*t])
         assert 2*E >= Fraction(a*a,independence)-a
         assert 2*T >= Fraction(a*a,independence)-3*a-V*M*(M+1)
         counts['variation_counting_cases']+=1
    # Exact rescaling and resource recurrences.
    for q in range(1,15):
     for d in range(1,15):
      for t in range(1,9):
       assert q*(d*t)**2 == d*(q*d*t*t)
       counts['progression_covariance']=counts['progression_covariance']+1
    for j in range(1,14):
      S=sum(Fraction(1,2)**(j-1-i)*2**i for i in range(j))
      assert S==Fraction(2**(j+1),3)-Fraction(2,3*2**j)
      counts['resource_geometric_sum']=counts['resource_geometric_sum']+1
    return {'status':'PASS','scope':'finite exact arithmetic; not an analytic proof or novelty certificate','counts':dict(counts)}

if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2,sort_keys=True))
