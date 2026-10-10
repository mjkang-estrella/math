"""Finite exact algebra only. No universal-proof or contribution certification."""
from fractions import Fraction as F
from itertools import product
from math import prod

def run():
    counts={'walsh_hessian_decompositions':0,'markov_rank_generating_identities':0,'backward_coordinate_orthogonality':0,'boolean_lift_kernel':0}
    for n in range(1,5):
        cube=list(product([-1,1],repeat=n));N=len(cube)
        for seed in range(5):
            h=[F(((j+1)*(seed+3))%13-6,7) for j in range(N)]
            hats=[sum(v*prod(x[i] for i in range(n) if mask>>i&1) for x,v in zip(cube,h))/N for mask in range(N)]
            assert sum(v*v for v in h)/N==sum(v*v for v in hats)
            m=hats[0]
            for a,rho,k in product([F(1,3),F(2,3)],[F(1,4),F(3,4)],[F(1,5),F(2,5)]):
                # k is a formal coefficient: this checks the exact quadratic
                # identity, not positivity or evaluation of atanh.
                th=[sum(hats[mask]*rho**mask.bit_count()*prod(x[i] for i in range(n) if mask>>i&1) for mask in range(N)) for x in cube]
                left=k*(sum(v*v for v in h)/N/(1-a*a)-m*m)-(sum(v*v for v in th)/N/(1-rho*rho*a*a)-m*m)
                q=k/(1-a*a)-rho*rho/(1-rho*rho*a*a)
                right=a*a*q*m*m+sum((k/(1-a*a)-rho**(2*mask.bit_count())/(1-rho*rho*a*a))*hats[mask]**2 for mask in range(1,N))
                assert left==right
                counts['walsh_hessian_decompositions']+=1
                b=hats[1]
                d1=sum((v-a*x[0])**2 for x,v in zip(cube,h))/N
                d2=sum((v-b*x[0])**2 for x,v in zip(cube,h))/N+(a-b)**2
                assert d1==d2
                counts['backward_coordinate_orthogonality']+=1
    for n in range(1,7):
        for alpha,beta,z in product([F(1,3),F(2,3)],[F(1,4),F(3,4)],[F(-1,2),F(2,3)]):
            P=[[1-alpha,alpha],[beta,1-beta]];pi=[beta/(alpha+beta),alpha/(alpha+beta)]
            x=[(-1)**(j*j+j//2) for j in range(n)]
            lhs=F(0)
            for states in product([0,1],repeat=n):
                probability=pi[states[0]]*prod(P[states[j-1]][states[j]] for j in range(1,n))
                rank=0;value=F(0)
                for j,s in enumerate(states):
                    if s:value+=x[j]*z**rank;rank+=1
                lhs+=probability*value
            row=pi[:];rhs=F(0)
            for j in range(n):
                rhs+=x[j]*row[1]
                row=[row[0]*P[0][i]+row[1]*z*P[1][i] for i in range(2)]
            assert lhs==rhs
            counts['markov_rank_generating_identities']+=1
    for x in [-1,1]:
        values=[x*(-1 if r==(1,1) else 1) for r in product([-1,1],repeat=2)]
        assert F(sum(values),4)==F(x,2)
        counts['boolean_lift_kernel']+=1
    return {'status':'PASS','arithmetic':'Fraction and integers only','checks':counts,'scope':'finite identities only; not universal proof or substantiality'}

if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
