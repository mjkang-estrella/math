"""Bounded exact arithmetic supporting Note 02; not a geometry/proof gate."""
from fractions import Fraction as Q
import json

def ceil(x): return -(-x.numerator//x.denominator)
def J(d,b): return max(0,ceil((1-b)/(1-d))-1)
def bounds(m,f,C,coefficients,ranks):
    V=[]; U=[]
    for j,b in enumerate(coefficients):
        u=m*(f+sum(J(d,b)*v for d,v in zip(coefficients[:j],V)))
        U.append(u); V.append(ranks[j]+(ceil(1/b)-1)*u)
    P=m*(f+sum(J(d,Q(0))*v for d,v in zip(coefficients,V)))
    return {'U':U,'V':V,'P':P,'length_bound':C+2*P}

def calculate():
    count=0
    for m in range(2,21):
        for a in range(1,m):
            d=Q(a,m)
            for z in range(m):
                b=Q(z,m)
                explicit=sum(1 for k in range(1,m+1) if 1+k*(1-d)<2-b)
                assert J(d,b)==explicit
                assert J(d,b)<=m-1
                if d<=b: assert J(d,b)==0
                count+=1
    # This is synthetic input to a formula, not an asserted geometric realization.
    examples=[{'m':3,'f':2,'C':5,'b':['2/3','1/3'],'R':[4,7],
               **bounds(3,2,5,[Q(2,3),Q(1,3)],[4,7])},
              {'m':1,'f':8,'C':2,'b':[],'R':[],**bounds(1,8,2,[],[])}]
    return {'cutoff_cases':count,'examples':examples,
            'scope':'exact cutoff and recurrence arithmetic only; no geometric existence or mathematical grade'}
if __name__=='__main__': print(json.dumps(calculate(),indent=2))
