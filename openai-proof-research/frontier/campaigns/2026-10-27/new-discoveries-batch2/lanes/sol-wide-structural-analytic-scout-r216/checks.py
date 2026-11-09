from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def det(a):
    a=[list(map(F,r)) for r in a]; d=F(1)
    for k in range(len(a)):
        j=next((j for j in range(k,len(a)) if a[j][k]),None)
        if j is None:return F(0)
        if j!=k:a[k],a[j]=a[j],a[k];d=-d
        q=a[k][k];d*=q
        for i in range(k+1,len(a)):
            c=a[i][k]/q
            for j in range(k+1,len(a)):a[i][j]-=c*a[k][j]
    return d

def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def hankel(r,N):return det([[comb(2*(i+j)+r,i+j) for j in range(N)] for i in range(N)])
def band(r,N):
    return det([[1 if i==j==0 else choose(r,max(i,j)) if min(i,j)==0 else
                 choose(r,abs(i-j))+(i==j)+choose(r,i+j)
                 for j in range(N)] for i in range(N)])

def main():
    out={'scope':'exact finite controls, not a proof of any universal source question'}
    cases=0
    for r in range(1,10):
        for N in range(1,15):
            assert hankel(r,N)==band(r,N);cases+=1
    out['hankel_basis_controls']=cases
    assert hankel(3,2)==-4
    out['literal_2009_odd_midpoint_sign_failure']={'r':3,'m':0,'actual':-4,'printed':4,'status':'known corrected 2018; no novelty credit'}
    cases=0
    for a in range(1,5):
      for b in range(5):
       for c in range(5):
        for d in range(5):
         for e in range(5):
          for f in range(5):
           for x0 in range(1,4):
            for x1 in range(1,4):
             cap=F(x1*x1,x0)
             q=lambda x2:(b*x0+c*x1)**2-a*x0*(d*x0+e*x1+f*x2)
             reduced=(b*b-a*d)*x0*x0+(2*b*c-a*e)*x0*x1+(c*c-a*f)*x1*x1
             assert q(cap)==reduced
             assert q(cap/2)>=q(cap);cases+=1
    out['PLC_last_variable_saturation_controls']=cases
    cases=0
    for g in range(7):
     for x in range(9):
      for y in range(9):
       q=(x+y)**2-g*x*y
       if g<=4:assert q>=0
       cases+=1
    assert (1+1)**2-5*1*1<0
    assert 2-3<0
    out['PLC_parameter_family_controls']=cases
    out['global_family']='rows (1), (1,1), (0,g,0), then zero: PLC iff 0<=g<=4; LC-positive iff 0<=g<=2'
    return out

if __name__=='__main__':
    s=json.dumps(main(),indent=2)+'\n'
    (Path(__file__).parent/'check-results.json').write_text(s)
    print(s)
