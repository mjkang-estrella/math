#!/usr/bin/env python3
"""Finite exact diagnostics only; no theorem, eligibility or novelty gate."""
import itertools, json
from fractions import Fraction as Q

def main():
    counts={"construction_and_derivative":0,"principalization":0,"degree_weights":0}
    for p,s,u,t,F,J in itertools.product((-1,0,1),repeat=6):
        f=u**3+t**7; x=s*s+f+p*p*F
        y=s+x*(x-f); z=s*x+p*p*J
        H=x*x*F-(1+2*s*x)*J-p*p*J*J-p*u
        assert x*y-z*(z+1)==p*p*(H+p*u)
        x0=s*s+f; L=x0*x0*F-(1+2*s*x0)*J
        M=(1-2*s*x0)*F+4*s*s*J
        assert F==4*s*s*L+(1+2*s*x0)*M
        assert J==-(1-2*s*x0)*L+x0*x0*M
        du=-p*p; ds=-3*p*p*x*u*u
        dF=(6*s*x+3)*u*u; dJ=3*x*x*u*u
        dx=2*s*ds+3*u*u*du+p*p*dF
        assert dx==0
        dH=x*x*dF-2*ds*x*J-(1+2*s*x)*dJ-2*p*p*J*dJ-p*du
        assert dH==p**3
        counts['construction_and_derivative']+=1
    for a,d,b,u,t in itertools.product((1,2),(-1,0,1),(-1,0,1),(-1,0,1),(-1,0,1)):
        a=Q(a);c=(1+b*d)/a;f=u**3+t**7
        x=a*b;y=d*c;z=d*b;h=x-f;s=y-x*h
        v=a**3*b-a*a*f-d*d
        f0=x-s*s-f;g0=z-s*x
        C=c*c-b*b*h;alpha=a*a*(1-2*b*d)
        beta=d*d*(3+2*b*d)+alpha*h
        assert f0==C*v and g0==b*b*v and alpha*C+beta*b*b==1
        N=d*d+a*a*f
        assert a*(a*c*c-2*b*c*d-a*b*b*f)==1-b*b*N
        counts['principalization']+=1
    aux={'a':0,'d':21,'b':-21,'c':0,'u':14,'t':6}
    assert aux['a']+aux['c']==aux['b']+aux['d']==0
    assert 2*aux['d']==2*aux['a']+3*aux['u']==2*aux['a']+7*aux['t']==42
    assert 3*aux['a']+aux['b']==-21
    counts['degree_weights']=3
    assert Q(1,2)+Q(1,3)+Q(1,7)==Q(41,42)
    assert Q(1,2)+1+1+1>Q(1,2)
    print(json.dumps({'status':'diagnostics completed','counts':counts,'scope':'Finite exact identities and weights only. Full T047S74 remains unresolved.'},sort_keys=True,indent=2))

if __name__=='__main__':main()
