#!/usr/bin/env python3
"""MIT; exact finite diagnostics, not a proof of the general statements."""
import json

def mul(x,y):
    a,b=x;c,d=y
    return a*c+b*d,a*d+b*c+b*d

def power(k):
    z=(1,0); t=(0,1) if k>=0 else (-1,1)
    for _ in range(abs(k)): z=mul(z,t)
    return z

def norm(z):
    a,b=z
    return a*a+a*b-b*b

def positive(z):
    # 2(a+b*tau)=2a+b+b*sqrt(5), exact sign comparison.
    a,b=z; u=2*a+b
    if b==0: return u>0
    if b>0: return u>=0 or 5*b*b>u*u
    return u>0 and u*u>5*b*b

def main():
    cases=0
    for b in range(1,16):
        t=power(2*b); ti=power(-2*b)
        assert mul(t,ti)==(1,0) and norm(t)==norm(ti)==1
        assert t[1]>0  # nonintegral equal-slot track count
        for m in range(1,101):
            A=(m-ti[0],-ti[1]); conjugate=(A[0]+A[1],-A[1])
            if positive(A) and not positive(conjugate) and conjugate!=(0,0):
                assert norm(A)<0
                for a in range(-15,16):
                    scaled=mul(A,power(2*a))
                    assert norm(scaled)==norm(A)<0 and scaled[1]!=0
                cases+=1
    print(json.dumps({'status':'PASS','negative_norm_complements':cases,
      'scales_per_complement':31,'scope':'Finite exact arithmetic only; general proof is in screen-253.md.'},indent=2))

if __name__=='__main__':main()
