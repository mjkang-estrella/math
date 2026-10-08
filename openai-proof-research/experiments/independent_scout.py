"""Finite sanity checks; no numerical claim proves an asymptotic theorem."""
from math import log
from fractions import Fraction

def checks():
    for j in range(7):
        start = 4**j
        mass = sum((Fraction(1,n) for n in range(start,2*start)), Fraction())
        assert mass >= Fraction(1,2)
    # Separated base-four digits: remaining tail <= one third of current weight.
    for e in range(10):
        w=Fraction(1,4**(e+1))
        assert sum((Fraction(1,4**(j+1)) for j in range(e+1,100)),Fraction()) < w/3
    # Example signed polynomial x^3 - 2*x - y is evaluated by nonnegative gates.
    for x in range(5):
        for y in range(5):
            u=x*x; v=u*x; w=2*x; t=w+y
            q=(u-x*x)**2+(v-u*x)**2+(w-2*x)**2+(t-w-y)**2+(v-t)**2
            assert (q==0)==(x**3-2*x-y==0)
    print('Exact block, digit-gap, and gate checks passed.')

def density(limit=1000000):
    largest=[0]*(limit+2)
    for p in range(2,limit+2):
        if largest[p]==0:
            for n in range(p,limit+2,p): largest[n]=p
    thresholds=(.5,.6,.8)
    hits={t:0 for t in thresholds}
    snapshots={10000,100000,limit}
    for n in range(2,limit+1):
        product=log(largest[n])*log(largest[n+1])/log(n)**2
        for t in thresholds: hits[t]+=product>t
        if n in snapshots:
            print('N=',n,[(t,round(hits[t]/(n-1),6),round(log(1/t)**2/2,6)) for t in thresholds])
if __name__=='__main__':
    checks();density()
