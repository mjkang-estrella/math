# MIT. Author: Myeongjin Kang. Float exploration only.
from bs import *
import random, math
def tailstats(w):
    """W=sum w_l E_l. Returns p=P(W>0), P=E W^+, N=E W^- via B-spline of L=<w,u>, W=S L, S~Gamma(k)."""
    w=[x for x in w if x!=0.0]; k=len(w)
    if k==0: return None
    if all(x>0 for x in w): return 1.0, sum(w), 0.0
    if all(x<0 for x in w): return 0.0, 0.0, -sum(w)
    if k==1: raise ValueError
    ws=sorted(w); pts=sorted(set(ws+[0.0])); pr=Ep=En=0.0
    for lo,hi in zip(pts,pts[1:]):
        if hi<=lo: continue
        c=(lo+hi)/2; h=(hi-lo)/2
        for x,wt in GL5:
            t=c+h*x; v=Mspl(t,ws)*wt*h
            if t>0: pr+=v; Ep+=t*v
            else: En-=t*v
    return pr, k*Ep, k*En
def bound_pair(a, i, j):
    """HNBUE bound on Phi for knots a (t=0), pair a_i<0<a_j."""
    m=len(a); n=m-2
    al=-a[i]; be=a[j]
    rest=[a[l] for l in range(m) if l not in (i,j)]
    st=tailstats(rest)
    if st is None: br=1.0
    else:
        p,P,N=st
        br=0.0
        if p>0: br+=p/(1+P/(p*al))
        if p<1: br+=(1-p)/(1+N/((1-p)*be))
    return D(a)/((n+1)*(al+be))*br
def best_bound(a):
    neg=[i for i,x in enumerate(a) if x<0]; pos=[j for j,x in enumerate(a) if x>0]
    return min(bound_pair(a,i,j) for i in neg for j in pos)
def outer_bound(a):
    i=min(range(len(a)),key=lambda l:a[l]); j=max(range(len(a)),key=lambda l:a[l])
    return bound_pair(a,i,j)
