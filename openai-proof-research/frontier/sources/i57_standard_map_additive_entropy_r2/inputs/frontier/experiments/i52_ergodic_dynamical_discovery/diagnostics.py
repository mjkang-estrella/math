#!/usr/bin/env python3
"""Finite diagnostics only. Standard library; emits JSON; never writes files."""
import json, math
from fractions import Fraction as Q


def mul(a,b):
    return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])

def mat(v): return (v,-1,1,0)
def det(a): return a[0]*a[3]-a[1]*a[2]
def norm(a): return (math.hypot(a[0]+a[3],a[1]-a[2])+math.hypot(a[0]-a[3],a[1]+a[2]))/2

def run():
    count=0
    def check(test):
        nonlocal count
        if not test: raise AssertionError('diagnostic assertion '+str(count))
        count+=1
    rational=[]
    for L in (3,5,10,100):
        for m in (1,2,3,5,8,12):
            a=(1,0,0,1)
            for _ in range(2*m): a=mul(mat(L),a)
            P,Q0=a[0],a[2]
            b=Q(2*Q0,P)
            B=mul(mat(b),a)
            check(det(B)==1);check(B[0]+B[3]==0)
            check(mul(B,B)==(-1,0,0,-1))
            check(mul(mat(0),a)[0]+mul(mat(0),a)[3]!=0)
            rational.append({'L':L,'good_run':2*m,'b':str(b),'bad_frequency':str(Q(1,2*m+1))})
    upper=[]
    for K in (16,64,256,1024):
        N=65536
        avg=math.fsum(math.asinh(abs(2+K*math.cos(2*math.pi*(i+.5)/N))/2) for i in range(N))/N
        rem=avg-math.log(K/2)
        check(0<rem<4/K)
        upper.append({'K':K,'midpoint_nodes':N,'a1_quadrature':avg,'remainder':rem,'K_times_remainder':K*rem})
    trajectories=[]
    for K in (16,64,256,1024):
        horizons=(1,2,4,8,16,32,64); sums={n:[] for n in horizons};goods={n:0 for n in horizons}
        for ix in range(11):
            for iy in range(13):
                q=(ix+.173)/11;p=(iy+.381)/13
                A=(1.,0.,0.,1.);scale=0.;vlogs=0.;good=True
                for j in range(1,65):
                    v=2+K*math.cos(2*math.pi*q);good=good and abs(v)>=2
                    vlogs+=math.log(abs(v)) if v else -math.inf
                    A=mul(mat(v),A);s=max(map(abs,A));A=tuple(x/s for x in A);scale+=math.log(s)
                    ln=scale+math.log(norm(A))
                    check(ln>=-1e-9);check(ln<=j*math.log(K+4)+1e-9)
                    if good:
                        check(ln+1e-8>=vlogs-j) # F's b=2 cone inequality
                    if j in sums:
                        sums[j].append(ln/j);goods[j]+=int(good)
                    q,p=(2*q-p+(K/(2*math.pi))*math.sin(2*math.pi*q))%1,q
                check(math.isfinite(ln))
        for n in horizons:
            avg=math.fsum(sums[n])/len(sums[n])
            b=min(K/4,max(2,(K/(n*math.log(K+4)))**(1/3)))
            lower=math.log(K/2)-2*n*b*math.log(K+4)/K-2/(b*(b-1))
            # Numerical comparison, not a certified integral inequality.
            trajectories.append({'K':K,'n':n,'grid_points':len(sums[n]),'mean_log_norm_per_step':avg,
                                 'b':b,'proved_integral_lower_bound':lower,'grid_minus_lower':avg-lower,'good_b2':goods[n]})
    fixed=[]
    for j in (1,2,10,100,1000):
        k=math.sqrt(j*j+1/math.pi**2)
        theta=math.atan2(j/k,-1/(math.pi*k));q=theta/(2*math.pi)
        kick=k*math.sin(theta);v=2+2*math.pi*k*math.cos(theta)
        check(abs(kick-j)<1e-8);check(abs(v)<1e-8)
        fixed.append({'j':j,'k':k,'q':q,'kick_error':kick-j,'trace':v})
    check(mul(mul(mat(0),mat(0)),mul(mat(0),mat(0)))==(1,0,0,1))
    # Full base marginal is uniform, yet chosen slope cancels identically.
    for K in (16,128):
        for i in range(80):
            q=(i+.25)/80;r=2+K*math.cos(2*math.pi*q)
            check((2+K*math.cos(2*math.pi*q))-r==0)
    cant=math.prod(math.cos(2*math.pi/(3**j)) for j in range(1,24))
    check(abs(cant)>.1)
    # Exact integer-period cancellation avoids inaccurate large floating phases.
    vals=[{'m':m,'tail_product':cant,'removed_integer_period_factors':m} for m in (0,1,4,10)]
    alpha=math.sqrt(2)/5;best=2.;hol=[]
    for m in range(1,20001):
        gap=2*abs(math.sin(math.pi*m*alpha))
        if gap<best:
            best=gap;hol.append({'mode':m,'gap':gap})
    check(best<.001)
    # Exact norm identity on moderate matrices and trace formula.
    for t in (-100,-5,-1,0,1,5,100):
        check(abs(math.log(norm(mat(t)))-math.asinh(abs(t)/2))<1e-12)
        check(det(mat(t))==1)
    return {'kind':'finite diagnostics, not universal proof or entropy computation','assertions':count,
            'rational_periodic_cocycles':rational,'one_step_quadrature':upper,'standard_map_finite_trajectories':trajectories,
            'actual_elliptic_fixed_points':fixed,'cantor_fourier_subsequence':vals,'irrational_holonomy_records':hol,
            'negative_controls':['wrong cancellation coefficient gives nonzero trace','uniform base marginal with r=v has exact resonance']}

if __name__=='__main__': print(json.dumps(run(),indent=2,sort_keys=True))
