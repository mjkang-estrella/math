#!/usr/bin/env python3
"""Independent finite audit checks; no upstream truth audit or infinite certification.
Run from repository root. Uses only Python standard library and exact Fractions.
"""
from fractions import Fraction as F
from itertools import permutations, product
from collections import defaultdict
from math import prod, isqrt
import json
from pathlib import Path

OUT = Path('frontier/experiments/i08_variable_capacity_r2/results.json')
results = {}

def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for e,c in p.items(): out[e] += c
    return {e:c for e,c in out.items() if c}

def mul(a,b):
    out = defaultdict(int)
    for e,c in a.items():
        for f,d in b.items(): out[tuple(x+y for x,y in zip(e,f))] += c*d
    return {e:c for e,c in out.items() if c}

def scale(a,k): return {e:c*k for e,c in a.items() if c*k}
zero = (0,)*6
one = {zero:1}
variables = [{tuple(int(i==j) for j in range(6)):1} for i in range(6)]
x,y = variables[:3],variables[3:]
s = add(*(mul(x[i],y[i]) for i in range(3)))
N = [add(x[i],y[i],mul(x[(i+1)%3],y[(i+2)%3]),mul(x[(i+2)%3],y[(i+1)%3])) for i in range(3)]
P = mul(mul(mul(N[0],N[1]),N[2]),add(one,scale(s,-2)))
assert sum(abs(c) for c in P.values()) <= 448
pure = {e:c for e,c in P.items() if sum(e[:3])==0 or sum(e[3:])==0}
assert pure == {(1,1,1,0,0,0):1,(0,0,0,1,1,1):1}
remaining = {e:c for e,c in P.items() if sum(e[:3])>=2 and sum(e[3:])>=2}
Q = mul(add(*(mul(n,n) for n in N)),add(one,scale(s,-1)))
# Reduce the quadratic expansion using symmetry; result keys encode a,b,tau_x,tau_y.
def expectation(e):
    degree=sum(e)
    if degree==0: return '1',F(1)
    if degree==2 and max(e)==2: return 'm',F(1,3)
    if e==(1,1,1): return 'tau',F(1)
    assert degree<=3
    return 'zero',F(0)
reduced=defaultdict(F)
for e,c in Q.items():
    k,a=expectation(e[:3]); l,b=expectation(e[3:]); reduced[(k,l)]+=c*a*b
reduced={k:v for k,v in reduced.items() if v}
assert reduced=={('m','1'):F(1),('1','m'):F(1),('tau','m'):F(-4),('m','tau'):F(-4),('tau','tau'):F(-6)}
results['symbolic']={'third_polynomial_terms':len(P),'third_coefficient_L1':sum(abs(c) for c in P.values()),'surviving_mixed_coefficient_L1':sum(abs(c) for c in remaining.values()),'pure_terms_exact':True,'quadratic_cancellation_exact':True,'uniform_remainder_bound':'|N1 N2 N3|/Z^2 <= Z <= 4, |3+2s| <= 9; E s^2 = ab/3; hence <=12ab'}

L=((1,1,-1,-1),(1,-1,1,-1),(1,-1,-1,1))
u=(F(1,4),)*4

def coords(p): return tuple(sum(c*q for c,q in zip(row,p)) for row in L)
def orbit(p):
    ps=set(permutations(p)); return {q:F(1,len(ps)) for q in ps}
def moments(law):
    m=tau=F(0)
    for p,w in law.items():
        z=coords(p); m+=w*sum(v*v for v in z); tau+=w*prod(z)
    return m,tau

def star(mu,nu):
    out=defaultdict(F)
    for p,wp in mu.items():
        for q,wq in nu.items():
            v=tuple(4*pi*qi for pi,qi in zip(p,q)); Z=sum(v)
            if Z: out[tuple(a/Z for a in v)]+=wp*wq*Z
    assert sum(out.values())==1
    return dict(out)

def channel(mu,t): return {tuple(F(1,4)+t*(v-F(1,4)) for v in p):w for p,w in mu.items()}
# Every integer partition of six into at most four parts yields an orbit, including faces.
seeds=sorted({tuple(sorted((a,b,c,6-a-b-c),reverse=True)) for a in range(7) for b in range(7-a) for c in range(7-a-b)})
laws=[orbit(tuple(F(a,6) for a in p)) for p in seeds]
laws.append({u:F(1)})
laws.append(orbit((F(1,3),F(1,3),F(1,3),F(0)))) # negative signed third moment
# A mixed law tests nonconstant radial information.
mix=defaultdict(F)
for p,w in laws[0].items(): mix[p]+=w*F(2,5)
for p,w in laws[-2].items(): mix[p]+=w*F(3,5)
laws.append(dict(mix))
zero_count=pair_count=negative_tau=0
for mu in laws:
    a,tx=moments(mu); negative_tau+=tx<0
    for nu in laws:
        b,ty=moments(nu); mp,tp=moments(star(mu,nu)); rem=poly=third_rem=Es2=F(0)
        for p,wp in mu.items():
            xx=coords(p)
            for q,wq in nu.items():
                yy=coords(q); ss=sum(a*b for a,b in zip(xx,yy)); Z=1+ss
                ns=tuple(xx[i]+yy[i]+xx[(i+1)%3]*yy[(i+2)%3]+xx[(i+2)%3]*yy[(i+1)%3] for i in range(3))
                assert 0<=Z<=4 and all(abs(a)<=Z for a in ns)
                weight=wp*wq; Es2+=weight*ss*ss
                poly+=weight*prod(ns)*(1-2*ss)
                if Z:
                    rem+=weight*sum(a*a for a in ns)*ss*ss/Z
                    rr=prod(ns)*ss*ss*(3+2*ss)/(Z*Z)
                    assert abs(rr)<=36*ss*ss
                    third_rem+=weight*rr
                else:
                    zero_count+=1; assert ns==(0,0,0)
        assert Es2==a*b/3
        assert mp==a+b-4*(tx*b+a*ty)-6*tx*ty+rem
        assert tp==poly+third_rem
        assert mp>=a+b-7*(abs(tx)*b+a*abs(ty))
        assert abs(tp)<=abs(tx)+abs(ty)+460*a*b
        pair_count+=1
results['posterior_pairs']={'laws':len(laws),'ordered_pairs':pair_count,'negative_tau_laws':negative_tau,'zero_normalizer_atoms':zero_count,'exact_identities_and_L':True,'upstream_moment_saving_not_tested':True}

# Finite, asymmetric exact flow trees, extended after their last level by perfect unary rays.
def sqrtf(z):
    a,b=isqrt(z.numerator),isqrt(z.denominator)
    assert a*a==z.numerator and b*b==z.denominator
    return F(a,b)

def make_tree(n,mode):
    nodes={():{'X':F(3,10**8),'R':F(1),'prob':F(1),'children':[]}}
    for i in range(n):
        for v in [p for p in nodes if len(p)==i]:
            splits=[F(1)] if (i+sum(v)+mode)%3==0 else ([F(9,25),F(16,25)] if (i+mode)%2 else [F(1,9),F(4,9),F(4,9)])
            for j,t in enumerate(splits):
                w=v+(j,)
                ls=[F(1),F(999,1000),F(1,1000),F(2,3)]
                lam=ls[(i+j+mode)%4]
                nodes[w]={'X':nodes[v]['X']*t/(lam*lam),'R':nodes[v]['R']*lam*lam,'prob':nodes[v]['prob']*t,'t':t,'lambda':lam,'children':[]}
                nodes[v]['children'].append(w)
    return nodes

flow_summaries=[]
for mode in range(4):
    n=5; nd=make_tree(n,mode); paths=[p for p in nd if len(p)==n]
    maxV=max(sum((1-nd[p[:i+1]]['lambda']**4)*nd[p[:i+1]]['X']**2 for i in range(n)) for p in paths)
    X0=nd[()]['X']; maxX=max(v['X'] for v in nd.values())
    assert maxX**2<=X0**2+maxV
    for p in nd:
        d=nd[p]; d['beta']=1-sum(nd[w]['t']**2 for w in d['children']) if d['children'] else F(0)
        if d['children']:
            assert d['X']==sum(nd[w]['lambda']**2*nd[w]['X'] for w in d['children'])
            diff=d['X']**2-sum(nd[w]['t']*nd[w]['lambda']**4*nd[w]['X']**2 for w in d['children'])
            assert diff==d['X']**2*(1-sum(nd[w]['t']**3 for w in d['children']))
            assert diff>=d['X']**2*d['beta']
    energy=F(0); double=F(0); terminal=F(0); unfolded=F(0)
    for p in paths:
        vs=[nd[p[:i]] for i in range(n+1)]; xx=[d['X'] for d in vs]
        alpha=[1-vs[i+1]['t'] for i in range(n)]
        K=lambda i,j:prod(sqrtf(vs[k]['t']) for k in range(i+1,j+1))
        lam=lambda i,j:prod(vs[k]['lambda'] for k in range(i+1,j+1))
        for i in range(n): assert sum(alpha[j]*K(i,j) for j in range(i+1,n))<=2
        for j in range(n+1): assert sum(alpha[i]*K(i,j) for i in range(j))<=2
        ee=sum(alpha[i]*xx[i]**2 for i in range(n))
        bb=sum(alpha[i]*alpha[j]*xx[i]*xx[j]*lam(i,j) for i in range(n) for j in range(i+1,n))
        for i in range(n):
            for j in range(i+1,n+1): assert xx[i]*xx[j]*lam(i,j)==sqrtf(xx[i]**3*xx[j])*K(i,j)
        assert bb<=2*ee
        # terminal U = sqrt(X/3)/3; every X/3 is a rational square.
        uu=sqrtf(xx[n]/3)/3
        tt=sum(alpha[i]*xx[i]*lam(i,n)*uu for i in range(n))
        assert tt<=2*max(sqrtf(x/3)*x/3 for x in xx)
        weight=vs[n]['prob']; energy+=weight*ee; double+=weight*bb; terminal+=weight*tt
        unfolded+=weight*(sum(xx[i]**2*alpha[i] for i in range(n))+2000*bb+tt)
    assert energy<=X0**2+maxV
    # Independently recurse equality versions of H and D; checks all expectation indices.
    for p in sorted(nd,key=len,reverse=True):
        d=nd[p]
        if not d['children']:
            d['U']=sqrtf(d['X']/3)/3; d['loss']=F(0)
        else:
            d['U']=sum(nd[w]['t']*nd[w]['lambda']*nd[w]['U'] for w in d['children'])+2000*d['X']*d['beta']
            d['loss']=d['X']*sum(nd[w]['t']*(1-nd[w]['t'])*nd[w]['lambda']*nd[w]['U'] for w in d['children'])+d['X']**2*d['beta']
    recursed=sum(d['prob']*d['loss'] for p,d in nd.items() if len(p)<n)
    assert recursed==unfolded
    flow_summaries.append({'mode':mode,'nodes':len(nd),'rays':len(paths),'depth':n,'exact_kernel_energy_and_unfolding':True})
results['finite_flows']=flow_summaries

# Actual finite channel products: independent exact local (H),(D) checks.
reveal=orbit((F(1),F(0),F(0),F(0)))
actual=[]
for params in [(F(1),),(F(1),F(1)),(F(1,1000),F(999,1000)),(F(1),F(1,2),F(2,3))]:
    terminals=[channel(reveal,F(i+1,100)) for i in range(len(params))]
    branch=[channel(law,t) for law,t in zip(terminals,params)]
    child=[moments(law) for law in terminals]; bs=[t*t*m for t,(m,h) in zip(params,child)]
    X=sum(bs); beta=1-sum((b/X)**2 for b in bs)
    combined={u:F(1)}
    for law in branch: combined=star(combined,law)
    mm,hh=moments(combined); deficit=sum(bs)-mm
    H=sum(t**3*abs(h) for t,(m,h) in zip(params,child))
    assert abs(hh)/X<=H/X+2000*X*beta
    bound=2000*(sum((1-b/X)*t**3*abs(h) for b,t,(m,h) in zip(bs,params,child))+X*X*beta)
    assert 0<=deficit/X<=bound
    if len(params)==1: assert deficit==0 and beta==0
    actual.append({'children':len(params),'support_size':len(combined),'exact_local_H_D':True})
# Slack profiles and an internal product test the branch-difference bound beyond terminals.
internal=star(channel(reveal,F(1,10)),channel(reveal,F(1,5)))
laws2=[internal,channel(reveal,F(1,7)),channel(reveal,F(1,8))]
lam2=[F(1),F(1,1000),F(999,1000)]
ch2=[moments(law) for law in laws2]
profiles=[m*F(i+2) for i,(m,h) in enumerate(ch2)]
bs=[t*t*m for t,(m,h) in zip(lam2,ch2)]
X=sum(t*t*z for t,z in zip(lam2,profiles))
tts=[t*t*z/X for t,z in zip(lam2,profiles)]
beta=1-sum(t*t for t in tts)
for b,t in zip(bs,tts): assert sum(bs)-b<=X*(1-t)
combo={u:F(1)}
for law,t in zip(laws2,lam2): combo=star(combo,channel(law,t))
mm,hh=moments(combo); dd=sum(bs)-mm
assert abs(hh)/X<=sum(t**3*abs(h) for t,(m,h) in zip(lam2,ch2))/X+2000*X*beta
bound=2000*(sum((1-s)*t**3*abs(h) for s,t,(m,h) in zip(tts,lam2,ch2))+X*X*beta)
assert 0<=dd/X<=bound
actual.append({'children':3,'support_size':len(combo),'slack_profiles':True,'internal_child_product':True,'exact_local_H_D':True})
results['actual_channel_stars']=actual
# Ray telescope, finite exact product and limit derived algebraically in review.
P=F(1); V=F(0)
for j in range(1,101):
    lam=1-F(1,(j+1)**2); P*=lam; V+=(1-lam**4)/P**4
    assert P==F(j+2,2*(j+1)) and V==P**(-4)-1
results['ray']={'checked_prefixes':100,'exact_product_and_weighted_telescope':True,'limit_potential':'15','limit_TV':'3/8'}
results['status']='PASS all finite checks; infinite theorem rests on written proof audit'
OUT.write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
