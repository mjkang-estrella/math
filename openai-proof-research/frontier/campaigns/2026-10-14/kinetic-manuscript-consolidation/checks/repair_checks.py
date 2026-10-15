"""Exact finite controls for the repaired prefix construction, not a proof of W.

One-dimensional normal collisions embed in R^3. Fractions avoid tolerances.
"""
from fractions import Fraction as F
from pathlib import Path
import json

checks={}
def ck(name, condition):
    if not condition:
        raise AssertionError(name)
    checks[name]=True

def build(vel, X, events, links=(), eps=F(1)):
    m=len(vel); cur=list(map(F,vel)); groups=list(range(m))
    # Each entry is [segment start (None = -infinity), affine origin, velocity].
    hist=[[[None,F(0),cur[p]]] for p in range(m)]
    last=[None]*m; times=[]; energy=sum(v*v for v in cur); prefix_energy=[]
    def move_group(g, delta):
        for p in range(m):
            if groups[p]==g:
                for seg in hist[p]: seg[1]+=delta
    for p,q,y in links:
        assert groups[p]!=groups[q]
        gp,gq=groups[p],groups[q]
        move_group(gq,F(y)+hist[p][0][1]-hist[q][0][1])
        groups=[gp if g==gq else g for g in groups]
    for kind,p,q,t in events:
        Ap,Aq=hist[p][-1][1],hist[q][-1][1]
        u=cur[p]-cur[q]
        if kind=='M':
            assert groups[p]!=groups[q]
            t=F(t)
            if u>=0: return {'Q':True,'success':False,'times':times}
            # geometric normal +1: x_p-x_q=eps and incoming u<0
            gp,gq=groups[p],groups[q]
            move_group(gq,Ap+t*cur[p]-eps-(Aq+t*cur[q]))
            groups=[gp if g==gq else g for g in groups]
        else:
            assert groups[p]==groups[q]
            if u==0: return {'Q':True,'success':False,'times':times}
            # Unique entering crossing for a collinear relative flight.
            entering=eps if u<0 else -eps
            t=(entering-(Ap-Aq))/u
            lower=max((v for v in (last[p],last[q]) if v is not None),default=None)
            if lower is not None and t<lower:
                return {'Q':True,'success':False,'times':times}
        if times and t<=times[-1]:
            return {'Q':False,'success':False,'times':times+[t]}
        xp=hist[p][-1][1]+t*cur[p]; xq=hist[q][-1][1]+t*cur[q]
        cur[p],cur[q]=cur[q],cur[p] # elastic equal-mass collinear reflection
        hist[p].append([t,xp-t*cur[p],cur[p]])
        hist[q].append([t,xq-t*cur[q],cur[q]])
        last[p]=last[q]=t; times.append(t)
        prefix_energy.append(sum(v*v for v in cur))
    move_group(groups[0],F(X)-hist[0][0][1])
    return {'Q':True,'success':True,'times':times,'hist':hist,
            'energy':energy,'prefix_energy':prefix_energy}

def phase(h,p,t):
    seg=h['hist'][p][0]
    for nxt in h['hist'][p][1:]:
        if nxt[0]<=t: seg=nxt
    return seg[1]+t*seg[2],seg[2]

v=[F(-1),F(0),F(3),F(4)]
first=[('M',0,1,F(1,5)),('M',1,2,F(2,5)),('R',0,1,None)]
oldbad=build(v,0,first+[('M',0,3,F(9,20))])
ck('counterchart_strict_redundant_time',oldbad['times']==[F(1,5),F(2,5),F(7,15),F(9,20)])
ck('counterchart_prefix_Q_rejects',not oldbad['Q'] and not oldbad['success'])
valid_events=first+[('M',0,3,F(1,2))]
base=build(v,F(2,7),valid_events)
ck('chronological_variant_accepted',base['success'] and base['Q'])
ck('all_lines_energy_conserved',all(e==base['energy']==26 for e in base['prefix_energy']))
for theta in (F(-3),F(-1,7),F(0),F(2,9),F(4)):
    shifted_events=[(k,p,q,t+theta if t is not None else None) for k,p,q,t in valid_events]
    shifted=build(v,F(2,7)-theta*v[0],shifted_events)
    assert shifted['success']
    assert shifted['times']==[t+theta for t in base['times']]
    for t in (F(-4),F(0),F(1,5),F(2,5),F(7,15),F(1,2),F(1),F(5)):
        for p in range(4): assert phase(shifted,p,t+theta)==phase(base,p,t)
    badshift=[(k,p,q,t+theta if t is not None else None) for k,p,q,t in first+[('M',0,3,F(9,20))]]
    assert not build(v,-theta*v[0],badshift)['Q']
ck('prefix_Q_and_all_segment_covariance_under_rational_shifts',True)
# No-merger history with one physical initial-link coordinate.
link_events=[('R',0,1,None)]
linked=build([1,0],0,link_events,[(0,1,F(3))])
ck('initial_link_redundant_time',linked['success'] and linked['times']==[F(2)])
for theta in (F(-3),F(-1,3),F(5,4),F(4)):
    sh=build([1,0],-theta,link_events,[(0,1,F(3)+theta)])
    assert sh['success'] and sh['times']==[F(2)+theta]
    for t in (F(-4),F(0),F(2),F(3),F(7)):
        for p in range(2): assert phase(sh,p,t+theta)==phase(linked,p,t)
ck('initial_link_shear_and_covariance',True)
sh=build([1,0],F(3),link_events,[(0,1,F(0))])
ck('extended_input_velocity_can_differ_at_fixed_birth_time',sh['success'] and phase(sh,0,F(0))[1]==0)
for m in range(1,15):
    for p in range(m):
        for h in range(1,7):
            assert -2*(m-h)+2*(m-1-p)+2*p==2*(h-1)
ck('cylinder_preserves_connected_root_scale',True)
ck('exact_centering_exponent',-1+F(21,20)*F(21,22)==F(1,440))
ck('dyadic_mu_exponent',-1+F(3,2)*4*F(1,8)==F(-1,4))
ck('microscopic_third_moment_mu_exponent',1-F(3,2)==F(-1,2))
# alpha^-1 * mu^3 / mu^(3/2) = mu^3; mu=eps^-2 -> eps^(P-6)
ck('microscopic_remainder_mu_exponent',F(3,2)+3-F(3,2)==3)
# second-moment leading union: alpha^-1 * mu*alpha / mu = 1
ck('second_moment_union_is_constant',F(3,2)+(1-F(3,2))-1==0)
result={'status':'PASS','count':len(checks),'checks':checks,
        'method':'exact rational arithmetic, finite counterchart/valid variant/initial-link charts and exponents only',
        'full_analytic_or_stochastic_certificate':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
