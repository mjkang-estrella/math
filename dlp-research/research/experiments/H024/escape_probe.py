#!/usr/bin/env python3
"""H024 finite escape gate; read protocol.md. No execution on import."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1] / 'H018' / 'bm_probe.py'
spec = importlib.util.spec_from_file_location('h024_meter_base', BASE)
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)
FIXTURES = ((59,28,27,73,(34,35)), (101,2,31,103,(0,43)),
            (251,1,4,271,(0,2)), (8191,1,5,8053,(0,789)))

class Curve:
    def __init__(self, m, p, a, b):
        self.m, self.f, self.a, self.b = m, base.Field(m,p), a, b
    def neg(self, p):
        if self.m.eq(p,None): return None
        return p[0], self.f.sub(0,p[1])
    def add(self, p, r):
        m,f=self.m,self.f
        if m.eq(p,None): return r
        if m.eq(r,None): return p
        x,y=p; v,w=r
        if m.eq(x,v):
            if m.eq(f.add(y,w),0): return None
            slope=f.mul(f.add(f.mul(3,f.square(x)),self.a), f.inverse(f.mul(2,y)))
        else: slope=f.mul(f.sub(w,y),f.inverse(f.sub(v,x)))
        z=f.sub(f.sub(f.square(slope),x),v)
        return z,f.sub(f.mul(slope,f.sub(x,z)),y)
    def scale(self, n, p):
        m=self.m; r=None
        while not m.eq(n,0):
            if not m.eq(m.band(n,1),0): r=self.add(r,p)
            n=m.shr(n,1)
            if not m.eq(n,0): p=self.add(p,p)
        return r


def require(m, condition, message):
    m.tick('assertion')
    if not condition: raise base.Invalid(message)


def fixture(m, params, reports):
    p,a,b,q,g=params; c=Curve(m,p,a,b); f=c.f; sf=base.Field(m,q)
    report=m.record(p=p,a=a,b=b,q=q,g=g,starts=[],N=0,D=0,trajectories=[],stop='incomplete',pending_transition=False)
    m.append(reports,report)
    m.phase='certification'
    require(m,base.prime_trial(m,p),'p composite')
    require(m,base.prime_trial(m,q),'q composite')
    require(m,not m.eq(f.add(f.mul(4,f.mul(f.square(a),a)),f.mul(27,f.square(b))),0),'singular')
    require(m,m.eq(f.square(g[1]),f.add(f.add(f.mul(f.square(g[0]),g[0]),f.mul(a,g[0])),b)),'G off curve')
    require(m,m.eq(c.scale(q,g),None),'wrong generator order')
    # q>4sqrt(p): at most one multiple of q in Hasse interval.
    require(m,m.lt(m.mul(16,p),m.mul(q,q)),'Hasse interval not narrow')
    require(m,m.le(m.mul(m.sub(q,m.add(p,1)),m.sub(q,m.add(p,1))),m.mul(4,p)),'q outside Hasse')
    m.phase='setup'
    target=c.scale(17,g)
    half=m.div(m.add(q,1),2)
    known=((None,0),(g,1),(c.neg(g),m.sub(q,1)),(c.add(g,g),2),(c.scale(half,g),half))
    m.tick('array_write',5)
    constants=(f.mul(2,g[1]),f.mul(3,g[0]))
    starts=[]; m.tick('bit_xor',2); r=7^p^q
    i=0
    while m.lt(i,8):
        r=m.rem(m.add(m.mul(1664525,r),1013904223),4294967296)
        m.tick('bit_xor'); label=m.rem(r^m.shr(r,16),q)
        m.append(starts,label); i=m.add(i,1)
    report['starts']=starts; m.tick('trace_field')

    def exception(point):
        i=0
        while m.lt(i,5):
            kp,k=m.read(known,i)
            if m.eq(point,kp): return True,k
            i=m.add(i,1)
        return False,0
    def canonical(point, aa, bb):
        # Caller has excluded the five known exceptional points.
        other=c.add(point,c.neg(g))
        u=f.sub(point[0],g[0]); v=f.sub(other[0],g[0])
        mu=f.mul(f.add(point[1],g[1]),f.inverse(u))
        require(m,m.eq(f.sub(f.sub(f.square(mu),constants[1]),u),v),'residual quadratic')
        if m.lt(v,u):
            point=c.add(g,c.neg(point)); u=v
            aa=sf.sub(1,aa); bb=sf.sub(0,bb)
        return point,aa,bb,mu,u
    def verify_relation(numerator,denominator):
        if m.eq(denominator,0): return 'fruitless',None
        answer=sf.mul(numerator,sf.inverse(denominator))
        require(m,m.eq(c.scale(answer,g),target),'bad recovered scalar')
        return 'verified',answer

    start=0
    while m.lt(start,8) and m.lt(report['D'],9):
        m.phase='start_construction'
        aa=m.read(starts,start); bb=1
        point=c.add(c.scale(aa,g),target)
        history=[]; step=0
        tr=m.record(start=start,transitions=0,escapes=0,termination=None,cycle=None,recovery=None)
        m.append(report['trajectories'],tr)
        while True:
            m.phase='exception_and_reference'
            require(m,m.eq(c.add(c.scale(aa,g),c.scale(bb,target)),point),'label invariant')
            exceptional,k=exception(point)
            if exceptional:
                m.phase='terminal_verification'
                tr['termination']='known_exception'
                tr['recovery']=verify_relation(sf.sub(k,aa),bb)
                break
            point,aa,bb,mu,u=canonical(point,aa,bb)
            m.phase='history'
            j=0; repeated=False
            while m.lt(j,len(history)):
                oldmu,olda,oldb,oldstep=m.read(history,j)
                if m.eq(mu,oldmu):
                    tr['termination']='repeat'; tr['cycle']=m.sub(step,oldstep)
                    m.phase='terminal_verification'
                    tr['recovery']=verify_relation(sf.sub(olda,aa),sf.sub(bb,oldb))
                    repeated=True; break
                j=m.add(j,1)
            if repeated: break
            if m.eq(step,32):
                tr['termination']='transition_cap'; break
            m.append(history,(mu,aa,bb,step))
            m.phase='regular_kernel'
            report['pending_transition']=True; m.tick('trace_field')
            report['N']=m.add(report['N'],1)
            mup=f.sub(f.mul(constants[0],f.inverse(u)),mu)
            z=f.sub(f.sub(f.square(mup),constants[1]),u)
            escape=m.lt(u,z)
            m.phase='affine_reference'
            reference=c.add(point,g)
            require(m,not m.eq(reference,None),'unexpected regular infinity')
            require(m,m.eq(reference,(f.add(g[0],z),f.sub(f.mul(mup,z),g[1]))),'translation mismatch')
            if escape:
                report['D']=m.add(report['D'],1); tr['escapes']=m.add(tr['escapes'],1)
                # Old representative, not the discarded translated candidate.
                m.phase='escape'
                point=c.add(point,point); aa=sf.mul(2,aa); bb=sf.mul(2,bb)
            else:
                point=reference; aa=sf.add(aa,1)
            step=m.add(step,1); tr['transitions']=step
            report['pending_transition']=False; m.tick('trace_field')
            if m.eq(report['D'],9):
                tr['termination']='permanent_block_rejection'; break
        start=m.add(start,1)
    m.phase='verdict'
    if m.eq(report['D'],9): report['stop']='ninth_escape'
    else: report['stop']='predeclared_block_completed'
    if m.eq(report['N'],0): report['verdict']='inconclusive_no_transitions'
    elif m.le(m.mul(21,report['N']),m.mul(620,report['D'])): report['verdict']='finite_gate_rejected'
    else: report['verdict']='not_rejected_not_a_gain'
    report['max_possible_block_trials']=256
    m.tick('trace_field',4)
    return report


def main():
    m=base.Meter(); reports=[]; error=None
    try:
        index=0
        while m.lt(index,4):
            fixture(m,m.read(FIXTURES,index),reports)
            index=m.add(index,1)
    except (base.Halt,base.Invalid) as exc:
        error=type(exc).__name__+': '+str(exc)
    result={'scope':'finite escape-rate gate only; no solver or timing improvement',
            'run_status':'inconclusive' if error else 'completed',
            'fixtures':reports,'error':error,'cap_hit':m.cap_hit,'events':m.total,
            'phase_events':m.by_phase,'event_categories':m.by_kind,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'base_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),
            'protocol_sha256':hashlib.sha256(Path(__file__).with_name('protocol.md').read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2))
    if error: raise SystemExit(2)

if __name__=='__main__': main()
