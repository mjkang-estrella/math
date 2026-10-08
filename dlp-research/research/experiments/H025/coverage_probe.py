#!/usr/bin/env python3
"""H025 fixed exact finite coverage screen. Read protocol.md; no run on import."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1] / 'H018' / 'bm_probe.py'
spec = importlib.util.spec_from_file_location('h025_meter_base', BASE)
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)
PRIMES = (509, 1009)
DESIGNS = ('control', 'A', 'B')
INPUTS = ((0,0), (0,1), (1,0))  # (Q coefficient, G coefficient)


def require(m, condition, message):
    m.tick('assertion')
    if not condition: raise base.Invalid(message)


def floor_root(m, n):
    lo,hi=0,m.add(n,1)
    while m.lt(m.add(lo,1),hi):
        mid=m.div(m.add(lo,hi),2)
        if m.le(m.mul(mid,mid),n): lo=mid
        else: hi=mid
    return lo


def ceil_root(m, n):
    a=floor_root(m,n)
    return a if m.eq(m.mul(a,a),n) else m.add(a,1)


class Case:
    def __init__(self,m,q,design,reports):
        m.phase='case_setup'
        self.m,self.q,self.design=m,q,design
        self.f=base.Field(m,q)
        self.r=m.record(q=q,design=design,status='incomplete',blocks=[],phase=None)
        m.append(reports,self.r)  # preserve partial case before charged setup
        self.first=[]
        self.r['first_discovery_cost_plus_one']=self.first
        z=0
        while m.lt(z,q):
            m.append(self.first,0); z=m.add(z,1)
        self.covered=0; self.cross_count=0; self.inverse_cache={}
        self.cost=0; self.generated=0; self.mean=0
        self.max_records=3; self.candidates=0; self.zero_denominators=0
        self.cross=m.zeroes(q)
        m.phase='input_setup'
        m.tick('initial_input_record',3)
        m.tick('initial_input_comparison',3)
        self.mark(0,False); self.mark(1,False); self.mark(m.sub(q,1),False)
        m.phase='parameter_setup'
        require(m,base.prime_trial(m,q),'nonprime order')
        M=floor_root(m,m.div(q,2))
        bits=0; temp=q
        while m.lt(1,temp):
            temp=m.shr(temp,1); bits=m.add(bits,1)
        h=m.div(bits,16)
        if m.lt(h,1): h=1
        self.B=m.mul(h,m.add(m.mul(2,h),1))
        self.cap=m.mul(m.div(m.mul(3,ceil_root(m,q)),self.B),self.B)
        if m.eq(design,'control'):
            bs=(0,1,2); ss=(1,M,m.sub(0,m.add(M,1))); cs=(0,0,0)
        elif m.eq(design,'A'):
            bs=(0,1,3,7); ss=(1,M,m.sub(0,m.add(M,1)),m.add(M,2))
            cs=self.shifts(bs,m.div(q,17))
        else:
            require(m,m.eq(design,'B'),'unknown design')
            bs=(1,2,4,8); ss=(M,m.sub(0,m.add(M,1)),m.add(M,2),m.sub(0,m.add(M,3)))
            cs=self.shifts(bs,m.div(q,73))
        self.r.update(m.record(block_size=self.B,main_cap=self.cap,b=bs,s=ss,c=cs))
        self.main=(bs,ss,cs)

    def shifts(self, bs, D):
        m=self.m; result=[]; i=0
        while m.lt(i,len(bs)):
            b=m.read(bs,i); m.append(result,self.f.mul(D,self.f.square(b)))
            i=m.add(i,1)
        return result

    def inverse(self,e,build=False):
        m=self.m
        if m.eq(e,0): return None
        m.tick('inverse_cache_lookup')
        if e not in self.inverse_cache:
            require(m,build,'inverse not precomputed')
            value=self.f.inverse(e)
            m.tick('inverse_cache_write'); self.inverse_cache[e]=value
        m.tick('inverse_cache_read')
        return self.inverse_cache[e]

    def prepare_inverses(self,bs):
        m,f=self.m,self.f; i=0
        while m.lt(i,len(bs)):
            b=m.read(bs,i); self.inverse(f.add(b,0),True)
            j=0
            while m.lt(j,len(bs)):
                old=m.read(bs,j)
                self.inverse(f.sub(b,old),True); self.inverse(f.add(b,old),True)
                j=m.add(j,1)
            self.inverse(f.sub(b,1),True); self.inverse(f.add(b,1),True)
            i=m.add(i,1)

    def mark(self,k,cross):
        m=self.m
        m.tick('candidate_update'); self.candidates=m.add(self.candidates,1)
        self.r['partial_candidate_updates']=self.candidates
        if m.eq(m.read(self.first,k),0):
            m.write(self.first,k,m.add(self.cost,1)); self.covered=m.add(self.covered,1)
            self.r['partial_total_coverage']=self.covered
        if cross:
            if m.eq(m.read(self.cross,k),0):
                m.write(self.cross,k,1); self.cross_count=m.add(self.cross_count,1)

    def point(self,i,j,bs,ss,cs,los,his):
        m,f=self.m,self.f
        b=m.read(bs,i); s=m.read(ss,i); c=m.read(cs,i)
        a=f.add(c,f.mul(j,s))
        invb=self.inverse(f.add(b,0))
        if invb is not None: self.mark(f.mul(f.sub(0,a),invb),False)
        # Comparisons with supplied inputs; no inverse-log table.
        ip=0
        while m.lt(ip,3):
            oldb,olda=m.read(INPUTS,ip)
            sign=1
            while m.le(sign,2):
                minus=m.eq(sign,2)
                e=f.add(b,oldb) if minus else f.sub(b,oldb)
                inv=self.inverse(e)
                if inv is not None:
                    numerator=f.sub(f.sub(0,olda) if minus else olda,a)
                    self.mark(f.mul(numerator,inv),False)
                else: self.zero_denominators=m.add(self.zero_denominators,1)
                sign=m.add(sign,1)
            ip=m.add(ip,1)
        family=0
        while m.lt(family,len(bs)):
            low=m.read(los,family); high=m.read(his,family)
            if m.le(low,high):
                oldb=m.read(bs,family); olds=m.read(ss,family); oldc=m.read(cs,family)
                sign=1
                while m.le(sign,2):
                    minus=m.eq(sign,2)
                    inv=self.inverse(f.add(b,oldb) if minus else f.sub(b,oldb))
                    if inv is None:
                        self.zero_denominators=m.add(self.zero_denominators,1)
                    else:
                        olda=f.add(oldc,f.mul(low,olds))
                        numerator=f.sub(f.sub(0,olda) if minus else olda,a)
                        k=f.mul(numerator,inv)
                        step=f.mul(f.sub(0,olds) if minus else olds,inv)
                        r=low; is_cross=not m.eq(i,family)
                        # At most 14 charged events per visited candidate,
                        # including mark, label increment and loop comparison.
                        while m.le(r,high):
                            self.mark(k,is_cross)
                            k=f.add(k,step); r=m.add(r,1)
                    sign=m.add(sign,1)
            family=m.add(family,1)
        low=m.read(los,i); high=m.read(his,i)
        if m.lt(high,low): m.write(los,i,j); m.write(his,i,j)
        elif m.lt(j,low): m.write(los,i,j)
        else: m.write(his,i,j)

    def phase(self,name,bs,ss,cs,nblocks,centered,early):
        m=self.m; m.phase=name+'_setup'; self.r['phase']=name; m.tick('trace_field')
        self.prepare_inverses(bs)
        los=m.zeroes(len(bs)); his=[]; i=0
        while m.lt(i,len(bs)):
            m.append(his,-1); i=m.add(i,1)
        self.cross=m.zeroes(self.q); self.cross_count=0
        emitted=0; block=0
        while m.lt(block,nblocks):
            if early and m.eq(self.covered,self.q): break
            m.phase=name+'_enumeration'
            fam=m.rem(block,len(bs)); turn=m.div(block,len(bs))
            low=m.read(los,fam); high=m.read(his,fam)
            direction=1
            if centered and m.eq(turn,0): start=m.sub(0,m.div(self.B,2))
            elif centered and m.eq(m.rem(turn,2),0):
                start=m.sub(low,1); direction=-1
            else: start=m.add(high,1)
            before=self.covered
            self.mean=m.add(self.mean,m.mul(self.B,m.sub(self.q,before)))
            self.cost=m.add(self.generated,self.B)
            pending=m.record(phase=name,family=fam,start=start,direction=direction,
                completed_points=0,covered_before=before,block_end_cost=self.cost,
                provisional_mean_numerator=self.mean)
            self.r['pending_block']=pending
            pos=0
            while m.lt(pos,self.B):
                j=m.add(start,m.mul(direction,pos))
                self.point(fam,j,bs,ss,cs,los,his)
                pos=m.add(pos,1)
                pending['completed_points']=pos
            emitted=m.add(emitted,self.B); self.generated=m.add(self.generated,self.B)
            records=m.add(emitted,3)
            if m.lt(self.max_records,records): self.max_records=records
            lengths=[]; squares=0; i=0
            while m.lt(i,len(bs)):
                length=m.add(m.sub(m.read(his,i),m.read(los,i)),1)
                m.append(lengths,length); squares=m.add(squares,m.mul(length,length))
                i=m.add(i,1)
            ceiling=m.sub(m.mul(emitted,emitted),squares)
            m.append(self.r['blocks'],m.record(phase=name,family=fam,start=start,direction=direction,
                emitted_this_phase=emitted,total_keys=self.generated,covered_before=before,
                covered_after=self.covered,cross_union=self.cross_count,cross_ceiling=ceiling,
                lengths=lengths,mean_numerator_so_far=self.mean))
            self.r['pending_block']=None
            require(m,m.le(self.cross_count,ceiling),'cross union exceeds pair ceiling')
            block=m.add(block,1)
        return emitted

    def run(self):
        m=self.m; bs,ss,cs=self.main
        emitted=self.phase('main',bs,ss,cs,m.div(self.cap,self.B),m.eq(self.design,'B'),True)
        miss=m.sub(self.q,self.covered)
        self.r.update(m.record(main_failure_count=miss,expected_clear_records_numerator=m.mul(miss,m.add(emitted,3))))
        if not m.eq(miss,0):
            m.phase='fallback_setup'
            m.tick('search_record_clear',m.add(emitted,3))
            m.tick('initial_input_record',3); m.tick('initial_input_comparison',3)
            # Reinstalled public inputs already covered. No old main pairs.
            self.mark(0,False); self.mark(1,False); self.mark(m.sub(self.q,1),False)
            D=ceil_root(m,m.mul(2,self.q)); H=m.div(m.add(D,1),2)
            blocks_per=m.div(m.add(H,self.B),self.B)
            self.phase('fallback',(0,1),(1,m.sub(0,D)),(0,0),m.mul(2,blocks_per),False,False)
        m.phase='verification'
        require(m,m.eq(self.covered,self.q),'fallback incomplete')
        total=0; i=0
        while m.lt(i,self.q):
            v=m.read(self.first,i); require(m,not m.eq(v,0),'undiscovered scalar')
            total=m.add(total,m.sub(v,1)); i=m.add(i,1)
        require(m,m.eq(total,self.mean),'survival and first-discovery sums differ')
        self.r.update(m.record(status='completed',mean_numerator=self.mean,mean_denominator=self.q,
            maximum_search_records=self.max_records,candidate_updates=self.candidates,
            zero_denominator_checks=self.zero_denominators,total_generated_keys=self.generated))


def main():
    m=base.Meter(); reports=[]; gates=[]; error=None
    try:
        qi=0
        while m.lt(qi,2):
            q=m.read(PRIMES,qi); di=0; control=None
            while m.lt(di,3):
                design=m.read(DESIGNS,di); case=Case(m,q,design,reports); case.run()
                if m.eq(di,0): control=case.mean
                else:
                    passed=m.le(m.mul(20,case.mean),m.mul(19,control))
                    m.append(gates,m.record(q=q,design=design,five_percent_key_gate=passed))
                di=m.add(di,1)
            qi=m.add(qi,1)
    except (base.Halt,base.Invalid) as exc:
        error=type(exc).__name__+': '+str(exc)
    result={'scope':'exact finite generated-key coverage, not EC work or asymptotics',
        'status':'inconclusive' if error else 'completed','error':error,'cap_hit':m.cap_hit,
        'cases':reports,'gates':gates,'events':m.total,'phase_events':m.by_phase,
        'event_categories':m.by_kind,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'base_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),
        'protocol_sha256':hashlib.sha256(Path(__file__).with_name('protocol.md').read_bytes()).hexdigest()}
    print(json.dumps(result,indent=2))
    if error: raise SystemExit(2)

if __name__=='__main__': main()
