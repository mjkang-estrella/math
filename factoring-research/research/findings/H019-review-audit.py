#!/usr/bin/env python3
"""One frozen independent H019 witness replay; no original module imports.

Direct binomial expansion is accumulated by original monomial, using integer
Gaussian powers and a binomial-coefficient recurrence. The original reference
uses the same mathematical identity; this source does not call/copy its helpers.
Geometry uses products of independently reduced pair fractions. No rootfinding.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import itertools
import json
import math
import os
import random
import signal
import subprocess
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ARCHIVE = HERE / 'H019-certificate-evidence'
OUT = HERE / 'H019-review-evidence'
FREEZE = HERE / 'H019-review-freeze.json'
CASES = [(4096,15),(16384,22),(65536,34),(262144,52)]
CONTROL_IDS = ['sqrt2-correct','imaginary-correct','zero-incorrect','duplicate-disks','repeated-polynomial']
Q, S, P = 2**40, 2**24, 65537
TQ = Q//S


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def create(path, data):
    with path.open('x') as stream:
        json.dump(data, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def checkpoint(data):
    pending = OUT/'outcomes.pending'
    with pending.open('w') as stream:
        json.dump(data, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(pending, OUT/'outcomes.json')


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def same(a,b,label):
    require(a == b, label)


def number_record(value):
    require(value >= 0, 'nonnegative hash operand')
    return {'bits':value.bit_length(), 'sha256':hashlib.sha256(value.to_bytes((value.bit_length()+7)//8,'big')).hexdigest()}


class Ledger:
    def __init__(self, case):
        self.case = case
        self.start = time.monotonic()
        self.last = self.start
        self.stage = 'loading'
        self.counters = {}
        self.stage_seconds = {}

    def add(self, key, amount=1):
        self.counters[key] = self.counters.get(key,0)+amount

    def event(self, stage, **details):
        now = time.monotonic()
        self.stage_seconds[self.stage] = self.stage_seconds.get(self.stage,0.0)+now-self.last
        self.last, self.stage = now, stage
        entry = {'id':self.case,'stage':stage,'elapsed_seconds':now-self.start,
                 'counters':dict(self.counters),'stage_seconds':dict(self.stage_seconds),**details}
        with (OUT/(self.case+'-events.jsonl')).open('a') as stream:
            stream.write(json.dumps(entry,sort_keys=True,allow_nan=False)+'\n')
            stream.flush()
            os.fsync(stream.fileno())


def squarefree(f, archived, ledger):
    derivative = [i*f[i] for i in range(1,len(f))]
    if archived['unit']:
        s, t = archived['s'], archived['t']
        require(all(type(x) is int and 0 <= x < P for x in s+t),'Bezout domain')
        # Accumulate contributions by output degree, independently of EEA.
        for degree in range(max(len(s)+len(f)-1,len(t)+len(derivative)-1)):
            total = 0
            for a,b in ((s,f),(t,derivative)):
                for i in range(max(0,degree-len(b)+1),min(degree+1,len(a))):
                    total += a[i]*b[degree-i]
                    ledger.add('bezout_products')
            same(total % P, int(degree == 0), 'modular Bezout identity')
        ledger.add('bezout_identities')
        return True
    # The only archived negative control is explicitly (X-1)^2.
    # Direct identities prove its gcd with 2(X-1), without invoking EEA.
    same(f,[1,-2,1],'negative squarefree control polynomial')
    same(sum(f),0,'repeated root f(1)')
    same(sum(derivative),0,'repeated root derivative(1)')
    same(derivative,[-2,2],'linear nonzero derivative')
    same(archived,{'unit':False,'gcd_degree':1},'negative modular gcd degree')
    ledger.add('repeated_root_identities')
    return False


def taylor_array(f, center, ledger):
    d = len(f)-1
    x,y = center
    powers = [(1,0)]
    for power in range(1,d+1):
        re,im = powers[-1]
        powers.append((x*re-y*im,x*im+y*re))
    ledger.add('gaussian_power_products',d)
    qpow = [Q**i for i in range(d+1)]
    values = [[0,0] for _ in range(d+1)]
    for i,fi in enumerate(f):
        choose = 1
        for j in range(i+1):
            factor = fi*choose*qpow[d-i+j]
            re,im = powers[i-j]
            values[j][0] += factor*re
            values[j][1] += factor*im
            ledger.add('binomial_terms')
            if j<i:
                choose = choose*(i-j)//(j+1)
    return values


def verify_disks(f, centers, count, R, archived, ledger):
    same(len(centers),count,'disk count')
    require(all(len(z)==2 and all(type(x) is int for x in z) for z in centers),'disk coordinate domain')
    gate = 'accepted'
    if R is not None:
        require(R*Q>TQ,'containment radius domain')
        for x,y in centers:
            require(x*x+y*y<(R*Q-TQ)**2,'strict disk containment')
            ledger.add('containment_predicates')
    for i,j in itertools.combinations(range(count),2):
        dx,dy = (centers[i][a]-centers[j][a] for a in range(2))
        ledger.add('disjointness_predicates')
        if dx*dx+dy*dy <= (2*TQ)**2:
            gate='disjointness'
    checked=[]
    if gate=='accepted':
        d=len(f)-1
        for index,center in enumerate(centers):
            ledger.event('taylor_disk',disk_index=index)
            A=taylor_array(f,center,ledger)
            # Multiply l1*t > u0+sum uj*t^j by Q^d*S^d.
            lhs=max(abs(c) for c in A[1])*S**(d-1)
            rhs=sum((abs(a)+abs(b))*S**(d-j) for j,(a,b) in enumerate(A) if j!=1)
            serialized=''.join(hex(a)+','+hex(b)+'\n' for a,b in A).encode('ascii')
            row={'index':index,'lhs_hex':hex(lhs),'rhs_hex':hex(rhs),
                 'lhs':number_record(lhs),'rhs':number_record(rhs),
                 'taylor_sha256':hashlib.sha256(serialized).hexdigest(),'strict':lhs>rhs}
            checked.append(row)
            ledger.add('taylor_predicates')
            ledger.add('taylor_positive' if lhs>rhs else 'taylor_negative')
            if lhs<=rhs:
                gate='disk_rouche'
                break
    actual={'accepted':gate=='accepted','gate':gate,'checks':checked}
    same(actual,archived,'entire archived disk witness')
    return gate


def geometry(centers, archived, ledger):
    k=len(centers)
    t=Fraction(1,S)
    coords=[tuple(Fraction(a,Q) for a in z) for z in centers]
    upper=[max(Fraction(1),abs(a)+abs(b)+t) for a,b in coords]
    same([int(u*Q) for u in upper],archived['U_times_Q'],'all root modulus upper bounds')
    pair={}
    rows=[]
    for i,j in itertools.combinations(range(k),2):
        distance=max(abs(coords[i][a]-coords[j][a]) for a in range(2))-2*t
        distance=max(Fraction(0),distance)
        delta=distance/(upper[i]*upper[j])
        pair[i,j]=delta
        rows.append({'i':i,'j':j,'L_times_Q':int(distance*Q),
                     'delta_lower_num_hex':hex(delta.numerator),'delta_lower_den_hex':hex(delta.denominator)})
        ledger.add('geometry_pairs')
    same(rows,archived['pairs'],'all normalized pair lower bounds')
    best=None
    arg=None
    for i,j,l in itertools.combinations(range(k),3):
        value=pair[i,j]*pair[i,l]*pair[j,l]/6
        if best is None or value<best:
            best,arg=value,[i,j,l]
        ledger.add('geometry_triples')
    require(best is not None and best>0,'strictly positive triple minimum')
    same(archived['positive'],True,'archived kappa positivity')
    same(arg,archived['minimizing_triple'],'lexicographic minimizing triple')
    same(hex(best.numerator),archived['kappa_num_hex'],'reduced kappa numerator')
    same(hex(best.denominator),archived['kappa_den_hex'],'reduced kappa denominator')
    return best,arg


def compare_count(N,d,H,h,kappa,archived,ledger):
    k=d-2
    exponent=5*d*(k-2)
    x,y=kappa.numerator,kappa.denominator
    lf=[[hex(x),exponent],[hex(h),exponent],[hex(N),9]]
    rf=[[hex(y),exponent],[hex(20736),5*d],[hex(2),10*d],
        [hex(12),5*d*d],[hex(d+1),5*d],[hex(H),5*d*(d+6)]]
    same(lf,archived['lhs_factors'],'all left exact operands and exponents')
    same(rf,archived['rhs_factors'],'all right exact operands and exponents')
    same(exponent,archived['exponent'],'5d(k-2) exponent')
    # Independent product tree through math.prod: no candidate grouping/shift.
    lhs=math.prod(pow(int(base,16),power) for base,power in lf)
    rhs=math.prod(pow(int(base,16),power) for base,power in rf)
    ledger.add('count_product_powers',len(lf)+len(rf))
    left,right=number_record(lhs),number_record(rhs)
    same(left,archived['lhs'],'left product width and hash')
    same(right,archived['rhs'],'right product width and hash')
    decision=lhs>=rhs
    same(decision,archived['ge'],'equation 11 decision with equality accepted')
    # This is an exact containing-cube count, never an enumerated population.
    count=(h-1)*(2*h-1)*(2*h-1)+k
    same(hex(count),archived['primitive_upper_count_hex'],'trial count expression')
    return {'equation_11':decision,'exponent':exponent,'lhs':left,'rhs':right,
            'trial_count_hex':hex(count),'trial_count_bits':count.bit_length(),
            'certified_upper_bound':decision}


def research(case,ledger):
    n,d=next((n,d) for n,d in CASES if case==f'n{n}-d{d}')
    payload=read(ARCHIVE/(case+'-input.json'))
    same(set(payload),{'N_hex'},'N-only input object')
    N=int(payload['N_hex'],16)
    w=read(ARCHIVE/(case+'-witness.json'))
    result=read(ARCHIVE/(case+'-result.json'))
    ledger.event('base_identity')
    require(N>1 and N%2==1 and N.bit_length()==n,'public input domain')
    same([w['n'],w['d']],[n,d],'public degree map')
    m=int(w['m_hex'],16)
    require(m>=2 and m**d<=N<(m+1)**d,'exact base root enclosure')
    f=[]
    quotient=N
    while quotient:
        quotient,digit=divmod(quotient,m)
        f.append(digit)
    same(f,[int(c,16) for c in w['f_hex']],'complete ordinary base digit reconstruction')
    require(len(f)==d+1 and f[-1]==1 and all(0<=c<m for c in f),'degree, monicity, digit bounds')
    evaluation=0
    for coefficient in reversed(f):
        evaluation=evaluation*m+coefficient
    same(evaluation,N,'full f(m)=N')
    same(w['base_ok'],True,'reported base status')
    hb=(67473*n-1)//(20000*d*d)+1
    H=2**hb
    same([w['hbits'],w['H_hex']],[hb,hex(H)],'fixed height')
    h=int(w['hstar_hex'],16)
    require(1<=h<=H and (h-1)**5<H**4<=h**5,'exact ceiling fifth-root cutoff')
    ledger.add('base_identities')
    ledger.event('squarefree')
    require(squarefree(f,w['squarefree'],ledger),'squarefree full polynomial')
    ledger.event('global_root_count')
    R=2*H+2
    left=f[d-2]*R**(d-2)
    right=sum(abs(c)*R**j for j,c in enumerate(f) if j!=d-2)
    require(left>right,'strict coefficient d-2 dominance')
    same(w['dominance'],{'R_hex':hex(R),'index':d-2,'strict':True,
                         'lhs':number_record(left),'rhs':number_record(right)},'global dominance witness')
    ledger.add('global_dominance_predicates')
    ledger.event('proposal_metadata_only')
    approx=w['approximation']
    require(approx['converged'] is True and 1<=approx['sweeps']<=500,'recorded convergence metadata')
    correction=float.fromhex(approx['max_correction_float_hex'])
    require(math.isfinite(correction) and 0<=Fraction(correction)<=Fraction(1,2**42),'recorded correction cutoff')
    same(len(approx['centers_float_hex']),d-2,'recorded proposed center count')
    rounded=[]
    for row in approx['centers_float_hex']:
        floats=[float.fromhex(x) for x in row]
        require(all(math.isfinite(x) for x in floats),'recorded finite centers')
        rounded.append([round(Fraction(x)*Q) for x in floats])
    same(rounded,w['disks'],'exact nearest-grid rationalization of recorded centers')
    ledger.event('disk_coverage')
    same(verify_disks(f,w['disks'],d-2,R,w['disk_verification'],ledger),'accepted','full-f inside disk coverage')
    ledger.event('normalized_geometry')
    kappa,arg=geometry(w['disks'],w['geometry'],ledger)
    ledger.event('count_comparison')
    data=compare_count(N,d,H,h,kappa,w['comparison'],ledger)
    status='pass' if data['equation_11'] else 'unknown'
    reason='certified_count' if data['equation_11'] else 'count_inequality'
    same([result['status'],result['reason'],result['reference_status'],result['reference_reason'],result['independent_match']],
         [status,reason,status,reason,True],'archived research and reference dispositions')
    if status=='pass':
        same(result['primitive_upper_count_hex'],data['trial_count_hex'],'passing result count')
        same([result['kappa_num_hex'],result['kappa_den_hex']],
             [hex(kappa.numerator),hex(kappa.denominator)],'passing result kappa')
    ledger.event('archived_counters')
    counters=result['counters']; k=d-2; sweeps=approx['sweeps']
    for key,value in {'aberth_sweeps':sweeps,'aberth_updates':sweeps*k,
                      'aberth_pair_reciprocals':sweeps*k*(k-1),
                      'candidate_disk_predicates':k,'reference_disk_predicates':k,
                      'candidate_geometry_pairs':math.comb(k,2),'reference_geometry_pairs':math.comb(k,2),
                      'candidate_geometry_triples':math.comb(k,3),'reference_geometry_triples':math.comb(k,3),
                      'reference_binomial_terms':k*(d+1)*(d+2)//2}.items():
        same(counters[key],value,'archived operation counter '+key)
    return {'audit_status':'verified','original_status':status,'original_reason':reason,
            'n':n,'d':d,'H_hex':hex(H),'hstar_hex':hex(h),'inside_disks':d-2,'outside_roots':2,
            'kappa_num_hex':hex(kappa.numerator),'kappa_den_hex':hex(kappa.denominator),
            'minimizing_triple':arg,**data}


def control(case,ledger):
    c=next(c for c in read(ARCHIVE/'controls.json')['controls'] if c['id']==case)
    w=read(ARCHIVE/('controls-'+case+'-witness.json'))
    result=read(ARCHIVE/('controls-'+case+'-result.json'))
    ledger.event('squarefree')
    sf=squarefree(c['f'],w['squarefree'],ledger)
    gate='squarefree'
    if sf:
        ledger.event('disk_verification')
        gate=verify_disks(c['f'],c['disks'],2,None,w['disk_verification'],ledger)
    same(gate,c['expected_gate'],'expected control gate')
    same(gate=='accepted',c['expected_accept'],'expected control decision')
    same(result,{'id':case,'status':'pass','candidate_accepted':c['expected_accept'],
                 'candidate_gate':gate,'reference_accepted':c['expected_accept'],
                 'reference_gate':gate},'original control outcome')
    return {'audit_status':'verified','original_status':'pass','accepted':gate=='accepted','gate':gate}


def worker(group):
    cases=CONTROL_IDS if group=='controls' else [group]
    for case in cases:
        ledger=Ledger(case)
        try:
            ledger.event('start')
            row=control(case,ledger) if group=='controls' else research(case,ledger)
        except Exception as error:
            row={'audit_status':'verification_failure' if isinstance(error,AssertionError) else 'error',
                 'exception':type(error).__name__,'message':str(error),'traceback':traceback.format_exc()}
        ledger.event('complete',audit_status=row['audit_status'])
        row.update(id=case,counters=ledger.counters,stage_seconds=ledger.stage_seconds,
                   elapsed_seconds=time.monotonic()-ledger.start)
        create(OUT/(case+'-result.json'),row)


def preflight():
    manifest=read(FREEZE)
    for row in manifest['files']:
        same(digest(ROOT/row['path']),row['sha256'],'review frozen source/input '+row['path'])
    frozen=read(ARCHIVE/'freeze.json'); seal=read(ARCHIVE/'seal.json')
    for row in seal['files']:
        same(digest(ARCHIVE/row['path']),row['sha256'],'sealed archive '+row['path'])
    for row in frozen['sources']:
        same(digest(ARCHIVE/row['snapshot']),row['sha256'],'original snapshot '+row['snapshot'])
    for row in frozen['inputs']:
        same(digest(ARCHIVE/row['path']),row['sha256'],'original frozen input '+row['path'])
    same(read(ARCHIVE/'completion.json')['seal_sha256'],digest(ARCHIVE/'seal.json'),'original completion link')
    trials=[[i,P%i] for i in range(2,math.isqrt(P)+1)]
    require(all(r for _,r in trials),'prime 65537 trial division')
    cert=read(ARCHIVE/'prime-certificate.json')
    same(cert['prime'],P,'fixed prime modulus')
    same(cert['trials'],trials,'all archived prime remainders')
    same(cert['prime_verified'],True,'archived prime status')
    rng=random.Random(1919)
    archived=read(ARCHIVE/'inputs.json')
    same(archived['seed'],1919,'one public RNG seed')
    same(len(archived['cases']),4,'fixed input denominator')
    inputs=[]
    for (n,d),row in zip(CASES,archived['cases']):
        # Regenerate exactly the archived draw rule; this is not a new sample.
        N=(1<<(n-1))|rng.getrandbits(n-1)|1
        case=f'n{n}-d{d}'
        same([row['id'],row['n'],row['d'],row['N_hex']],[case,n,d,hex(N)],'exact persistent-RNG input')
        path=ARCHIVE/(case+'-input.json')
        same(read(path),{'N_hex':hex(N)},'exact archived worker payload')
        same(digest(path),row['N_only_input_sha256'],'input list link')
        inputs.append({'id':case,'input_sha256':digest(path),'exact_draw_match':True})
    # Freeze already includes actual controls; independently reconstruct them.
    a=math.isqrt(2*Q*Q)
    if (2*a+1)**2 < 8*Q*Q:
        a+=1
    specs=[([-2,0,1],[[a,0],[-a,0]],True,'accepted'),
           ([1,0,1],[[0,Q],[0,-Q]],True,'accepted'),
           ([-2,0,1],[[0,0],[-a,0]],False,'disk_rouche'),
           ([-2,0,1],[[a,0],[a,0]],False,'disjointness'),
           ([1,-2,1],[[Q,0],[Q,0]],False,'squarefree')]
    controls=[dict(id=i,f=f,disks=z,expected_accept=a,expected_gate=g)
              for i,(f,z,a,g) in zip(CONTROL_IDS,specs)]
    same(read(ARCHIVE/'controls.json'),{'controls':controls},'all five expanded control definitions')
    # Check stage logging/order/caps without executing archived programs.
    events=[json.loads(line) for line in (ARCHIVE/'runner-events.jsonl').read_text().splitlines()]
    require(all(a['elapsed_seconds']<=b['elapsed_seconds'] for a,b in zip(events,events[1:])),'monotone recorded runner events')
    starts=[e for e in events if e['event']=='worker_start']
    same([e['id'] for e in starts],['controls']+[f'n{n}-d{d}' for n,d in CASES],'single logged original execution order')
    same([e['cap_seconds'] for e in starts],[3.0,12.0,12.0,12.0,12.0],'original recorded caps')
    outcome=read(ARCHIVE/'outcomes.json')
    same(outcome['disposition'],'inconclusive','original criterion disposition')
    same(outcome['research_tally'],{'pass':1,'unknown':3,'verification_failure':0,'error':0,'timeout':0,'unstarted':0},'fixed research denominator')
    for row in outcome['research']:
        same(row['exit_code'],0,'original normal worker exit')
        require(row['worker_wall_seconds']<=row['cap_seconds'],'original worker within cap')
    return {'audit_status':'verified','review_freeze_sha256':digest(FREEZE),'prime_trial_divisions':len(trials),
            'sealed_files':len(seal['files']),'frozen_sources':len(frozen['sources']),'frozen_inputs':len(frozen['inputs']),
            'inputs':inputs,'control_definitions_verified':5,'original_recorded_order_and_caps_verified':True}


def last_event(case):
    path=OUT/(case+'-events.jsonl')
    if not path.exists():
        return None
    valid=None
    for line in path.read_text().splitlines():
        try:
            valid=json.loads(line)
        except json.JSONDecodeError:
            pass
    return valid


class AuditDeadline(Exception):
    pass


def run():
    start=time.monotonic()
    if OUT.exists():
        raise SystemExit('REFUSED: review evidence exists; no second replay or overwrite')
    OUT.mkdir()
    ids=CONTROL_IDS+[f'n{n}-d{d}' for n,d in CASES]
    rows=[{'id':case,'audit_status':'unstarted'} for case in ids]
    outcome={'schema':'H019-independent-arithmetic-replay-v1','cases':rows,'complete':False,
             'review_freeze_sha256':digest(FREEZE)}
    checkpoint(outcome)
    active=None
    current=[]
    def kill():
        if active is not None and active.poll() is None:
            os.killpg(active.pid,signal.SIGKILL)
            active.wait()
    def alarm(signum,frame):
        kill()
        raise AuditDeadline('55 second internal deadline')
    signal.signal(signal.SIGALRM,alarm)
    signal.signal(signal.SIGTERM,alarm)
    signal.setitimer(signal.ITIMER_REAL,max(.001,55-(time.monotonic()-start)))
    try:
        outcome['preflight']=preflight()
        create(OUT/'preflight.json',outcome['preflight'])
        checkpoint(outcome)
        for group in ['controls']+[f'n{n}-d{d}' for n,d in CASES]:
            current=CONTROL_IDS[:] if group=='controls' else [group]
            remaining=53-(time.monotonic()-start)
            if remaining<=0:
                current=[]
                break
            cap=min(3 if group=='controls' else 12,remaining)
            launched=time.monotonic()
            with (OUT/(group+'-stdout.log')).open('x') as stdout, (OUT/(group+'-stderr.log')).open('x') as stderr:
                active=subprocess.Popen([sys.executable,'-B',str(Path(__file__).resolve()),'--worker',group],
                                        cwd=ROOT,stdout=stdout,stderr=stderr,start_new_session=True)
                timeout=False
                try:
                    code=active.wait(timeout=max(.001,cap-(time.monotonic()-launched)))
                except subprocess.TimeoutExpired:
                    timeout=True
                    kill()
                    code=active.returncode
            active=None
            for case in current:
                row=next(r for r in rows if r['id']==case)
                path=OUT/(case+'-result.json')
                if path.exists():
                    row.update(read(path))
                elif last_event(case) is not None:
                    row.update(audit_status='timeout' if timeout else 'error',
                               reason='worker_cap' if timeout else 'worker_exit_without_result',
                               last_flushed_event=last_event(case),partial_counters_only=True)
                else:
                    row.update(reason='batch_stopped_before_case')
                row.update(group=group,worker_exit_code=code,group_wall_seconds=time.monotonic()-launched,
                           group_cap_seconds=cap)
                if code!=0 and row['audit_status']=='verified':
                    row.update(audit_status='error',reason='abnormal_worker_exit_despite_result')
            current=[]
            checkpoint(outcome)
    except Exception as error:
        outcome['outer_exception']={'type':type(error).__name__,'message':str(error),'traceback':traceback.format_exc()}
    finally:
        kill()
        for case in current:
            row=next(r for r in rows if r['id']==case)
            path=OUT/(case+'-result.json')
            if path.exists():
                row.update(read(path))
            elif last_event(case) is not None:
                row.update(audit_status='timeout',reason='outer_deadline',last_flushed_event=last_event(case),partial_counters_only=True)
        categories=['verified','verification_failure','error','timeout','unstarted']
        outcome['audit_tally']={s:sum(r['audit_status']==s for r in rows) for s in categories}
        outcome['complete']=True
        outcome['all_nine_verified']=all(r['audit_status']=='verified' for r in rows) and outcome.get('preflight',{}).get('audit_status')=='verified'
        outcome['elapsed_before_final_write']=time.monotonic()-start
        checkpoint(outcome)
        files=[p for p in sorted(OUT.rglob('*')) if p.is_file()]
        seal={'files':[{'path':str(p.relative_to(OUT)),'sha256':digest(p),'bytes':p.stat().st_size} for p in files],
              'review_freeze_sha256':digest(FREEZE),'elapsed_before_seal_write':time.monotonic()-start}
        create(OUT/'seal.json',seal)
        elapsed=time.monotonic()-start
        create(OUT/'completion.json',{'seal_sha256':digest(OUT/'seal.json'),'elapsed_through_seal_seconds':elapsed,
                                      'within_55_seconds_through_seal':elapsed<=55,'audit_tally':outcome['audit_tally']})
        signal.setitimer(signal.ITIMER_REAL,0)
        print(json.dumps({'audit_tally':outcome['audit_tally'],'all_nine_verified':outcome['all_nine_verified'],
                          'elapsed_seconds':time.monotonic()-start},sort_keys=True),flush=True)


if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--worker':
        worker(sys.argv[2])
    elif len(sys.argv)==1:
        run()
    else:
        raise SystemExit('no arguments, or internal --worker GROUP only')
