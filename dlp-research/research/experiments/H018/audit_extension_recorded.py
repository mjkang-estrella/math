#!/usr/bin/env python3
"""One saved-evidence audit; never imports or reruns either H018 probe.

All numerical inputs are pinned recorded evidence. Affine scalar arithmetic is
used only to verify the recorded order certificate; transition checks consume
the saved endpoints. No curve search, point count, new orbit, or new feature is
sampled. Gaussian elimination independently certifies the saved prefix ranks.

The audit ledger counts arithmetic primitives, explicit array accesses, numeric
loop/index work, and assertion evaluations. An assertion is ONE audit check,
even if its predicate combines comparisons; provenance/schema/JSON/Python
administration is not expanded. This is a DIFFERENT instrumentation convention
from the candidate's bounded-word RAM ledger. Do not add the raw counts or
claim that the candidate's million-event allowance included this verification.
"""

import hashlib
import json
import sys
import time
from collections import Counter
from pathlib import Path


DIRECTORY = Path(__file__).resolve().parent
ROOT = DIRECTORY.parents[1]
PINS = {
    "extension_results.json": "acaaf3489a3a3bbddf6ae01f7980f4f79ea37ee48bfdc83f269ced9ec4ab4634",
    "bm_probe_extension.py": "f855b0b868fd01a9b7fcb51201bc968e5f0fe68b09491d9590acadc48907df65",
    "bm_probe.py": "0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7",
    "initial_results.json": "fc52157f888da32181c0b1ad749a965cc5539cf06f0e95fdefd26a00ee7843a0",
}
PROTOCOL_PINS = {
    "H018-bm-probe-v1.md": "6aea6695ec278f0804dcea3361a52d8d494bb1a3cf9f5559e73e74822a31094f",
    "H018-bm-probe-v2.md": "c7405b4dad545348cde3ee64b735dce8343d0f7f422fe73d6f2f8d89573bc22e",
}


class Audit:
    def __init__(self):
        self.started = time.monotonic()
        self.phase = "integrity_and_ledger"
        self.counts = Counter()
        self.phases = {}

    def tick(self, kind, n=1):
        self.counts[kind] += n
        self.phases.setdefault(self.phase, Counter())[kind] += n
        if time.monotonic() - self.started >= 60:
            raise RuntimeError("verification exceeded its separate 60-second guard")

    def check(self, condition, message):
        self.tick("assertion_check")
        if not condition:
            raise AssertionError(message)

    def add(self, x, y):
        self.tick("integer_add"); return x + y

    def sub(self, x, y):
        self.tick("integer_sub"); return x - y

    def mul(self, x, y):
        self.tick("integer_mul"); return x * y

    def rem(self, x, p):
        self.tick("integer_rem"); return x % p

    def div(self, x, y):
        self.tick("integer_div"); return x // y

    def lt(self, x, y):
        self.tick("comparison"); return x < y

    def le(self, x, y):
        self.tick("comparison"); return x <= y

    def eq(self, x, y):
        self.tick("comparison"); return x == y

    def read(self, values, i):
        self.tick("array_read"); return values[i]

    def write(self, values, i, x):
        self.tick("array_write"); values[i] = x

    def append(self, values, x):
        self.tick("array_write"); values.append(x)

    def fm(self, x, y, p):
        self.tick("modular_mul"); return (x * y) % p

    def fa(self, x, y, p):
        self.tick("modular_add"); return (x + y) % p

    def fs(self, x, y, p):
        self.tick("modular_sub"); return (x - y) % p

    def power(self, x, e, p):
        out = 1
        while not self.eq(e, 0):
            self.tick("bit_and")
            if not self.eq(e & 1, 0):
                out = self.fm(out, x, p)
            self.tick("bit_shift"); e >>= 1
            if not self.eq(e, 0):
                x = self.fm(x, x, p)
        return out

    def inverse(self, x, p):
        self.check(not self.eq(x, 0), "zero audit inverse")
        return self.power(x, self.sub(p, 2), p)

    def each(self, values):
        # Explicit traversal/index/condition accounting, not Python bytecode.
        i = 0
        while self.lt(i, len(values)):
            yield self.read(values, i)
            i = self.add(i, 1)


def prime(m, n):
    if m.lt(n, 2): return False
    d = 2
    while m.le(m.mul(d, d), n):
        if m.eq(m.rem(n, d), 0): return False
        d = m.add(d, 1)
    return True


def affine_add(m, left, right, p, a):
    """Independent affine formulas, not the candidate's Jacobian code."""
    m.tick("point_branch", 2)
    if left is None: return right
    if right is None: return left
    x, y = left; u, v = right
    if m.eq(x, u):
        if m.eq(m.fa(y, v, p), 0): return None
        numerator = m.fa(m.fm(3, m.fm(x, x, p), p), a, p)
        denominator = m.fm(2, y, p)
    else:
        numerator = m.fs(v, y, p); denominator = m.fs(u, x, p)
    slope = m.fm(numerator, m.inverse(denominator, p), p)
    xx = m.fs(m.fs(m.fm(slope, slope, p), x, p), u, p)
    yy = m.fs(m.fm(slope, m.fs(x, xx, p), p), y, p)
    return xx, yy


def certificate_scalar(m, k, point, p, a):
    """Right-to-left certificate verification only; no orbit generation."""
    out = None
    while not m.eq(k, 0):
        m.tick("bit_and")
        if not m.eq(k & 1, 0): out = affine_add(m, out, point, p, a)
        m.tick("bit_shift"); k >>= 1
        if not m.eq(k, 0): point = affine_add(m, point, point, p, a)
    return out


def hankel_rank(m, values, n, q):
    """Forward Gaussian elimination of H[i,j]=values[i+j], no BM replay."""
    m.check(len(values) >= 2*n-1, "insufficient saved Hankel entries")
    matrix = []
    i = 0
    while m.lt(i, n):
        row = []; j = 0
        while m.lt(j, n):
            m.append(row, m.read(values, m.add(i, j)))
            j = m.add(j, 1)
        m.append(matrix, row); i = m.add(i, 1)
    rank = 0; col = 0; pivots = []
    while m.lt(col, n):
        pivot = rank
        while m.lt(pivot, n):
            row = m.read(matrix, pivot)
            if not m.eq(m.read(row, col), 0): break
            pivot = m.add(pivot, 1)
        if m.eq(pivot, n):
            col = m.add(col, 1); continue
        if not m.eq(pivot, rank):
            upper = m.read(matrix, rank); lower = m.read(matrix, pivot)
            m.write(matrix, rank, lower); m.write(matrix, pivot, upper)
        pivot_row = m.read(matrix, rank)
        pivot_value = m.read(pivot_row, col)
        m.append(pivots, pivot_value)
        inverse = m.inverse(pivot_value, q)
        i = m.add(rank, 1)
        while m.lt(i, n):
            row = m.read(matrix, i); value = m.read(row, col)
            if not m.eq(value, 0):
                factor = m.fm(value, inverse, q); j = col
                while m.lt(j, n):
                    value = m.fs(m.read(row, j), m.fm(factor, m.read(pivot_row, j), q), q)
                    m.write(row, j, value); j = m.add(j, 1)
            i = m.add(i, 1)
        rank = m.add(rank, 1); col = m.add(col, 1)
    return rank, pivots


def stream_checks(m, stream, q):
    values = stream['prefix_including_any_uncommitted_last_input']
    trace = stream['completed_update_trace']; L = stream['completed_L']
    m.check(not stream['update_in_progress'] and len(values)==len(trace)==stream['completed_prefix_length'], 'uncommitted saved stream')
    old_L = 0; shift = 1; old_discrepancy = 1; i = 0
    for entry in m.each(trace):
        d = entry['discrepancy']
        changed = d != 0 and 2*old_L <= i
        expected_L = i+1-old_L if changed else old_L
        expected_shift = 1 if changed else shift+1
        m.check(entry['index']==i and entry['value']==m.read(values,i), 'trace index/value')
        m.check(entry['before_L']==old_L and entry['after_L']==expected_L and entry['degree_update']==changed, 'trace length chain')
        m.check(entry['before_shift']==shift and entry['after_shift']==expected_shift and entry['previous_discrepancy']==old_discrepancy, 'trace shift/discrepancy chain')
        m.check(m.fm(entry['ratio'],old_discrepancy,q)==d and (d!=0 or entry['ratio']==0), 'trace ratio')
        m.check(entry['reached_limit']==(expected_L>=stream['threshold']), 'trace threshold flag')
        if changed: old_discrepancy = d
        old_L = expected_L; shift = expected_shift; i = m.add(i,1)
    m.check(old_L==L and stream['threshold_reached']==(L>=stream['threshold']), 'terminal stream length')
    c = stream['current_connection_buffer_may_be_partial_on_cap']
    m.check(m.read(c,0)==1 and len(c)>L and all(x==0 for x in c[L+1:]), 'connection buffer')
    n = L
    while m.lt(n,len(values)):
        total = 0; j = 0
        while m.le(j,L):
            total = m.fa(total,m.fm(m.read(c,j),m.read(values,m.sub(n,j)),q),q)
            j = m.add(j,1)
        m.check(total==0,'saved recurrence fails'); n=m.add(n,1)
    return values


def main():
    if not sys.dont_write_bytecode: raise SystemExit('Use python3 -B')
    m=Audit(); report={'status':'in_progress','scope':'saved-evidence verification only; no probe import/rerun',
                     'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    try:
        for name,digest in PINS.items():
            m.check(hashlib.sha256((DIRECTORY/name).read_bytes()).hexdigest()==digest,'pinned artifact '+name)
        for name,digest in PROTOCOL_PINS.items():
            m.check(hashlib.sha256((ROOT/'hypotheses'/name).read_bytes()).hexdigest()==digest,'pinned protocol '+name)
        r=json.loads((DIRECTORY/'extension_results.json').read_text())
        prior=json.loads((DIRECTORY/'initial_results.json').read_text())
        prov=r['provenance']
        for key,name in [('extension_source_sha256','bm_probe_extension.py'),('prior_source_sha256','bm_probe.py'),('prior_output_sha256','initial_results.json')]:
            m.check(prov[key]==PINS[name],'recorded provenance '+key)
        m.check(prov['extension_protocol_sha256']==PROTOCOL_PINS['H018-bm-probe-v2.md'] and prov['prior_protocol_sha256']==PROTOCOL_PINS['H018-bm-probe-v1.md'],'recorded protocol provenance')
        m.check(r['status']=='completed_finite_diagnostic_only' and r['cap_hit'] is None and not r['phase_reservation_overruns'],'completion/cap flags')
        m.check(r['current_events']==508887 and r['cumulative_events']==580642 and r['prior_events_actually_debited']==71755,'event totals')
        m.check(r['cumulative_events']==r['current_events']+prior['events']==r['meter_recorded_events_including_successful_prior_debit'],'carry equality')
        phases=r['cumulative_phase_events']; kinds=r['cumulative_event_categories_with_prior_lump']; detail=r['cumulative_phase_event_categories']
        m.check(sum(phases.values())==sum(kinds.values())==r['cumulative_events'],'cumulative category sums')
        for phase,categories in detail.items():
            m.check(sum(categories.values())==phases[phase],'phase categories '+phase)
        for kind,count in kinds.items():
            m.check(sum(v.get(kind,0) for v in detail.values())==count,'global category '+kind)
        m.check(r['current_phase_events']=={k:v for k,v in phases.items() if k!='prior_diagnostic'},'current phase partition')
        m.check(r['current_event_categories']=={k:v for k,v in kinds.items() if k!='prior_run_events'},'current kind partition')
        m.check(sum(r['current_phase_events'].values())==sum(r['current_event_categories'].values())==r['current_events'],'current sums')
        m.check(phases['prior_diagnostic']==kinds['prior_run_events']==prior['events'],'prior category')
        reservations=r['cumulative_paper_phase_reservations']
        m.check(sum(reservations.values())==r['cumulative_paper_total']==868942,'paper sum')
        m.check(all(v<=reservations[k] for k,v in phases.items()) and r['cumulative_events']<=1000000,'reservations/cap')
        m.check(r['planted_control_validated'] and r['controls_completed'] and r['feature_sampling_completed'],'completion controls')

        f=r['fixture']; p,a,b,q=f['p'],f['a'],f['b'],f['q']; w=r['primitive_w']; G=(f['gx'],f['gy'])
        m.check((p,a,b,q,G,w)==(8191,1,5,8053,(0,789),2),'frozen recorded fixture')
        attempts=r['selection_attempts']; qs=r['q_candidates']
        m.check(qs==prior['q_candidates'] and len(qs)==39 and q!=p,'recertified candidate record')
        m.check([v['b'] for v in attempts]==[1,2,3,4,5],'selection order')
        m.check([[t['q'] for t in v.get('q_tests',[])] for v in attempts]==[qs,[],qs,qs,qs[:4]],'order-test schedule')
        rows=[t for v in attempts for t in v.get('q_tests',[])]
        m.check(len(rows)==f['order_tests']==121 and sum(t['is_zero'] for t in rows)==1 and rows[-1]['is_zero'],'order-test success position')
        m.check(attempts[1]=={'b':2,'outcome':'rational_two_torsion_at_minus_one'},'frozen filter')
        D=sum(t['q'].bit_length()-1 for t in rows); A=sum(t['q'].bit_count()-1 for t in rows); ell=sum(t['q'].bit_length() for t in rows); ordinary=A-1
        # Exactly one final inverse-point addition; no polynomial/BM replay.
        order={'array_write':121,'bit_and':D,'bit_shift':14*121,'comparison':2*D+3*ordinary+4+17*121+ell+121,
               'field_add':3*D+ordinary,'field_mul':5*D+15*ordinary+6,'field_square':8*D+5*ordinary+2,
               'field_sub':7*D+8*ordinary,'integer_add':121,'trace_field':5*121}
        m.check(order==detail['order_certification'],'order formula cost ledger')
        report['recorded_order_schedule']={'tests':121,'doubles':D,'ordinary_additions':ordinary,'inverse_point_additions':1}

        m.phase='fixture_certificate'
        m.check(prime(m,p) and prime(m,q) and q!=p and 2*q>8373,'prime/Hasse hypotheses')
        m.check(m.mul(181,181)<=m.mul(4,p)<m.mul(182,182) and (p+1-181,p+1+181)==(8011,8373),'exact integer Hasse interval')
        m.check(m.rem(m.add(4,m.mul(27,m.mul(b,b))),p)!=0,'nonsingularity')
        m.check(certificate_scalar(m,q,G,p,a) is None,'independent [q]G certificate')
        for candidate in m.each(qs): m.check(prime(m,candidate),'recorded q candidate primality')
        remaining=m.sub(q,1)
        for factor in m.each(r['q_minus_one_distinct_prime_factors']):
            m.check(prime(m,factor),'recorded factor prime')
            while m.eq(m.rem(remaining,factor),0): remaining=m.div(remaining,factor)
        m.check(remaining==1,'factor coverage')
        m.check(len(r['primitive_attempts'])==1 and r['primitive_attempts'][0]['passed'],'primitive attempt record')
        for test in m.each(r['primitive_attempts'][0]['tests']):
            exponent=m.div(m.sub(q,1),test['ell'])
            residue=m.power(w,exponent,q)
            m.check(exponent==test['exponent'] and residue==test['residue'] and residue!=1,'primitive residue')
        m.check([v['ell'] for v in r['primitive_attempts'][0]['tests']]==r['q_minus_one_distinct_prime_factors'],'all primitive tests')

        m.phase='saved_points_and_features'
        point_equations=0
        for attempt in m.each(attempts):
            if 'gx' not in attempt: continue
            x,y=attempt['gx'],attempt['gy']; bb=attempt['b']
            m.check(m.fm(y,y,p)==m.fa(m.fa(m.fm(m.fm(x,x,p),x,p),x,p),bb,p),'selected affine G equation')
            point_equations=m.add(point_equations,1)
            for test in m.each(attempt['q_tests']):
                x,y,z=test['multiple_x'],test['multiple_y'],test['multiple_z']
                m.check(all(0<=v<p for v in (x,y,z)) and test['is_zero']==(z==0),'recorded endpoint bounds')
                z2=m.fm(z,z,p); z4=m.fm(z2,z2,p); z6=m.fm(z4,z2,p)
                rhs=m.fa(m.fa(m.fm(m.fm(x,x,p),x,p),m.fm(x,z4,p),p),m.fm(bb,z6,p),p)
                m.check(m.fm(y,y,p)==rhs,'recorded Jacobian equation')
                point_equations=m.add(point_equations,1)
        streams=r['features']; samples=r['shared_affine_samples']
        m.check([v['name'] for v in streams]==['centered_x','centered_y','kappa','centered_formal_parameter'] and len(samples)==127,'feature names/sample count')
        previous=None; index=0; branch_sum=0
        for saved in m.each(samples):
            x,y=saved['x'],saved['y']; point=(x,y)
            m.check(saved['index']==index and 0<=x<p and 0<y<p,'saved sample bounds/index')
            m.check(m.fm(y,y,p)==m.fa(m.fa(m.fm(m.fm(x,x,p),x,p),x,p),b,p),'sample curve equation')
            if previous is None: m.check(point==G,'initial saved sample')
            else: m.check(affine_add(m,previous,previous,p,a)==point,'independent saved doubling transition')
            X=m.sub(x,p) if m.lt(4095,x) else x
            Y=m.sub(y,p) if m.lt(4095,y) else y
            numerator=m.sub(m.sub(m.sub(m.mul(Y,Y),m.mul(m.mul(X,X),X)),X),b)
            m.check(m.rem(numerator,p)==0,'exact saved kappa quotient')
            parameter=m.fs(0,m.fm(x,m.inverse(y,p),p),p)
            centered_parameter=m.sub(parameter,p) if m.lt(4095,parameter) else parameter
            expected=(m.rem(X,q),m.rem(Y,q),m.rem(m.div(numerator,p),q),m.rem(centered_parameter,q))
            fi=0
            for stream in m.each(streams):
                m.check(m.read(stream['prefix_including_any_uncommitted_last_input'],index)==expected[fi],'saved feature value')
                fi=m.add(fi,1)
            branch_sum=m.add(branch_sum,2*(x>4095)+2*(y>4095)+(parameter>4095))
            previous=point; index=m.add(index,1)
        orbit={'bit_and':126,'bit_shift':14*126,'comparison':22*126,'field_add':3*126,'field_mul':5*126,'field_square':8*126,'field_sub':7*126}
        m.check(orbit==detail['orbit_scalar'],'orbit scalar plus next-loop ledger')
        features={'array_read':508,'array_write':127,'bit_and':3302,'bit_shift':3302,'comparison':14731,
                  'field_add':254,'field_mul':3683,'field_square':3429,'field_sub':127,'integer_add':1139,
                  'integer_div':127,'integer_mul':381,'integer_rem':635,'integer_sub':635+branch_sum,'trace_field':382}
        m.check(features==detail['features'],'feature formula/branch ledger')
        report['recorded_points_verified']={'selection_point_equations':point_equations,'samples':index,'stored_transitions':index-1,'stored_feature_values':4*index}

        m.phase='saved_controls'
        planted,pseudo=r['controls']
        m.check(planted['name']=='planted_three_powers' and pseudo['name']=='fixed_LCG_not_an_iid_null','control names')
        planted_values=stream_checks(m,planted,q); pseudo_values=stream_checks(m,pseudo,q)
        m.check(len(planted_values)==16 and planted['completed_L']==3 and len(pseudo_values)==63 and pseudo['completed_L']==32,'control prefix lengths')
        i=0
        for value in m.each(planted_values):
            expected=m.fa(m.fa(1,m.fm(2,m.power(w,i,q),q),q),m.fm(3,m.power(w,m.mul(2,i),q),q),q)
            m.check(value==expected,'planted saved term'); i=m.add(i,1)
        state=18018
        for value in m.each(pseudo_values):
            state=m.rem(m.add(m.mul(1664525,state),1013904223),4294967296)
            m.check(value==m.rem(state,q),'LCG saved term')
        planted_rank,_=hankel_rank(m,planted_values,3,q)
        pseudo_rank,_=hankel_rank(m,pseudo_values,32,q)
        m.check(planted_rank==3 and pseudo_rank==32,'independent control ranks')
        report['control_ranks']={'planted':planted_rank,'fixed_LCG':pseudo_rank}

        m.phase='independent_feature_hankel_ranks'
        ranks={}; pivot_records={}
        for stream in m.each(streams):
            values=stream_checks(m,stream,q)
            m.check(len(values)==127 and stream['completed_L']==64 and stream['threshold']==64 and stream['threshold_reached'],'feature terminal lengths')
            rank,pivots=hankel_rank(m,values,64,q)
            ranks[stream['name']]=rank; pivot_records[stream['name']]=pivots
            m.check(rank==64,'independent feature Hankel rank is not64')
        report['feature_hankel_ranks']=ranks
        report['nonzero_pivot_records']=pivot_records
        report['status']='PASS'
        report['certified_scope']='Each saved127-term prefix has minimum recurrence length64; each exact admitted feature has no global representation with fewer than64 scalar powers.'
        report['limitations']=['No asymptotic or other-curve claim; no solver improvement.','Recorded failed order endpoints checked on-curve, not all independently scalar-recomputed.','Trace bookkeeping checked; final lower bounds certified by independent Gaussian elimination, not BM replay.','No new fixture, orbit, feature or target was sampled.']
    except Exception as exc:
        report['status']='FAIL_OR_INCOMPLETE'
        report['failure']=type(exc).__name__+': '+str(exc)
    report['candidate_events']={'current':508887,'prior':71755,'cumulative':580642,'unit':'candidate bounded-word modular RAM events'}
    report['separate_verification_ledger']={'instrumented_events':sum(m.counts.values()),'by_kind':dict(m.counts),'by_phase':{k:dict(v) for k,v in m.phases.items()},'unit':'audit arithmetic/access/loop/assertion events; composite assertions count once, unlike candidate RAM'}
    report['combined_work_accounting']={'candidate_RAM_events':580642,'verification_instrumented_events':sum(m.counts.values()),'raw_sum_omitted':'Different conventions; audit is additional disclosed verification work outside candidate cap.'}
    report['elapsed_before_report_encoding_seconds']=time.monotonic()-m.started
    print(json.dumps(report,indent=2,sort_keys=True))
    if report['status']!='PASS': raise SystemExit(1)


if __name__=='__main__': main()
