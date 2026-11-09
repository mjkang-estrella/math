#!/usr/bin/env python3
"""Frozen one-shot fixed certificate/vector protocol. Standard library only."""
import time
START = time.perf_counter()
import datetime
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import struct
import subprocess
import sys
import tracemalloc

ROOT = Path(__file__).resolve().parent
STEM = 'W006-cyclotomic-validation-'
LIMITS = dict(total_seconds=60, case_seconds=1, events=20_000,
              traced_bytes=32*1024*1024, case_bytes=1024*1024,
              overall_bytes=16*1024*1024)
TARGETS = ((1610612737, 29), (3221225473, 30))
BASES = (2, 3, 5, 7, 11)
DEGREES = (2, 4, 8, 16)
RECORD = struct.Struct('<QQQQ')


def path(suffix):
    return ROOT / (STEM + suffix)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write_json(p, value):
    data = (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()
    with p.open('xb') as f:
        f.write(data)
    return len(data)


class Censored(Exception):
    pass


class Meter:
    def __init__(self, modulus, trace_path):
        self.modulus = modulus
        self.trace_path = trace_path
        self.trace = trace_path.open('xb')
        self.events = 0
        self.max_operand_bits = modulus.bit_length()
        self.max_unreduced_bits = 0
        self.squared_width_sum = 0
        self.check()

    def check(self):
        if time.perf_counter() - START >= LIMITS['case_seconds']:
            raise Censored('cooperative case time')
        if tracemalloc.get_traced_memory()[1] > LIMITS['traced_bytes']:
            raise Censored('soft traced allocation')

    def madd(self, x, y, acc):
        if self.events >= LIMITS['events']:
            raise Censored('event budget')
        # Reserve 64 KiB for metadata; 20,000 binary records use 640,000 bytes.
        if (self.events + 1) * RECORD.size > LIMITS['case_bytes'] - 65536:
            raise Censored('evidence budget')
        if self.events % 64 == 0:
            self.check()
        assert 0 <= x < self.modulus and 0 <= y < self.modulus
        assert 0 <= acc < self.modulus
        raw = x*y + acc
        result = raw % self.modulus
        self.trace.write(RECORD.pack(x, y, acc, result))
        width = max(x.bit_length(), y.bit_length(), acc.bit_length(),
                    self.modulus.bit_length())
        self.max_operand_bits = max(self.max_operand_bits, width)
        self.max_unreduced_bits = max(self.max_unreduced_bits, raw.bit_length())
        self.squared_width_sum += width*width
        self.events += 1
        return result

    def finish(self):
        self.trace.close()
        return dict(events=self.events, max_operand_bits=self.max_operand_bits,
                    max_unreduced_bits=self.max_unreduced_bits,
                    squared_width_sum=self.squared_width_sum,
                    trace_bytes=self.trace_path.stat().st_size,
                    trace_sha256=digest(self.trace_path),
                    trace_file=self.trace_path.name)


def binary_power(base, exponent, meter):
    value = 1
    base %= meter.modulus
    while exponent:
        if exponent & 1:
            value = meter.madd(value, base, 0)
        exponent >>= 1
        if exponent:
            base = meter.madd(base, base, 0)
    return value


def certificate(t, e, meter, result):
    power_two = 1 << e
    algebra = dict(t_equals_3_times_2e_plus_1=(t == 3*power_two + 1),
                   e_at_least_one=e >= 1, power_two=power_two,
                   power_two_squared=power_two*power_two,
                   strict_size_inequality=power_two*power_two > t,
                   exponent=(t-1)//2)
    result.update(hypotheses=algebra, tested_bases=[], proper_gcds=[],
                  status='UNKNOWN', witness=None)
    if not all(algebra[k] for k in ('t_equals_3_times_2e_plus_1',
                                   'e_at_least_one', 'strict_size_inequality')):
        result['reason'] = 'algebraic hypothesis failed'
        return
    for a in BASES:
        meter.check()
        entry = dict(base=a, gcd=math.gcd(a, t), start_event=meter.events,
                     residue=None, status='STARTED')
        result['tested_bases'].append(entry)
        if 1 < entry['gcd'] < t:
            g = entry['gcd']
            assert t % g == 0
            result['proper_gcds'].append(dict(factor=g, cofactor=t//g))
        residue = binary_power(a, (t-1)//2, meter)
        entry.update(residue=residue, end_event=meter.events,
                     multiplications=meter.events-entry['start_event'])
        if entry['gcd'] == 1 and residue == t-1:
            assert not result['proper_gcds']
            entry['status'] = 'PRIME_CERTIFICATE'
            result.update(status='PRIME_CERTIFIED', witness=a)
            break
        entry['status'] = 'FAILED_WITNESS'
    else:
        result['witness'] = 'NO_WITNESS'
        if result['proper_gcds']:
            result['status'] = 'COMPOSITE_BY_PROPER_GCD'
        result['reason'] = 'fixed menu exhausted without certificate'
    seen = len(result['tested_bases'])
    result['untested_bases'] = list(BASES[seen:])


def vector(n, length, meter, result):
    # Only this reviewed candidate module is loaded; no evaluator values are
    # given to fold. The runner supplies each explicitly paid arithmetic result.
    spec = importlib.util.spec_from_file_location('frozen_cyclic_candidate',
                                                  path('candidate.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    gen = module.fold(n, length)
    reply = None
    try:
        while True:
            request = gen.send(reply)
            reply = meter.madd(*request)
    except StopIteration as done:
        coefficients = done.value
    assert len(coefficients) == length
    gcds = [math.gcd(c, n) for c in coefficients]
    factors = []
    for g in gcds:
        if 1 < g < n:
            assert n % g == 0
            factors.append(dict(factor=g, cofactor=n//g))
    exponent = n-1
    convolution_count = exponent.bit_count() + exponent.bit_length()-1
    assert meter.events == length*length*convolution_count
    result.update(status='ALL_UNIT' if all(g == 1 for g in gcds)
                  else 'COMPLETED_NONUNIT', coefficients=coefficients, gcds=gcds,
                  proper_factors=factors, convolutions=convolution_count,
                  expected_events=length*length*convolution_count,
                  exponent_bits=exponent.bit_length(),
                  exponent_popcount=exponent.bit_count())


def worker(kind, modulus, parameter, name):
    assert tracemalloc.is_tracing(), 'invoke Python with -X tracemalloc=1'
    result = dict(kind=kind, modulus=modulus, parameter=parameter, status='UNKNOWN')
    meter = None
    try:
        meter = Meter(modulus, path(name+'.bin'))
        if kind == 'certificate':
            assert (modulus, parameter) in TARGETS
            certificate(modulus, parameter, meter, result)
        elif kind == 'vector':
            assert parameter in DEGREES
            vector(modulus, parameter, meter, result)
        else:
            raise ValueError('unsupported case')
        meter.check()
    except Censored as exc:
        result.update(status='UNKNOWN', reason=str(exc), censored=True)
    except Exception as exc:
        result.update(status='UNKNOWN', reason=type(exc).__name__+': '+str(exc),
                      censored=True)
    finally:
        if meter is not None:
            result.update(meter.finish())
        result['worker_elapsed_seconds'] = time.perf_counter()-START
        result['peak_traced_bytes'] = tracemalloc.get_traced_memory()[1]
        if result['worker_elapsed_seconds'] >= LIMITS['case_seconds']:
            result.update(status='UNKNOWN', reason='case time at serialization',
                          censored=True)
        if result['peak_traced_bytes'] > LIMITS['traced_bytes']:
            result.update(status='UNKNOWN', reason='allocation at serialization',
                          censored=True)
        print(json.dumps(result, sort_keys=True))


def run_case(kind, modulus, parameter, name, deadline):
    remaining = deadline-time.perf_counter()
    if remaining <= 0:
        return dict(kind=kind, modulus=modulus, parameter=parameter,
                    status='UNKNOWN', reason='unstarted: whole-run deadline')
    start = time.perf_counter()
    command = [sys.executable, '-B', '-X', 'tracemalloc=1', str(Path(__file__)),
               '--worker', kind, str(modulus), str(parameter), name]
    try:
        cp = subprocess.run(command, capture_output=True,
                            timeout=min(LIMITS['case_seconds'], remaining),
                            cwd=ROOT.parent.parent, check=False)
        if cp.returncode != 0:
            result = dict(status='UNKNOWN', reason='worker exit '+str(cp.returncode))
        else:
            result = json.loads(cp.stdout)
        if cp.stderr:
            result['stderr'] = cp.stderr.decode(errors='replace')[:16384]
    except subprocess.TimeoutExpired:
        result = dict(status='UNKNOWN', reason='hard subprocess deadline',
                      censored=True, events=None, peak_traced_bytes=None)
    except Exception as exc:
        result = dict(status='UNKNOWN', reason=type(exc).__name__+': '+str(exc))
    result.update(kind=kind, modulus=modulus, parameter=parameter,
                  cold_case_seconds=time.perf_counter()-start)
    if result['cold_case_seconds'] >= LIMITS['case_seconds']:
        result.update(status='UNKNOWN', reason='cold case time cap', censored=True)
    trace = path(name+'.bin')
    if trace.exists():
        result.update(trace_file=trace.name, trace_bytes=trace.stat().st_size,
                      trace_sha256=digest(trace))
    data = json.dumps(result, sort_keys=True, indent=2).encode()
    total = len(data)+1+(trace.stat().st_size if trace.exists() else 0)
    result['case_evidence_bytes_before_size_field'] = total
    if total + 256 > LIMITS['case_bytes']:
        result.update(status='UNKNOWN', reason='case evidence cap', censored=True)
    write_json(path(name+'.json'), result)
    return result


def main():
    assert tracemalloc.is_tracing(), 'invoke Python with -X tracemalloc=1'
    # An exclusive durable marker prevents a second execution, even after failure.
    marker = path('execution-started.json')
    write_json(marker, dict(started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            command='python3 -B -X tracemalloc=1 '+str(Path(__file__)),
                            one_run_only=True, pid=os.getpid()))
    freeze = json.loads(path('freeze.json').read_text())
    for entry in freeze['files']:
        p = ROOT.parent.parent / entry['path']
        assert digest(p) == entry['sha256'], 'freeze changed: '+str(p)
    deadline = START+LIMITS['total_seconds']
    certificates = []
    for index, (t, e) in enumerate(TARGETS, 1):
        certificates.append(run_case('certificate', t, e, 'case-target-'+str(index), deadline))
    vectors = []
    theorem_checks = []
    if all(c['status'] == 'PRIME_CERTIFIED' for c in certificates):
        p, q = (t for t, _ in TARGETS)
        n = p*q
        assert q == 2*p-1 and p < q < 2*p
        for length in DEGREES:
            bound = (length-1)**(length//2)
            check = dict(length=length, p_mod_L=p % length, p_gt_L_minus_1=p>length-1,
                         q=q, norm_bound=bound, q_gt_bound=q>bound)
            theorem_checks.append(check)
            assert check['p_mod_L'] == 1 and check['p_gt_L_minus_1'] and check['q_gt_bound']
            vectors.append(run_case('vector', n, length, 'case-L-'+str(length), deadline))
        combined = 'CERTIFIED_THEOREM_INSTANCE'
    else:
        n = None
        combined = 'UNKNOWN'
        for length in DEGREES:
            vectors.append(dict(kind='vector', parameter=length, status='UNKNOWN',
                                reason='unstarted: both target certificates required'))
    report = dict(protocol='W006 fixed certificate and folded-vector check', limits=LIMITS,
                  target_certificates=certificates, N=n, theorem_checks=theorem_checks,
                  vectors=vectors, combined_theorem_instance=combined,
                  freeze_sha256=digest(path('freeze.json')),
                  elapsed_seconds=time.perf_counter()-START,
                  parent_peak_traced_bytes=tracemalloc.get_traced_memory()[1],
                  verified_factoring_improvement='NONE')
    owned_bytes = sum(f.stat().st_size for f in ROOT.glob(STEM+'*') if f.is_file())
    for directory in (path('inputs'), path('sources')):
        owned_bytes += sum(f.stat().st_size for f in directory.rglob('*') if f.is_file())
    report['overall_evidence_bytes_before_outcomes'] = owned_bytes
    assert owned_bytes + 131072 < LIMITS['overall_bytes']
    if report['elapsed_seconds'] >= LIMITS['total_seconds']:
        report['run_status'] = 'UNKNOWN_WHOLE_RUN_DEADLINE'
    elif report['parent_peak_traced_bytes'] > LIMITS['traced_bytes']:
        report['run_status'] = 'UNKNOWN_PARENT_ALLOCATION'
    else:
        report['run_status'] = 'FINISHED'
    write_json(path('outcomes.json'), report)
    print(json.dumps(dict(run_status=report['run_status'],
                          combined=combined, N=n,
                          certificates=[c['status'] for c in certificates],
                          vectors=[v['status'] for v in vectors],
                          elapsed_seconds=report['elapsed_seconds']), sort_keys=True))


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        worker(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    else:
        main()
