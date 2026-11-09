"""Bounded reduced-ring density diagnostic, not a factoring solver."""
import hashlib
import json
import math
import platform
import random
import time
from collections import Counter
from functools import cache
from pathlib import Path

CONFIG = {"seed": 9009, "bits": [32, 48], "samples": 2,
          "batch_sizes": [8, 16, 32], "stages": 64, "seconds": 55}


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def integer_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def integer_sub(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] -= x
    return trim(out)


def recurrence(mul, sub, half, base):
    @cache
    def psi(k):
        if k in base:
            return base[k]
        m = k//2
        if k % 2:
            return sub(mul(psi(m+2), mul(mul(psi(m), psi(m)), psi(m))),
                       mul(psi(m-1), mul(mul(psi(m+1), psi(m+1)), psi(m+1))))
        return half(mul(psi(m),
                        sub(mul(psi(m+2), mul(psi(m-1), psi(m-1))),
                            mul(psi(m-2), mul(psi(m+1), psi(m+1))))))
    return psi


def exact_half(a):
    assert all(x % 2 == 0 for x in a)
    return trim([x//2 for x in a])


BASE = {0: (0,), 1: (1,), 2: (2,), 3: (0, 0, -1), 4: (-32, 0, 0, -4)}


class Ring:
    def __init__(self, n, parameters, deadline):
        self.n, self.r, self.deadline = n, len(parameters), deadline
        self.counts = Counter()
        a = (1,)
        for x in parameters:
            a = tuple(v % n for v in integer_mul(a, (-x, 1)))
        self.a = a

    def reduce(self, p):
        out = [x % self.n for x in p]
        for k in range(len(out)-1, self.r-1, -1):
            lead = out[k]
            for i in range(self.r):
                out[k-self.r+i] = (out[k-self.r+i]-lead*self.a[i]) % self.n
        return trim(out[:self.r])

    def mul(self, a, b):
        if time.monotonic() >= self.deadline:
            raise TimeoutError
        self.counts['multiplications'] += 1
        self.counts['input_degree_slots'] += len(a)+len(b)
        self.counts['input_nonzero_coefficients'] += sum(x != 0 for x in a)+sum(x != 0 for x in b)
        out = self.reduce(integer_mul(a, b))
        self.counts['output_degree_slots'] += len(out)
        self.counts['output_nonzero_coefficients'] += sum(x != 0 for x in out)
        return out

    def sub(self, a, b):
        return trim([x % self.n for x in integer_sub(a, b)])

    def half(self, a):
        inv = (self.n+1)//2
        return trim([x*inv % self.n for x in a])


def scalar_recurrence(a, n):
    # Independent scalar arithmetic; equality here checks quotient-ring evaluation.
    @cache
    def f(k):
        if k <= 4:
            return (0, 1, 2, -a*a, -4*a*a*a-32)[k] % n
        m = k//2
        if k % 2:
            return (f(m+2)*pow(f(m), 3, n)-f(m-1)*pow(f(m+1), 3, n)) % n
        return (f(m)*(f(m+2)*f(m-1)**2-f(m-2)*f(m+1)**2)*((n+1)//2)) % n
    return f


def evaluate(coeff, x, n):
    out = 0
    for c in reversed(coeff):
        out = (out*x+c) % n
    return out


def prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))


def run(n, params, deadline, integer_reference):
    start = time.monotonic()
    ring = Ring(n, params, deadline)
    psi = recurrence(ring.mul, ring.sub, ring.half,
                     {k: ring.reduce(v) for k, v in BASE.items()})
    scalar = [scalar_recurrence(a, n) for a in params]
    rows = []
    status = 'complete'
    reason = None
    try:
        for j in range(1, CONFIG['stages']+1):
            if time.monotonic() >= deadline:
                raise TimeoutError
            values = psi(1 << j)
            for a, ref in zip(params, scalar):
                assert evaluate(values, a, n) == ref(1 << j), ('scalar', n, j, a)
            if j <= 4:
                assert values == ring.reduce(integer_reference(1 << j)), ('integer', n, j)
            rows.append({'j': j, 'degree': len(values)-1,
                         'nonzero_coefficients': sum(x != 0 for x in values),
                         'degree_slots': len(values), 'totals': dict(ring.counts)})
    except TimeoutError:
        status = 'partial'
        reason = 'deadline'
    except AssertionError as error:
        status = 'error'
        reason = repr(error)
    return {'N': n, 'r': len(params), 'parameters': params,
            'discriminant_gcds': [math.gcd((4*pow(a, 3, n)+27) % n, n) for a in params],
            'status': status, 'reason': reason, 'rows': rows,
            'counts': dict(ring.counts), 'seconds': time.monotonic()-start}


def main():
    here = Path(__file__).resolve().parent
    output = here/'result.json'
    if output.exists():
        raise SystemExit('Refusing to overwrite evidence.')
    start = time.monotonic()
    deadline = start+CONFIG['seconds']
    rng = random.Random(CONFIG['seed'])
    generation, moduli = [], []
    for bits in CONFIG['bits']:
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        selected, attempts = [], 0
        while len(selected) < CONFIG['samples'] and time.monotonic() < deadline:
            attempts += 1
            p, q = rng.randrange(lo, hi) | 1, rng.randrange(lo, hi) | 1
            if p != q and prime(p) and prime(q):
                n = p*q
                if n.bit_length() == bits and n not in selected:
                    selected.append(n)
        moduli.extend(selected)
        generation.append({'bits': bits, 'N': selected, 'attempts': attempts,
                           'sample_shortfall': CONFIG['samples']-len(selected)})
    integer_reference = recurrence(integer_mul, integer_sub, exact_half, BASE)
    results = []
    for n in moduli:
        for r in CONFIG['batch_sizes']:
            if time.monotonic() >= deadline:
                results.append({'N': n, 'r': r, 'status': 'unstarted'})
                continue
            params = []
            while len(params) < r:
                x = rng.randrange(n)
                if x not in params:
                    params.append(x)
            results.append(run(n, params, deadline, integer_reference))
    late = [(case, row) for case in results for row in case.get('rows', []) if row['j'] >= 8]
    dense = sum(10*row['nonzero_coefficients'] >= 9*case['r'] for case, row in late)
    fraction = dense/len(late) if late else None
    error = any(case['status'] == 'error' for case in results)
    disposition = ('soundness_failure' if error else 'finite_sparse_collapse_rejected'
                   if fraction is not None and fraction >= .9 else 'inconclusive')
    result = {'schema': 1, 'config': CONFIG, 'python': platform.python_version(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'protocol_sha256': hashlib.sha256((here.parents[1]/'hypotheses/H009.md').read_bytes()).hexdigest(),
              'generation': generation, 'results': results,
              'summary': {'status_counts': dict(Counter(c['status'] for c in results)),
                          'late_stages': len(late), 'dense_late_stages': dense,
                          'dense_fraction': fraction, 'disposition': disposition},
              'seconds': time.monotonic()-start,
              'scope': 'Materialized reduced-ring recurrence only; not a factoring benchmark or a universal finite-ring lower bound.'}
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'summary': result['summary'], 'seconds': result['seconds']}))


if __name__ == '__main__':
    main()
