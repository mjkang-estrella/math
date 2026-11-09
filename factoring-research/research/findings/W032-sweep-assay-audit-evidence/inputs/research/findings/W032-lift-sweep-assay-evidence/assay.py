"""One frozen diagnostic. Never import/run to explore cases before freezing."""
import collections
import json
import math
import operator
import os
from pathlib import Path
import time
import traceback

ROOT = Path(__file__).resolve().parent


class StopBudget(Exception):
    pass


class CheckFailure(Exception):
    pass


def require(test, message):
    if not test:
        raise CheckFailure(message)


class Meter:
    def __init__(self, config, start, records, events):
        self.start = start
        self.deadline = start + config['global_seconds_cap'] - config['recording_reserve_seconds']
        self.cap = config['arithmetic_event_cap']
        self.count = 0
        self.group = None
        self.phase = 'initialization'
        self.records = records
        self.events = events
        self.ops = collections.Counter()
        self.phases = collections.Counter()
        self.max_width = 0
        self.record_counts = collections.Counter()

    def elapsed(self):
        return time.monotonic() - self.start

    def record(self, kind, **data):
        self.record_counts[kind] += 1
        self.records.write(json.dumps(dict(kind=kind, group=self.group,
            phase=self.phase, event_count=self.count, elapsed_s=self.elapsed(), **data),
            sort_keys=True) + '\n')
        self.records.flush()

    def op(self, name, function, *args):
        if self.count >= self.cap:
            raise StopBudget('global arithmetic event cap reached; next primitive not executed')
        if time.monotonic() >= self.deadline:
            raise StopBudget('global time allowance reached; final second reserved for recording')
        try:
            result = function(*args)
        except Exception as exc:
            self.record('primitive_failure', operation=name, operands=args,
                        error=repr(exc))
            raise
        results = result if isinstance(result, tuple) else (result,)
        aw = [abs(x).bit_length() for x in args]
        rw = [abs(x).bit_length() for x in results]
        self.count += 1
        self.ops[name] += 1
        self.phases[str(self.group) + ':' + self.phase] += 1
        self.max_width = max(self.max_width, *aw, *rw)
        self.events.write(json.dumps(dict(id=self.count, group=self.group,
            phase=self.phase, operation=name, operands=args, result=result,
            operand_bits=aw, result_bits=rw, elapsed_s=self.elapsed()),
            sort_keys=True) + '\n')
        self.events.flush()
        return result

    def add(self, a, b): return self.op('add', operator.add, a, b)
    def sub(self, a, b): return self.op('subtract', operator.sub, a, b)
    def mul(self, a, b): return self.op('multiply', operator.mul, a, b)
    def div(self, a, b): return self.op('floor_divide', operator.floordiv, a, b)
    def mod(self, a, b): return self.op('remainder', operator.mod, a, b)
    def divmod(self, a, b): return self.op('divmod', divmod, a, b)
    def gcd(self, a, b): return self.op('gcd', math.gcd, a, b)
    def inverse(self, a, b): return self.op('inverse', lambda x, y: pow(x, -1, y), a, b)
    def eq(self, a, b): return self.op('equal', operator.eq, a, b)
    def lt(self, a, b): return self.op('less_than', operator.lt, a, b)
    def le(self, a, b): return self.op('less_equal', operator.le, a, b)
    def absolute(self, a): return self.op('absolute', abs, a)
    def bits(self, a): return self.op('bit_length', int.bit_length, a)

    def power(self, base, exponent, modulus=None):
        result = 1
        if modulus is not None:
            base = self.mod(base, modulus)
        while self.lt(0, exponent):
            exponent, odd = self.divmod(exponent, 2)
            if odd:
                result = self.mul(result, base)
                if modulus is not None:
                    result = self.mod(result, modulus)
            if self.lt(0, exponent):
                base = self.mul(base, base)
                if modulus is not None:
                    base = self.mod(base, modulus)
        return result

    def exact(self, numerator, denominator, label):
        quotient, remainder = self.divmod(numerator, denominator)
        require(self.eq(remainder, 0), 'inexact division: ' + label)
        return quotient


def prime_at_least(start, meter, label):
    n = start
    while True:
        divisor = None
        if meter.lt(n, 2):
            prime = False
        elif meter.eq(n, 2):
            prime = True
        elif meter.eq(meter.mod(n, 2), 0):
            prime, divisor = False, 2
        else:
            prime = True
            d = 3
            while meter.le(meter.mul(d, d), n):
                if meter.eq(meter.mod(n, d), 0):
                    prime, divisor = False, d
                    break
                d = meter.add(d, 2)
        meter.record('prime_trial', label=label, n=n, prime=prime, divisor=divisor)
        if prime:
            return n
        n = meter.add(n, 1)


def outcome(c, n, meter):
    g = meter.gcd(c, n)
    if meter.eq(c, 0):
        category = 'zero'
    elif meter.eq(g, 1):
        category = 'unit'
    elif meter.eq(g, n):
        category = 'full_nonzero'
    else:
        require(meter.lt(1, g) and meter.lt(g, n), 'improper gcd classified proper')
        require(meter.eq(meter.mod(n, g), 0), 'proper gcd does not divide N')
        category = 'proper'
    return g, category


def horner(coefficients, a, modulus, meter):
    # Square the actual unwrapped input before reducing; its full width is paid.
    square = meter.mod(meter.mul(a, a), modulus)
    acc = coefficients[-1]
    for coefficient in reversed(coefficients[:-1]):
        acc = meter.mod(meter.add(meter.mul(acc, square), coefficient), modulus)
    return acc


def weighted_sum(weights, values, meter):
    result = 0
    for weight, value in zip(weights, values):
        result = meter.add(result, meter.mul(weight, value))
    return result


class SortThreshold:
    def __init__(self, item, meter):
        self.item, self.meter = item, meter

    def __lt__(self, other):
        return self.meter.lt(self.item['w'], other.item['w'])


def candidate(n, meter, state):
    """Candidate inputs: N, public meter, and an empty output object. No p or q."""
    meter.phase = 'candidate_setup'
    state['status'] = 'running'
    ell = meter.bits(n)
    R = meter.div(meter.add(ell, 3), 4)
    twoR = meter.mul(2, R)
    m = meter.add(twoR, 1)
    L = meter.sub(twoR, 2)
    state.update(N=n, bit_length=ell, R=R, m=m, L=L, a0=1,
                 guards=[], base=[], coefficients=[], thresholds=[],
                 intervals=[], maximal_segments=[], ties=[], factors=[])
    require(meter.le(2, R), 'R below stipulated branch')
    require(meter.lt(meter.add(1, m), n), 'base stencil too wide')
    good = True
    points = []
    for denominator in range(2, m + 1):
        g, category = outcome(denominator, n, meter)
        check = dict(kind='denominator_factor', value=denominator, gcd=g, category=category)
        state['guards'].append(check)
        meter.record('guard', check=check)
        if not meter.eq(g, 1):
            good = False
    for i in range(m + 1):
        a = meter.add(1, i)
        points.append(a)
        g, category = outcome(a, n, meter)
        check = dict(kind='initial_point', i=i, value=a, gcd=g, category=category)
        state['guards'].append(check)
        meter.record('guard', check=check)
        if not meter.eq(g, 1):
            good = False
    if not good:
        state['status'] = 'inapplicable_nonunit_branch'
        return state
    n2 = meter.mul(n, n)
    modulus = meter.power(n, twoR)
    radix = meter.power(n, L)
    top_place = meter.power(n, meter.sub(L, 1))
    bound = meter.power(4, R)
    state.update(N2=n2, modulus=modulus, radix=radix, top_place=top_place, bound=bound)
    weights = []
    binomial = 1
    for i in range(m + 1):
        parity = meter.mod(meter.sub(m, i), 2)
        weights.append(meter.sub(0, binomial) if parity else binomial)
        if meter.lt(i, m):
            binomial = meter.exact(meter.mul(binomial, meter.sub(m, i)),
                                   meter.add(i, 1), 'binomial weight')
    state['weights'] = weights
    require(meter.eq(weighted_sum(weights, [1] * len(points), meter), 0), 'weight sum')
    require(meter.eq(weighted_sum(weights, points, meter), 0), 'weighted affine sum')

    meter.phase = 'coefficient_recurrence'
    coefficients = state['coefficients']
    coefficients.append(1)
    meter.record('coefficient', j=0, value=1)
    for j in range(1, R):
        twice = meter.mul(2, j)
        odd = meter.sub(twice, 1)
        factor = meter.sub(meter.mul(odd, odd), n2)
        denominator = meter.mul(meter.mul(4, twice), meter.add(twice, 1))
        inverse = meter.inverse(denominator, modulus)
        value = meter.mod(meter.mul(coefficients[-1], n2), modulus)
        value = meter.mod(meter.mul(value, factor), modulus)
        value = meter.mod(meter.mul(value, inverse), modulus)
        coefficients.append(value)
        meter.record('coefficient', j=j, value=value, denominator=denominator, inverse=inverse)

    meter.phase = 'base_acquisition'
    for i, a in enumerate(points):
        r = horner(coefficients, a, modulus, meter)
        u = meter.exact(meter.sub(r, 1), n2, 'base r-1 / N^2')
        require(meter.le(0, u) and meter.lt(u, radix), 'base u range')
        b, v = meter.divmod(u, top_place)
        require(meter.le(0, b) and meter.lt(b, n), 'base top digit range')
        point = dict(i=i, a=a, r=r, u=u, b=b, v=v)
        state['base'].append(point)
        meter.record('base_point', **point)
    c0 = meter.exact(weighted_sum(weights, [p['r'] for p in state['base']], meter),
                     modulus, 'Delta^m r / M')
    c0_from_u = meter.exact(weighted_sum(weights, [p['u'] for p in state['base']], meter),
                            radix, 'Delta^m u / N^L')
    require(meter.eq(c0, c0_from_u), 'base quotient normalizations disagree')
    require(meter.lt(meter.absolute(c0), bound), 'base carry bound')
    state['c0'] = c0
    meter.record('base_quotient', c0=c0, c0_from_u=c0_from_u)

    meter.phase = 'threshold_generation'
    thresholds = state['thresholds']
    for point in state['base']:
        a, b, i = point['a'], point['b'], point['i']
        for k in range(1, a + 1):
            numerator = meter.sub(meter.mul(k, n), b)
            # Positive numerator; ceil numerator/a without any floating point.
            w = meter.div(meter.add(numerator, meter.sub(a, 1)), a)
            retained = meter.le(1, w) and meter.lt(w, n)
            threshold = dict(w=w, i=i, k=k, weight=weights[i])
            meter.record('threshold', retained=retained, **threshold)
            if retained:
                thresholds.append(threshold)
    meter.phase = 'threshold_sort'
    sorted_thresholds = sorted(thresholds, key=lambda x: SortThreshold(x, meter))
    state['sorted_thresholds'] = sorted_thresholds
    meter.record('sorted_thresholds', thresholds=sorted_thresholds)

    meter.phase = 'sweep'
    covered = 0
    proper_length = 0
    last_end = -1
    distinct = set()
    max_c_bits = 0
    category_lengths = dict(zero=0, unit=0, full_nonzero=0, proper=0)

    def interval(start, end, c):
        nonlocal covered, proper_length, last_end, max_c_bits
        require(meter.eq(start, meter.add(last_end, 1)), 'interval adjacency')
        require(meter.le(start, end), 'empty interval')
        require(meter.lt(meter.absolute(c), bound), 'carry bound during sweep')
        length = meter.add(meter.sub(end, start), 1)
        g, category = outcome(c, n, meter)
        item = dict(start=start, end=end, c=c, gcd=g, category=category, length=length)
        # Retain the mathematical interval before any later bookkeeping can stop.
        state['intervals'].append(item)
        meter.record('interval', **item)
        covered = meter.add(covered, length)
        category_lengths[category] = meter.add(category_lengths[category], length)
        if category == 'proper':
            proper_length = meter.add(proper_length, length)
            state['factors'].append(dict(factor=g, start=start, end=end, c=c,
                                         divisibility_verified=True, event=meter.count))
        distinct.add(c)
        width = meter.bits(meter.absolute(c))
        if meter.lt(max_c_bits, width):
            max_c_bits = width
        segments = state['maximal_segments']
        if segments and meter.eq(segments[-1]['c'], c):
            segments[-1]['end'] = end
            segments[-1]['length'] = meter.add(segments[-1]['length'], length)
        else:
            segments.append(item.copy())
        last_end = end

    c, start, index = c0, 0, 0
    while index < len(sorted_thresholds):  # list-cursor administration
        w = sorted_thresholds[index]['w']
        interval(start, meter.sub(w, 1), c)
        tie = []
        delta = 0
        while index < len(sorted_thresholds) and meter.eq(sorted_thresholds[index]['w'], w):
            event = sorted_thresholds[index]
            tie.append(event)
            delta = meter.add(delta, event['weight'])
            # Check each threshold is precisely the advertised one-step crossing.
            point = state['base'][event['i']]
            at = meter.div(meter.add(point['b'], meter.mul(point['a'], w)), n)
            before = meter.div(meter.add(point['b'], meter.mul(point['a'], meter.sub(w, 1))), n)
            require(meter.eq(at, event['k']), 'threshold at-value')
            require(meter.eq(before, meter.sub(event['k'], 1)), 'threshold before-value')
            index += 1
        old_c = c
        c = meter.sub(c, delta)
        item = dict(w=w, events=tie, total_weight=delta, old_c=old_c, new_c=c)
        state['ties'].append(item)
        meter.record('tie_update', **item)
        start = w
    interval(start, meter.sub(n, 1), c)
    require(meter.eq(covered, n), 'incomplete interval coverage')
    require(meter.eq(last_end, meter.sub(n, 1)), 'wrong final endpoint')
    divisor = meter.gcd(proper_length, n)
    probability = dict(numerator=meter.div(proper_length, divisor), denominator=meter.div(n, divisor))
    for segment in state['maximal_segments']:
        meter.record('maximal_segment', **segment)
    state.update(status='sweep_complete', coverage=covered, proper_length=proper_length,
                 category_lengths=category_lengths, distinct_c_count=len(distinct),
                 max_c_bits=max_c_bits, probability=probability,
                 sweep_completed_event=meter.count)
    meter.record('sweep_complete', coverage=covered, proper_length=proper_length,
                 category_lengths=category_lengths, distinct_c_count=len(distinct),
                 max_c_bits=max_c_bits, probability=probability,
                 interval_count=len(state['intervals']), segment_count=len(state['maximal_segments']))
    return state


def direct_control(n, state, control, meter):
    meter.phase = 'direct_control:' + control['label']
    control.update(status='running', start_event=meter.count, points=[])
    label = control['label']
    if label == '0': w = 0
    elif label == '1': w = 1
    elif label == 'N//2': w = meter.div(n, 2)
    elif label == 'N-1': w = meter.sub(n, 1)
    else: raise CheckFailure('unexpected frozen control label')
    control['w'] = w
    exponent = meter.sub(meter.mul(2, state['R']), 3)
    shift = meter.mul(meter.mul(12, meter.power(n, exponent)), w)
    values = []
    for point in state['base']:
        a = meter.add(point['a'], shift)
        r = horner(state['coefficients'], a, state['modulus'], meter)
        values.append(r)
        item = dict(i=point['i'], a_unwrapped=a, r=r)
        control['points'].append(item)
        meter.record('direct_control_point', label=label, w=w, **item)
    numerator = weighted_sum(state['weights'], values, meter)
    quotient = meter.exact(numerator, state['modulus'], 'direct lifted quotient')
    expected = None
    for segment in state['maximal_segments']:
        if meter.le(segment['start'], w) and meter.le(w, segment['end']):
            expected = segment['c']
            break
    require(expected is not None, 'no segment for control')
    require(meter.eq(quotient, expected), 'direct polynomial control disagrees')
    control.update(status='passed', numerator=numerator, quotient=quotient,
                   expected=expected, end_event=meter.count)
    meter.record('direct_control_complete', control=control)


def pair_multiply(left, right, delta, modulus, meter):
    a, b = left
    c, d = right
    real = meter.mod(meter.add(meter.mul(a, c), meter.mul(meter.mul(b, d), delta)), modulus)
    imag = meter.mod(meter.add(meter.mul(a, d), meter.mul(b, c)), modulus)
    return real, imag


def pair_power(z, delta, exponent, modulus, meter):
    result = (1, 0)
    base = (meter.mod(z, modulus), 1)
    while meter.lt(0, exponent):
        exponent, odd = meter.divmod(exponent, 2)
        if odd:
            result = pair_multiply(result, base, delta, modulus, meter)
        if meter.lt(0, exponent):
            base = pair_multiply(base, base, delta, modulus, meter)
    return result


def scalar_control(n, state, control, meter):
    """Original quadratic algebra and normalization, independently of coefficients."""
    meter.phase = 'original_scalar_control'
    control.update(status='running', w=0, points=[], start_event=meter.count)
    twoR = meter.mul(2, state['R'])
    big = meter.power(n, meter.add(twoR, 3))
    output = meter.power(n, meter.add(twoR, 1))
    place = meter.power(n, twoR)
    n2 = meter.mul(n, n)
    half = meter.exact(meter.sub(n, 1), 2, 'odd N normalization exponent')
    unit = meter.power(-4, half, output)
    digits = []
    for point in state['base']:
        a = point['a']
        require(meter.eq(meter.gcd(a, n), 1), 'scalar nonunit a')
        z = meter.mul(n, a)
        delta = meter.mod(meter.sub(meter.mul(z, z), 4), big)
        A, B = pair_power(z, delta, n, big, meter)
        quotient = meter.exact(A, n2, 'scalar A/N^2')
        normalization = meter.mod(meter.mul(a, unit), output)
        inverse = meter.inverse(normalization, output)
        value = meter.mod(meter.mul(quotient, inverse), output)
        digit = meter.div(value, place)
        require(meter.le(0, digit) and meter.lt(digit, n), 'scalar digit range')
        digits.append(digit)
        item = dict(i=point['i'], a=a, z=z, delta=delta, A=A, B=B,
                    quotient=quotient, normalization=normalization, inverse=inverse,
                    V=value, top_digit=digit)
        control['points'].append(item)
        meter.record('scalar_control_point', **item)
    # Direct difference table, not the candidate's binomial weights.
    differences = digits
    for order in range(state['m']):
        differences = [meter.sub(differences[i + 1], differences[i])
                       for i in range(len(differences) - 1)]
        meter.record('scalar_difference_level', order=order + 1, values=differences)
    filtered = meter.mod(differences[0], n)
    expected = meter.mod(meter.sub(0, state['c0']), n)
    require(meter.eq(filtered, expected), 'scalar filtered top digits disagree with -c0')
    control.update(status='passed', filtered_integer=differences[0], filtered_mod_N=filtered,
                   negative_c0_mod_N=expected, end_event=meter.count,
                   big_modulus=big, output_modulus=output, U=unit)
    meter.record('scalar_control_complete', control=control)


def main():
    config = json.loads((ROOT / 'config.json').read_text())
    start = float(os.environ['W032_ASSAY_MONOTONIC_START'])
    groups = []
    for index, b in enumerate(config['groups_b']):
        groups.append(dict(b=b, status='unstarted', candidate={'status': 'unstarted'},
            direct_controls=[dict(label=label, status='unstarted') for label in config['direct_controls']],
            scalar_control={'status': 'unstarted' if index == 0 else 'not_scheduled', 'label': 'first_N_w0'},
            diagnostic_verification={'status': 'unstarted'}))
    with (ROOT / 'events.jsonl').open('x') as events, (ROOT / 'records.jsonl').open('x') as records:
        meter = Meter(config, start, records, events)
        status = dict(status='running', groups=groups)
        for group in groups:
            meter.record('group_plan', planned=group)
        active = None
        try:
            for index, group in enumerate(groups):
                active = group
                meter.group = group['b']
                group.update(status='running', start_event=meter.count, start_elapsed_s=meter.elapsed())
                meter.phase = 'diagnostic_prime_generation'
                lower = meter.power(2, group['b'])
                p = prime_at_least(lower, meter, 'p')
                group['p'] = p
                gap = meter.power(2, meter.div(group['b'], 2))
                q_lower = meter.add(meter.add(p, gap), 1)
                q = prime_at_least(q_lower, meter, 'q')
                n = meter.mul(p, q)
                group.update(q=q, N=n)
                require(meter.le(lower, p) and meter.le(q_lower, q) and meter.lt(p, q), 'prime ordering')
                meter.record('diagnostic_primes', p=p, q=q, N=n, p_lower=lower, q_lower=q_lower)
                state = candidate(n, meter, group['candidate'])
                if state['status'] == 'inapplicable_nonunit_branch':
                    group['status'] = 'inapplicable_nonunit_branch'
                    for control in group['direct_controls']:
                        control.update(status='inapplicable_nonunit_branch')
                    if index == 0:
                        group['scalar_control'].update(status='inapplicable_nonunit_branch')
                else:
                    for control in group['direct_controls']:
                        direct_control(n, state, control, meter)
                    if index == 0:
                        scalar_control(n, state, group['scalar_control'], meter)
                    group['status'] = 'complete'
                meter.phase = 'diagnostic_verification'
                verification = group['diagnostic_verification']
                verification['status'] = 'running'
                for factor in state['factors']:
                    g = factor['factor']
                    require(meter.eq(meter.mod(n, g), 0), 'independent divisibility verification')
                    require(meter.eq(g, p) or meter.eq(g, q), 'gcd not one of diagnostic primes')
                    meter.record('factor_verification', **factor, hidden_factor_verified=True)
                for guard in state['guards']:
                    if guard['category'] == 'proper':
                        g = guard['gcd']
                        require(meter.eq(meter.mod(n, g), 0), 'guard factor verification')
                        require(meter.eq(g, p) or meter.eq(g, q), 'guard hidden-factor verification')
                numerator = meter.sub(meter.add(p, q), 2)
                denominator = meter.mul(p, q)
                divisor = meter.gcd(numerator, denominator)
                baseline = dict(numerator=meter.div(numerator, divisor), denominator=meter.div(denominator, divisor))
                verification.update(status='passed', ordinary_random_gcd_probability=baseline,
                                    raw_numerator=numerator, raw_denominator=denominator)
                group.update(end_event=meter.count, end_elapsed_s=meter.elapsed())
                meter.record('group_complete', result=group)
            status['status'] = 'complete'
        except StopBudget as exc:
            status.update(status='stopped_budget', reason=str(exc), stop_phase=meter.phase,
                          stop_group=meter.group)
        except Exception as exc:
            status.update(status='failed', reason=repr(exc), stop_phase=meter.phase,
                          stop_group=meter.group, traceback=traceback.format_exc())
        finally:
            if status['status'] != 'complete':
                reason = status.get('reason', 'unknown')
                for group in groups:
                    if group is active:
                        group.update(status=status['status'], reason=reason, end_event=meter.count,
                                     end_elapsed_s=meter.elapsed())
                    elif group['status'] == 'unstarted':
                        group['reason'] = reason
                    components = [group['candidate'], group['diagnostic_verification'],
                                  group['scalar_control'], *group['direct_controls']]
                    for component in components:
                        if component['status'] == 'running':
                            component.update(status=status['status'], reason=reason)
                        elif component['status'] == 'unstarted':
                            component['reason'] = reason
            status.update(arithmetic_events=meter.count, operations=dict(meter.ops),
                          phases=dict(meter.phases), maximum_operand_or_result_bits=meter.max_width,
                          elapsed_before_terminal_recording_s=meter.elapsed())
            for group in groups:
                meter.record('group_terminal', result=group)
            meter.record('run_terminal', status=status['status'], reason=status.get('reason'),
                         arithmetic_events=meter.count, operations=dict(meter.ops), phases=dict(meter.phases))
            status['record_counts'] = dict(meter.record_counts)
            with (ROOT / 'status.json').open('x') as out:
                json.dump(status, out, indent=2, sort_keys=True)
                out.write('\n')
        return 0 if status['status'] == 'complete' else 2


if __name__ == '__main__':
    raise SystemExit(main())
