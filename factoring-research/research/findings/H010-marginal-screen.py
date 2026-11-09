#!/usr/bin/env python3
"""H010: exact Boolean validation and one preregistered graph-only screen.

No factor/order input to candidate(). No numerical amplitude evaluation.
Only Python standard library. All outputs are H010-marginal-* owned files.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import time

ROOT = Path(__file__).resolve().parent
ZERO, ONE = -1, -2


def literal(bit):
    return ONE if bit else ZERO


class Circuit:
    def __init__(self):
        self.nodes = []  # None = input; otherwise (sorted input ids, truth table)
        self.inputs = []
        self.cache = {}

    def inp(self):
        v = len(self.nodes)
        self.nodes.append(None)
        self.inputs.append(v)
        return v

    def gate(self, args, fn):
        scope = sorted(set(v for v in args if v >= 0))
        table = []
        for row in range(1 << len(scope)):
            values = {v: (row >> i) & 1 for i, v in enumerate(scope)}
            values.update({ZERO: 0, ONE: 1})
            table.append(int(fn(*(values[v] for v in args))))
        # Exact local truth-table simplification, including repeated arguments.
        for j in range(len(scope) - 1, -1, -1):
            if all(table[r] == table[r | (1 << j)]
                   for r in range(len(table)) if not r & (1 << j)):
                table = [table[r] for r in range(len(table)) if not r & (1 << j)]
                del scope[j]
        if not scope:
            return literal(table[0])
        if len(scope) == 1 and table == [0, 1]:
            return scope[0]
        key = (tuple(scope), tuple(table))
        if key in self.cache:
            return self.cache[key]
        out = len(self.nodes)
        self.nodes.append(key)
        self.cache[key] = out
        return out

    def evaluate(self, values):
        assert len(values) == len(self.inputs)
        result = {ZERO: 0, ONE: 1}
        result.update(zip(self.inputs, values))
        for out, gate in enumerate(self.nodes):
            if gate is not None:
                scope, table = gate
                row = sum(result[v] << i for i, v in enumerate(scope))
                result[out] = table[row]
        return result

    def factors(self, outputs):
        # Remove only unused deterministic outputs, in reverse topological order.
        # Each such output sums to exactly one for every assignment to its parents.
        live = set(v for v in outputs if v >= 0)
        for out in range(len(self.nodes) - 1, -1, -1):
            if out in live and self.nodes[out] is not None:
                live.update(self.nodes[out][0])
        factors = []
        for out, gate in enumerate(self.nodes):
            if out not in live or gate is None:
                continue
            scope, table = gate
            scope = scope + (out,)  # out has largest creation index
            relation = tuple(int(((r >> (len(scope)-1)) & 1) ==
                                 table[r & ((1 << (len(scope)-1))-1)])
                             for r in range(1 << len(scope)))
            factors.append((scope, relation))
        return live | set(self.inputs), factors


def word(value, width):
    return [literal((value >> i) & 1) for i in range(width)]


def readword(wires, values):
    return sum(values[v] << i for i, v in enumerate(wires))


def add(C, left, right, carry=ZERO):
    assert len(left) == len(right)
    out = []
    for u, v in zip(left, right):
        s = C.gate((u, v, carry), lambda a, b, c: a ^ b ^ c)
        carry = C.gate((u, v, carry), lambda a, b, c: (a+b+c) >= 2)
        out.append(s)
    return out, carry


def mux(C, control, yes, no):
    return C.gate((control, yes, no), lambda h, d, s: d if h else s)


def addmod(C, current, bit, constant, N):
    n = N.bit_length()
    assert len(current) == n and 0 <= constant < N
    # Both summands < N; the n+1-bit sum is < 2N.
    controlled = [bit if ((constant >> i) & 1) else ZERO for i in range(n)]
    total, _ = add(C, current + [ZERO], controlled + [ZERO])
    # total + (2^(n+1)-1-N) + 1; final carry iff total >= N.
    diff, ge = add(C, total, word(((1 << (n+1))-1) ^ N, n+1), ONE)
    return [mux(C, ge, diff[i], total[i]) for i in range(n)]


def multiply(C, source, constant, N):
    n = N.bit_length()
    result = word(0, n)
    d = constant
    for bit in source:  # least significant source bit first
        result = addmod(C, result, bit, d, N)
        d = (2*d) % N
    return result


def exponentiate(C, inputs, powers, N):
    result = word(1, N.bit_length())
    for j in range(len(inputs)-1, -1, -1):  # high exponent bit first
        product = multiply(C, result, powers[j], N)
        result = [mux(C, inputs[j], product[i], result[i])
                  for i in range(N.bit_length())]
    return result


def equality(left, right):
    scope = tuple(sorted(set(v for v in (left, right) if v >= 0)))
    table = []
    for r in range(1 << len(scope)):
        vals = {v: (r >> i) & 1 for i, v in enumerate(scope)}
        vals.update({ZERO: 0, ONE: 1})
        table.append(int(vals[left] == vals[right]))
    return scope, tuple(table)


def simplify(variables, factors):
    """Pin unary supports; identify equality wires; deduplicate 0/1 factors.

    Fixed point, factors in lexicographic order. No disequality substitution,
    global semantic reasoning, inferred order, or contraction/re-factorization.
    """
    parent = {v: v for v in variables}
    pinned = {}

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    while True:
        changed = False
        new = set()
        for scope, table in sorted(factors):
            roots = [root(v) for v in scope]
            free = sorted(set(v for v in roots if v not in pinned))
            reduced = []
            for r in range(1 << len(free)):
                vals = {v: (r >> i) & 1 for i, v in enumerate(free)}
                vals.update(pinned)
                reduced.append(table[sum(vals[v] << i for i, v in enumerate(roots))])
            for j in range(len(free)-1, -1, -1):
                if all(reduced[r] == reduced[r | (1 << j)]
                       for r in range(len(reduced)) if not r & (1 << j)):
                    reduced = [reduced[r] for r in range(len(reduced))
                               if not r & (1 << j)]
                    del free[j]
            if not free:
                assert reduced == [1], 'zero scalar outside candidate promise'
                continue
            if len(free) == 1 and sum(reduced) == 1:
                pinned[free[0]] = reduced.index(1)
                changed = True
            elif len(free) == 2 and reduced == [1, 0, 0, 1]:
                parent[free[1]] = free[0]  # lowest creation index survives
                changed = True
            else:
                new.add((tuple(free), tuple(reduced)))
        factors = new
        if not changed:
            break
    remaining = {root(v) for v in variables} - set(pinned)
    return remaining, sorted(factors)


def candidate(N, a, k):
    """Inputs exactly N, unit base a, and public prefix length k."""
    assert N >= 3 and N % 2 and 0 < a < N and math.gcd(N, a) == 1
    m = (N*N-1).bit_length()
    assert 0 <= k <= m
    powers = [a]
    for _ in range(1, m):
        powers.append((powers[-1]*powers[-1]) % N)
    # Cancel the common unmeasured low-bit suffix (permutation identity).
    C = Circuit()
    ket = [C.inp() for _ in range(k)]
    out = exponentiate(C, ket, powers[m-k:], N)
    bra = [C.inp() for _ in range(k)]
    out2 = exponentiate(C, bra, powers[m-k:], N)
    variables, factors = C.factors(out + out2)
    factors += [equality(u, v) for u, v in zip(out, out2)]
    variables, factors = simplify(variables, factors)
    return C, variables, factors, (ket, bra, out, out2)


def minfill(variables, factors, cap, deadline):
    adj = {v: set() for v in variables}
    for scope, table in factors:
        for v in scope:
            adj[v].update(set(scope) - {v})
    w = max((len(scope) for scope, table in factors), default=0)
    order, events = [], {'candidate_scores': 0, 'pair_checks': 0}
    while adj:
        if time.monotonic() >= deadline:
            return dict(status='planning_timeout', width_lower_bound=w,
                        remaining=len(adj), eliminated=len(order), events=events)
        best, best_score = None, None
        # ascending IDs lets the first zero-fill vertex terminate a scan exactly.
        for v in sorted(adj):
            neighbors = sorted(adj[v])
            score = 0
            events['candidate_scores'] += 1
            for i, u in enumerate(neighbors):
                for z in neighbors[i+1:]:
                    events['pair_checks'] += 1
                    score += z not in adj[u]
            if best_score is None or score < best_score:
                best, best_score = v, score
            if score == 0:
                break
        neighbors = sorted(adj[best])
        # Dense bucket product is explicitly materialized, including eliminated v.
        # Output factor has len(neighbors) bits; bucket width has one more.
        w = max(w, len(neighbors)+1)
        order.append(best)
        if w > cap:
            payload = json.dumps(order, separators=(',', ':')).encode()
            return dict(status='width_rejected', width_lower_bound=w,
                        witness_vertex=best, witness_neighbors=neighbors,
                        witness_fill=best_score, eliminated=len(order)-1,
                        remaining=len(adj), order_prefix=order,
                        order_sha256=hashlib.sha256(payload).hexdigest(), events=events)
        for u in neighbors:
            adj[u].update(set(neighbors)-{u})
            adj[u].remove(best)
        del adj[best]
    return dict(status='complete', width=w, order=order, events=events)


def validate():
    counts = Counter()
    # Truth-table gate relations have exactly one output per input row by build.
    for N in range(3, 16, 2):
        n = N.bit_length()
        for d in range(N):
            C = Circuit()
            x = [C.inp() for _ in range(n)]
            b = C.inp()
            result = addmod(C, x, b, d, N)
            for u in range(N):
                for bit in (0, 1):
                    vals = C.evaluate([(u >> i)&1 for i in range(n)] + [bit])
                    assert readword(result, vals) == (u+bit*d) % N
                    counts['addmod_assignments'] += 1
            C = Circuit()
            x = [C.inp() for _ in range(n)]
            result = multiply(C, x, d, N)
            for u in range(1 << n):
                vals = C.evaluate([(u >> i)&1 for i in range(n)])
                assert readword(result, vals) == u*d % N
                counts['multiply_assignments'] += 1
        for a in range(1, N):
            if math.gcd(a, N) != 1:
                continue
            m = (N*N-1).bit_length()
            powers = [pow(a, 1 << j, N) for j in range(m)]
            C = Circuit()
            x = [C.inp() for _ in range(m)]
            result = exponentiate(C, x, powers, N)
            for u in range(1 << m):
                vals = C.evaluate([(u >> i)&1 for i in range(m)])
                assert readword(result, vals) == pow(a, u, N)
                counts['exponent_assignments'] += 1
            # Exhaust the local paired permutation identity, including b=0.
            for d in powers:
                for bit in (0, 1):
                    mult = d if bit else 1
                    for u in range(N):
                        for v in range(N):
                            assert (u*mult % N == v*mult % N) == (u == v)
                            counts['paired_cancellations'] += 1
            # Exact all-zero prefix counts before/after suffix cancellation.
            full = [pow(a, u, N) for u in range(1 << m)]
            for k in range(m+1):
                t = m-k
                original = 0
                for low in range(1 << t):
                    freq = Counter(full[(u << t) + low] for u in range(1 << k))
                    original += sum(v*v for v in freq.values())
                reduced = Counter(pow(a, u << t, N) for u in range(1 << k))
                collisions = sum(v*v for v in reduced.values())
                assert Fraction(original, (1 << m)*(1 << k)) == Fraction(collisions, 1 << (2*k))
                counts['prefix_cancellation_cases'] += 1
    # Exhaust sum-preservation of normalization on every collection of up to two
    # distinct nonzero Boolean relations on scopes of size <=2 over 3 variables.
    all_factors = []
    for size in (1, 2):
        for scope in itertools.combinations(range(3), size):
            for mask in range(1, 1 << (1 << size)):
                all_factors.append((scope, tuple((mask >> r)&1 for r in range(1 << size))))
    def partition(variables, factors):
        vs = sorted(variables)
        total = 0
        for r in range(1 << len(vs)):
            values = {v: (r >> i)&1 for i, v in enumerate(vs)}
            total += math.prod(tab[sum(values[v] << i for i, v in enumerate(sc))]
                               for sc, tab in factors)
        return total
    for i, f in enumerate(all_factors):
        for g in all_factors[i:]:
            z = partition(set(range(3)), [f, g])
            if z == 0:
                continue
            vs, fs = simplify(set(range(3)), [f, g])
            assert partition(vs, fs) == z
            counts['normalization_cases'] += 1
    # Complete network partition by exhaustive free-variable assignments when
    # <=18 remain; no amplitudes, only exact Boolean counting.
    for N in (3, 5, 7):
        for a in range(1, N):
            if math.gcd(a, N) != 1:
                continue
            m = (N*N-1).bit_length()
            for k in range(min(m, 3)+1):
                C, vs, fs, _ = candidate(N, a, k)
                if len(vs) > 18:
                    counts['network_partition_omitted_gt18'] += 1
                    continue
                freq = Counter(pow(a, u << (m-k), N) for u in range(1 << k))
                assert partition(vs, fs) == sum(v*v for v in freq.values())
                counts['network_partition_cases'] += 1
    return dict(status='passed', counts=dict(counts))


def isprime(v):
    return v >= 2 and all(v % d for d in range(2, math.isqrt(v)+1))


def corpus():
    rng = random.Random(1002)
    result = []
    for n in (8, 12, 16, 20):
        h = n//2
        primes = [v for v in range(1 << (h-2), 1 << (h+1)) if isprime(v)]
        moduli = set()
        for ni in range(3):
            while True:
                p, q = rng.sample(primes, 2)
                N = p*q
                if (N.bit_length() == n and N not in moduli
                        and max(p, q) <= 4*min(p, q)):
                    break
            moduli.add(N)
            bases = set()
            for ai in range(2):
                while True:
                    a = rng.randrange(2, N)
                    if math.gcd(a, N) == 1 and a not in bases:
                        break
                bases.add(a)
                m = (N*N-1).bit_length()
                for k in range(m+1):
                    result.append(dict(id=f'n{n:02d}-N{ni}-a{ai}-k{k:02d}',
                                       n=n, N=N, a=a, k=k, m=m,
                                       cap=2*(n-1).bit_length()+4))
    return result


def screen():
    start = time.monotonic()
    deadline = start+55
    cases = corpus()
    header = dict(seed=1002, external_cap_seconds=60, internal_cap_seconds=55,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  protocol_sha256=hashlib.sha256((ROOT/'H010-marginal-prereg.md').read_bytes()).hexdigest(),
                  cases=[dict(c, status='unstarted') for c in cases])
    (ROOT/'H010-marginal-manifest.json').write_text(json.dumps(header, indent=2)+'\n')
    journal = ROOT/'H010-marginal-outcomes.jsonl'
    assert not journal.exists(), 'never overwrite frozen outcomes'
    with journal.open('x') as fh:
        for case in cases:
            if time.monotonic() >= deadline:
                break
            fh.write(json.dumps(dict(id=case['id'], event='started'))+'\n'); fh.flush()
            before = time.monotonic()
            C, vs, fs, _ = candidate(case['N'], case['a'], case['k'])
            build = time.monotonic()-before
            result = minfill(vs, fs, case['cap'], deadline)
            result.update(id=case['id'], event='finished', build_seconds=build,
                          case_seconds=time.monotonic()-before, nodes_created=len(C.nodes),
                          remaining_variables=len(vs), factors=len(fs))
            fh.write(json.dumps(result, sort_keys=True)+'\n'); fh.flush()
            if result['status'] != 'complete':
                break  # first rejection or censor stops this one frozen wave
        fh.write(json.dumps(dict(event='run_end', elapsed_seconds=time.monotonic()-start))+'\n')
        fh.flush()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('validate', 'screen'))
    args = parser.parse_args()
    if args.mode == 'validate':
        start = time.monotonic()
        result = validate()
        result['elapsed_seconds'] = time.monotonic()-start
        result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        print(json.dumps(result, indent=2))
    else:
        screen()
