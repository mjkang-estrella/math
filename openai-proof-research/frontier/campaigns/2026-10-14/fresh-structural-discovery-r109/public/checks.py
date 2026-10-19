#!/usr/bin/env python3
"""Small exact controls of the written interface; not the source FPRAS or a proof gate."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json


def median_law(base, r):
    assert r > 0 and r % 2 == 1 and sum(base.values()) == 1
    ans, cdf, previous = {}, F(0), F(0)
    for value, weight in sorted(base.items()):
        cdf += weight
        current = sum((F(comb(r, j)) * cdf**j * (1-cdf)**(r-j)
                       for j in range((r+1)//2, r+1)), F(0))
        ans[value] = current-previous
        previous = current
    assert sum(ans.values()) == 1 and all(x >= 0 for x in ans.values())
    return ans


def naive_median(base, r):
    ans = dict.fromkeys(base, F(0))
    for values in product(base, repeat=r):
        prob = F(1)
        for value in values:
            prob *= base[value]
        ans[sorted(values)[r//2]] += prob
    return ans


def tree_trial(codes, q, r):
    """Enumerate scalar macro histories with a deliberately fallible mock counter."""
    assert codes and all(len(x) == q for x in codes)
    U = 2**q
    def count(prefix):
        return sum(x.startswith(prefix) for x in codes)
    def estimates(prefix):
        n = count(prefix)
        assert n > 0
        if len(prefix) == q:
            return {F(1): F(1)}
        base = {}
        # Outputs 0 and 2U are bad calls and are clipped exactly as in the proof.
        for raw, prob in [(F(n), F(3,4)), (F(0), F(1,8)), (F(2*U), F(1,8))]:
            value = min(F(U), max(F(1), raw))
            base[value] = base.get(value, F(0)) + prob
        return median_law(base, r)
    masses = dict.fromkeys(codes, F(0))
    histories = 0
    def walk(prefix, probability, Q, Z):
        nonlocal histories
        if len(prefix) == q:
            masses[prefix] += probability * min(F(1), 1/(4*Z*Q))
            histories += 1
            return
        children = [prefix+x for x in '01' if count(prefix+x)]
        if len(children) == 1:
            walk(children[0], probability, Q, Z)
            return
        left, right = children
        for h0, p0 in estimates(left).items():
            for h1, p1 in estimates(right).items():
                for child, h in [(left,h0), (right,h1)]:
                    branch = h/(h0+h1)
                    walk(child, probability*p0*p1*branch, Q*branch, Z)
    for Z, pr in estimates('').items():
        walk('', pr, F(1), Z)
    success = sum(masses.values())
    assert 0 < success <= 1
    law = {x: mass/success for x, mass in masses.items()}
    assert sum(law.values()) == 1
    return law, success, histories


def controls():
    distributions = [
        {F(1,2):F(1,4), F(1):F(1,2), F(7):F(1,4)},
        {F(1):F(7,8), F(8):F(1,8)},
        {F(1):F(1)},
    ]
    median_cases = 0
    for base in distributions:
        for r in (1,3,5):
            assert median_law(base,r) == naive_median(base,r)
            median_cases += 1
    fixtures = [(1, {'0'}), (1, {'0','1'}), (2, {'00','01','11'}),
                (3, {'000','001','010','111'}), (3, {'001','101'})]
    trials, histories = 0, 0
    max_tv = F(0)
    for q, codes in fixtures:
        for r in (1,3,5):
            law, success, h = tree_trial(codes,q,r)
            u = F(1,len(codes))
            max_tv = max(max_tv, sum(abs(p-u) for p in law.values())/2)
            # Choose an exactly admissible rational correction weight for this
            # small mock law. This does not test the theorem's asymptotic D.
            retained = min(u/p for p in law.values())/2
            delta = 1-retained
            residual = {x:(u-retained*p)/delta for x,p in law.items()}
            assert all(v >= 0 for v in residual.values())
            assert sum(residual.values()) == 1
            assert all(retained*law[x]+delta*residual[x] == u for x in codes)
            trials += 1
            histories += h
    # Fixed good estimate tree: verify Q-correction exactly equalizes masses.
    codes = {'00','01','11'}
    eta = F(1,300)
    H = {'':3*(1+eta), '0':2*(1-eta), '1':1*(1+eta),
         '00':F(1), '01':F(1), '11':F(1)}
    proposals = {}
    for code in codes:
        prefix, Q = '', F(1)
        for bit in code:
            children = [prefix+b for b in '01' if any(x.startswith(prefix+b) for x in codes)]
            if len(children) == 2:
                Q *= H[prefix+bit]/sum(H[c] for c in children)
            prefix += bit
        proposals[code] = Q
    accepted = {x:p*min(F(1),1/(4*H['']*p)) for x,p in proposals.items()}
    assert len(set(accepted.values())) == 1
    # Mutation: omitting the Q factor fails exact uniformity on this good tree.
    assert len(set(proposals.values())) > 1
    # Every tiny capped 2-by-2 fiber: original prefixes equal translated fibers.
    fibers = prefix_cases = 0
    for caps in product(range(3), repeat=4):
        widths = [b.bit_length() for b in caps]
        groups = {}
        for table in product(*(range(b+1) for b in caps)):
            a,b,c,d = table
            margins = (a+b,c+d,a+c,b+d)
            code = ''.join(format(v, '0%db' % w) if w else ''
                           for v,w in zip(table,widths))
            groups.setdefault(margins, []).append((table,code))
        for margins, objects in groups.items():
            fibers += 1
            prefixes = {code[:i] for _,code in objects for i in range(len(code)+1)}
            for prefix in prefixes:
                intervals, offset = [], 0
                for bound,width in zip(caps,widths):
                    used = min(width,max(0,len(prefix)-offset))
                    known = int(prefix[offset:offset+used],2) if used else 0
                    low = known << (width-used)
                    high = min(bound,((known+1) << (width-used))-1)
                    intervals.append((low,high))
                    offset += width
                low = [a for a,b in intervals]
                residual = (margins[0]-low[0]-low[1],margins[1]-low[2]-low[3],
                            margins[2]-low[0]-low[2],margins[3]-low[1]-low[3])
                translated = 0
                for a,b,c,d in product(*(range(hi-lo+1) for lo,hi in intervals)):
                    translated += (a+b,c+d,a+c,b+d) == residual
                assert translated == sum(code.startswith(prefix) for _,code in objects)
                prefix_cases += 1
    return {
        'status':'EXACT_FINITE_CONTROLS_COMPLETED',
        'median_cdf_vs_tape_enumeration_cases':median_cases,
        'mock_tree_laws':trials,
        'macro_histories':histories,
        'largest_mock_tv':str(max_tv),
        'omitted_Q_mutation_detected':True,
        'tiny_capped_table_fibers':fibers,
        'translated_prefix_count_checks':prefix_cases,
        'scope':'Finite rational identities only. Not an implementation of source C, an asymptotic runtime test, an independent review, or a theorem/priority gate.'
    }


if __name__ == '__main__':
    print(json.dumps(controls(),indent=2,sort_keys=True))
