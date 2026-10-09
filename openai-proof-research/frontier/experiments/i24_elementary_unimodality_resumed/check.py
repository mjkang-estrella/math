"""New, bounded exact checks of the resumed bar argument (standard library).

Does not run, import, or rewrite the inherited graph/mutation enumerators.
Finite rational specializations test normalization; the report proves identities.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent


class Torus:
    def __init__(self, matrix, v, cutoff):
        self.B, self.v, self.cutoff = matrix, v, cutoff
        self.n = len(matrix)
        self.zero = (0,) * self.n
        self.roots = sorted((r for r in product(range(cutoff + 1), repeat=self.n)
                             if 0 < sum(r) <= cutoff), key=lambda r: (sum(r), r))

    def omega(self, a, b):
        return sum(a[i] * self.B[i][j] * b[j]
                   for i in range(self.n) for j in range(self.n))

    def mul(self, a, b):
        out = {}
        for r, x in a.items():
            for s, y in b.items():
                u = tuple(i + j for i, j in zip(r, s))
                if sum(u) <= self.cutoff:
                    out[u] = out.get(u, F(0)) + x*y*self.v**self.omega(r, s)
        return {r: x for r, x in out.items() if x}

    def inv(self, a):
        assert a.get(self.zero) == 1
        x = {r: -z for r, z in a.items() if r != self.zero}
        out = p = {self.zero: F(1)}
        out = dict(out)
        for _ in range(self.cutoff):
            p = self.mul(p, x)
            for r, z in p.items():
                out[r] = out.get(r, F(0)) + z
        return {r: z for r, z in out.items() if z}

    def log(self, a):
        x = {r: z for r, z in a.items() if r != self.zero}
        out, p = {}, {self.zero: F(1)}
        for k in range(1, self.cutoff + 1):
            p = self.mul(p, x)
            for r, z in p.items():
                out[r] = out.get(r, F(0)) + F((-1)**(k+1), k)*z
        return {r: z for r, z in out.items() if z}

    def factors(self, g, h):
        plus, middle, minus = ({self.zero: F(1)} for _ in range(3))
        for r in self.roots:
            remainder = g.get(r, F(0)) - self.mul(self.mul(plus, middle), minus).get(r, F(0))
            sign = sum(a*b for a, b in zip(h, r))
            target = plus if sign > 0 else minus if sign < 0 else middle
            if remainder:
                target[r] = remainder
        assert self.mul(self.mul(plus, middle), minus) == g
        return plus, middle, minus

    def incoming_group(self):
        g = {self.zero: F(1)}
        for r in self.roots:
            h = tuple(sum(self.B[i][j]*r[j] for j in range(self.n)) for i in range(self.n))
            middle = self.factors(g, h)[1]
            prior = self.log(middle).get(r, F(0))
            nonzero = [x for x in r if x]
            j = sum(r)
            prescribed = F((-1)**(j+1), j)/(self.v**j-self.v**(-j)) if len(nonzero) == 1 else F(0)
            if prescribed != prior:
                g[r] = prescribed-prior
        for r in self.roots:
            h = tuple(sum(self.B[i][j]*r[j] for j in range(self.n)) for i in range(self.n))
            j = sum(r)
            prescribed = F((-1)**(j+1), j)/(self.v**j-self.v**(-j)) if sum(x != 0 for x in r) == 1 else F(0)
            assert self.log(self.factors(g, h)[1]).get(r, F(0)) == prescribed
        return g

    def adjoint(self, g, m):
        inverse = self.inv(g)
        out = {}
        for a, x in g.items():
            for b, y in inverse.items():
                r = tuple(i+j for i, j in zip(a, b))
                if sum(r) <= self.cutoff:
                    power = self.omega(a, m)+self.omega(a, b)+self.omega(m, b)
                    out[r] = out.get(r, F(0)) + x*y*self.v**power
        return {r: z for r, z in out.items() if z}


def bar_checks():
    matrices = [((0, 1), (-1, 0)),
                ((0, -2, 0, 1, 0), (2, 0, -1, -1, 1), (0, 1, 0, -1, -1),
                 (-1, 1, 1, 0, -1), (0, -1, 1, 1, 0))]
    checks = []
    for B in matrices:
        for value in (F(2), F(5, 3)):
            t, tb = Torus(B, value, 3), Torus(B, 1/value, 3)
            g, gb = t.incoming_group(), tb.incoming_group()
            assert gb == t.inv(g)
            covectors = [(1,)*len(B), (-1,)*len(B), tuple(i-2 for i in range(len(B)))]
            comparisons = 0
            for h in covectors:
                fs, fbs = t.factors(g, h), tb.factors(gb, h)
                for f, fb in zip(fs, fbs):
                    assert fb == t.inv(f)
                    for m in (tuple(range(len(B))), tuple(1-i for i in range(len(B)))):
                        for inverse in (False, True):
                            a = t.inv(f) if inverse else f
                            ab = tb.inv(fb) if inverse else fb
                            assert t.adjoint(a, m) == tb.adjoint(ab, m)
                            comparisons += len(t.roots)+1
            checks.append({'rank': len(B), 'v': str(value), 'cutoff': 3,
                           'nonzero_root_slots': len(t.roots), 'adjoint_coefficient_comparisons': comparisons})
    return checks


def unit_checks():
    # Independent use of D's rational coefficients and formal inversion,
    # compared to the finite centered elementary-alphabet formula.
    count = 0
    for v in (F(2), F(5, 3)):
        d = [F(1)]
        for j in range(1, 6):
            denominator = F(1)
            for i in range(1, j+1):
                denominator *= 1-v**(-2*i)
            d.append(v**(-j*j)/denominator)
        inv = [F(1)]
        for j in range(1, 6):
            inv.append(-sum(d[k]*inv[j-k] for k in range(1, j+1)))
        for t in range(-4, 5):
            a = abs(t)
            expected = [F(1)]
            for w in range(1-a, a, 2):
                old = expected
                expected = [F(0)]*(len(old)+1)
                for j, c in enumerate(old):
                    expected[j] += c
                    expected[j+1] += c*v**w
            left, right = (d, inv) if t >= 0 else (inv, d)
            for j in range(6):
                actual = sum(left[k]*right[j-k]*v**(t*(2*k-j)) for k in range(j+1))
                assert actual == (expected[j] if j < len(expected) else 0)
                count += 1
    # Entire positive pairing-one crossing of the algebraically allowed wall.
    # Both units use the same ray, so there is no extra inter-ray skew factor.
    bad = {0: {0: 1}, 1: {-2: 1, 2: 1}, 2: {0: 1}}
    assert bad[1].get(0, 0)-bad[1].get(2, 0) == -1
    # A positive rational, bar-invariant SERIES need not be Laurent polynomial.
    for v in (F(2), F(5, 3)):
        assert v*v/(v*v-1)**2 == (1/v)**2/((1/v)**2-1)**2
    return {'normalized_unit_coefficient_comparisons': count,
            'allowed_wall_jump_polynomials': bad,
            'allowed_wall_occurrence_in_source_chart': 'NOT ESTABLISHED',
            'positive_bar_invariant_infinite_series': 'v^2/(v^2-1)^2 = sum_{j>=1} j*v^(-2j)'}


def main():
    results = {'scope': 'new finite exact normalization checks, not a general proof or source witness implementation',
               'bar': bar_checks(), 'units': unit_checks()}
    encoded = json.dumps(results, indent=2, sort_keys=True)+'\n'
    import sys
    if '--check' in sys.argv:
        assert (OUT/'results.json').read_text() == encoded
    else:
        (OUT/'results.json').write_text(encoded)
    print(encoded)


if __name__ == '__main__':
    main()
