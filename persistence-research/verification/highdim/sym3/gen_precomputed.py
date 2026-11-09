"""Search-only arithmetic caches; certificate semantics/checker are unchanged.

Singleton coefficient groups retain their own coordinate. Repeated groups use
the inherited multiset refinement. No quotient exchanges distinct coefficients.
"""
import sys
sys.dont_write_bytecode = True
import math
from gen_sym import Generator


class PrecomputedGenerator(Generator):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.forbidden_cache = {}
        self.decimal_orbits = {}
        self.sumset_precompute_stats = {'orbits': 0, 'forbidden_hits': 0}

    def forbidden(self, T, e, a, w):
        if not self.pin_digits:
            return super().forbidden(T, e, a, w)
        # With decimal pinning, free lower bounds do not change the coset image.
        key = (T, e[0], a[1], w[1])
        if key in self.forbidden_cache:
            self.sumset_precompute_stats['forbidden_hits'] += 1
            return self.forbidden_cache[key]
        result = super().forbidden(T, e, a, w)
        if len(self.forbidden_cache) > 200000:
            self.forbidden_cache.clear()
        self.forbidden_cache[key] = result
        return result

    def contribution(self, p, d, g, c, residue):
        key = (p, g, c, residue)
        if key not in self.sumcache:
            orbitkey = (p, g)
            if orbitkey not in self.decimal_orbits:
                # Exponents range over residue + g*j modulo ord_p(10).
                step = pow(10, g, p)
                orbit = [1]
                for _ in range(1, d // g):
                    orbit.append(orbit[-1] * step % p)
                self.decimal_orbits[orbitkey] = tuple(orbit)
                self.sumset_precompute_stats['orbits'] += 1
            base = c * pow(10, residue, p) % p
            self.sumcache[key] = {base * v % p for v in self.decimal_orbits[orbitkey]}
        return self.sumcache[key]

    def sumkill(self, r, M, a, w):
        if not self.sumsets:
            return None
        candidates = []
        for d, ee in self.byperiod.items():
            f = d // math.gcd(M, d)
            if 1 < f <= 7:
                candidates.extend(e for e in ee if ((e[0] - 1) // e[4] > 1 or self.pin2 or self.pin_digits) and e[0] <= 10**12)
        def strength(e):
            if self.pin_digits:
                # This call also initializes the parent coset cache.
                self.forbidden(1, e, a, w)
                h, images, _ = self.cosets[(e[0], a[1], w[1])]
                return ((e[0] - 1) // (h * max(1, len(images))), -e[1])
            return ((e[0] - 1) // e[4], -e[1])
        candidates.sort(key=strength, reverse=True)
        for e in candidates[:16]:
            self.check_budget()
            p, d, _, _, _ = e
            if self.pin_digits and not self.cosets[(p, a[1], w[1])][1]:
                self.kills['empty_decimal_target'] += 1
                return e
            g = math.gcd(M, d)
            vals = {self.K % p}
            for c, q in zip((1,) + self.coefs, r):
                term = self.contribution(p, d, g, c, q % g)
                if len(vals) * len(term) > 20000:
                    break
                vals = {(u + v) % p for u in vals for v in term}
            else:
                if all(self.forbidden(t, e, a, w) for t in vals):
                    self.kills['sumset'] += 1
                    return e
        return None
