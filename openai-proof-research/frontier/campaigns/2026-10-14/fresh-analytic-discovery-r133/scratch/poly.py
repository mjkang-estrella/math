# MIT License. Author: Myeongjin Kang. Minimal exact multivariate polynomial arithmetic (integer/Fraction coeffs).
from fractions import Fraction as Fr

class P:
    __slots__ = ("t", "nv")
    def __init__(self, t, nv):
        self.t = {k: v for k, v in t.items() if v != 0}; self.nv = nv
    @staticmethod
    def var(i, nv):
        e = [0] * nv; e[i] = 1; return P({tuple(e): 1}, nv)
    @staticmethod
    def const(c, nv):
        return P({(0,) * nv: c}, nv)
    def _c(self, o):
        return o if isinstance(o, P) else P.const(o, self.nv)
    def __add__(self, o):
        o = self._c(o); r = dict(self.t)
        for k, v in o.t.items(): r[k] = r.get(k, 0) + v
        return P(r, self.nv)
    __radd__ = __add__
    def __neg__(self): return P({k: -v for k, v in self.t.items()}, self.nv)
    def __sub__(self, o): return self + (-self._c(o))
    def __rsub__(self, o): return self._c(o) - self
    def __mul__(self, o):
        o = self._c(o); r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2)); r[k] = r.get(k, 0) + v1 * v2
        return P(r, self.nv)
    __rmul__ = __mul__
    def __pow__(self, e):
        r = P.const(1, self.nv)
        for _ in range(e): r = r * self
        return r
    def divexact(self, d):
        """exact division by polynomial d (must divide); lex-leading-term long division."""
        q = P({}, self.nv); r = P(dict(self.t), self.nv)
        lt_d = max(d.t); cd = d.t[lt_d]
        while r.t:
            lt = max(r.t); c = Fr(r.t[lt]) / cd
            if any(a < b for a, b in zip(lt, lt_d)): raise ValueError("not divisible")
            m = P({tuple(a - b for a, b in zip(lt, lt_d)): c}, self.nv)
            q = q + m; r = r - m * d
        q.t = {k: (int(v) if Fr(v).denominator == 1 else v) for k, v in q.t.items()}
        return q
    def subs(self, i, poly):
        r = P({}, self.nv)
        for k, v in self.t.items():
            e = list(k); a = e[i]; e[i] = 0
            r = r + P({tuple(e): v}, self.nv) * (poly ** a)
        return r
    def mincoef(self):
        return min(self.t.values()) if self.t else 0
    def neg_terms(self):
        return {k: v for k, v in self.t.items() if v < 0}
    def __call__(self, *x):
        s = 0
        for k, v in self.t.items():
            m = v
            for xi, a in zip(x, k): m *= xi ** a
            s += m
        return s
