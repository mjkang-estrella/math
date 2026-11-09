"""
Exact computation and periodicity certificate for z -> G(S(x,y,z)), trimmed spider legs x, y fixed.

Notation (trimmed legs): S(x,y,z) has a centre c and three legs of x, y, z markable edges, each
ending at a special (free) vertex.  Coupled states are (sigma, r, f): sigma = (centre label,
state of short leg 1, state of short leg 2); the long leg is attached with r >= 1 unmarked
edges and far-end condition f in {'F','T','A'}.

Values of detached runs (Theorem: run values):  run(k, near, far).
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(1000000)


def run(k, near, far):
    if k == 0:
        return 0
    if near == 'F' and far == 'F':
        return k & 1
    if near == 'F' or far == 'F':
        return k
    if near == far:
        return k & 1
    return 1 if (k >= 2 and k % 2 == 0) else 0


def flip(f):
    return {'F': 'F', 'T': 'A', 'A': 'T'}[f]


def mex(s):
    g = 0
    while g in s:
        g += 1
    return g


IN = {'N': 'I', 'I': 'I', 'O': 'F'}     # centre receives an incoming arrow
OUT = {'N': 'O', 'O': 'O', 'I': 'F'}    # centre gets an outgoing arrow
NEAR = {'I': 'A', 'O': 'T'}            # last centre edge must point Away (label I) / Toward (O)


@lru_cache(maxsize=None)
def two_leg(label, l1, l2):
    """Coupled value: centre label in {I,O}, exactly two attached legs l1,l2 (no long leg).
    Independent implementation (same recursion as spider.py)."""
    opts = set()
    legs = [l1, l2]
    for i in range(2):
        r, f = legs[i]
        other = legs[1 - i]
        for j in range(1, r + 1):
            for d in ('T', 'A'):
                if j == r and f != 'F' and d != f:
                    continue
                det = run(r - j, d, f)
                if j >= 2:
                    nl = tuple(sorted([(j - 1, d), other]))
                    val = two_leg(label, *nl)
                else:
                    newlab = IN[label] if d == 'T' else OUT[label]
                    if newlab == 'F':
                        val = run(other[0], 'F', other[1])
                    else:
                        val = run(other[0], NEAR[newlab], other[1])
                opts.add(det ^ val)
    return mex(opts)


def W(label, s1, s2):
    """Value of the coupled position after the long leg has detached:
    centre label (any), short legs s1, s2 (None = detached)."""
    att = [s for s in (s1, s2) if s is not None]
    if label == 'F':
        x = 0
        for (r, f) in att:
            x ^= run(r, 'F', f)
        return x
    if len(att) == 0:
        return 0
    if len(att) == 1:
        r, f = att[0]
        return run(r, NEAR[label], f)
    # two attached short legs; label must be I or O here
    assert label in ('I', 'O')
    return two_leg(label, *tuple(sorted(att)))


class Spider:
    def __init__(self, x, y):
        self.x, self.y = x, y
        self.V = {}          # (sigma, r, f) -> value
        self.acc = {}        # (sigma, d, parity) -> set of V(sigma, i, d) for i <= current-3
        self.vals_by = {}    # (sigma, d) -> dict value -> sorted list of i (for F-family lookups)

    def short_moves(self, sigma, r, f):
        """Yield option values from moves on short legs (long leg (r,f) stays put)."""
        label, s1, s2 = sigma
        out = []
        shorts = [s1, s2]
        for k in range(2):
            s = shorts[k]
            if s is None:
                continue
            rs, fs = s
            other = shorts[1 - k]
            for j in range(1, rs + 1):
                for d in ('T', 'A'):
                    if j == rs and fs != 'F' and d != fs:
                        continue
                    det = run(rs - j, d, fs)
                    if j >= 2:
                        ns = [None, None]
                        ns[k] = (j - 1, d)
                        ns[1 - k] = other
                        out.append(det ^ self.val((label, ns[0], ns[1]), r, f))
                    else:
                        newlab = IN[label] if d == 'T' else OUT[label]
                        if newlab == 'F':
                            v = run(r, 'F', f)
                            if other is not None:
                                v ^= run(other[0], 'F', other[1])
                            out.append(det ^ v)
                        else:
                            if other is None:
                                out.append(det ^ run(r, NEAR[newlab], f))
                            else:
                                ns = [None, None]
                                ns[1 - k] = other
                                out.append(det ^ self.val((newlab, ns[0], ns[1]), r, f))
        return out

    def val(self, sigma, r, f):
        key = (sigma, r, f)
        if key in self.V:
            return self.V[key]
        label, s1, s2 = sigma
        opts = set(self.short_moves(sigma, r, f))
        # long-leg move at j = 1 (edge at the centre)
        for d in ('T', 'A'):
            if r == 1 and f != 'F' and d != f:
                continue
            newlab = IN[label] if d == 'T' else OUT[label]
            opts.add(run(r - 1, d, f) ^ W(newlab, s1, s2))
        if f != 'F':
            # i = j-1 in [1, r-1]; detached run c(r-1-i, d, f)
            for i in range(max(1, r - 2), r):
                for d in ('T', 'A'):
                    if i == r - 1 and d != f:
                        continue
                    opts.add(self.V[(sigma, i, d)] ^ run(r - 1 - i, d, f))
            # i <= r-3 via accumulated sets
            for d in ('T', 'A'):
                for par in (0, 1):
                    S = self.acc.get((sigma, d, par), ())
                    if not S:
                        continue
                    # any i with this parity, i <= r-3: k = r-1-i >= 2
                    k_par = (r - 1 - par) % 2
                    bit = k_par if d == f else 1 - k_par
                    for v in S:
                        opts.add(v ^ bit)
            g = mex(opts)
        else:
            # options t XOR V(sigma, r-1-t, d), t in [0, r-2]
            g = 0
            while True:
                if g in opts:
                    g += 1
                    continue
                hit = False
                for d in ('T', 'A'):
                    vb = self.vals_by.get((sigma, d))
                    if not vb:
                        continue
                    for w, idxset in vb.items():
                        i = r - 1 - (g ^ w)
                        if 1 <= i <= r - 1 and i in idxset:
                            hit = True
                            break
                    if hit:
                        break
                if hit:
                    g += 1
                    continue
                break
        self.V[key] = g
        return g

    def sigmas(self):
        x, y = self.x, self.y

        def states(L):
            st = [(L, 'F')]
            for r in range(1, L):
                st += [(r, 'T'), (r, 'A')]
            return st
        out = []
        for a in states(x):
            for b in states(y):
                out.append(('N', a, b))
        for lab in ('I', 'O'):
            for a in states(x):
                out.append((lab, a, None))
            for b in states(y):
                out.append((lab, None, b))
        return out

    def compute(self, R):
        sig = self.sigmas()
        for r in range(1, R + 1):
            # make sure accumulated sets contain i <= r-3
            i = r - 3
            if i >= 1:
                for s in sig:
                    for d in ('T', 'A'):
                        self.acc.setdefault((s, d, i % 2), set()).add(self.V[(s, i, d)])
            for s in sig:
                for f in ('T', 'A', 'F'):
                    self.val(s, r, f)
            # register forced values at index r for F-family lookups
            for s in sig:
                for d in ('T', 'A'):
                    v = self.V[(s, r, d)]
                    self.vals_by.setdefault((s, d), {}).setdefault(v, set()).add(r)
        self.R = R
        self.sig = sig

    def G(self, z):
        return self.V[(('N', (self.x, 'F'), (self.y, 'F')), z, 'F')]
