#!/usr/bin/env python3
"""Fixed exact algebra only. No candidate runs, searches, sweeps or optimizer.

Sparse polynomial identities are checked over Z. Two preselected arithmetic
examples exercise signs and m=1; one preselected obstruction illustrates the
symbolic proof. This is not a factoring routine or formal proof assistant.
"""

from collections import defaultdict
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json


class Poly:
    """Integer polynomials; monomials are sorted tuples of variable names."""

    def __init__(self, terms):
        self.terms = {mon: val for mon, val in terms.items() if val}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly({(): value})

    def __add__(self, other):
        result = defaultdict(int, self.terms)
        for mon, val in self.coerce(other).terms.items():
            result[mon] += val
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({mon: -val for mon, val in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        result = defaultdict(int)
        for mon1, val1 in self.terms.items():
            for mon2, val2 in self.coerce(other).terms.items():
                result[tuple(sorted(mon1 + mon2))] += val1 * val2
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        value = Poly.coerce(1)
        for _ in range(exponent):
            value = value * self
        return value


def variables(names):
    return [Poly({(name,): 1}) for name in names.split()]


checks = []


def identity(name, lhs, rhs):
    assert not (Poly.coerce(lhs) - rhs).terms, name
    checks.append(name)


# Universal polynomial identities; no specialization/parameter enumeration.
u, v, j, m, k, N, t = variables("u v j m k N t")
f = lambda X: u * X**2 + v * X + N * t
identity("Taylor value and derivative lift", f(j + m*k),
         f(j) + m*k*(2*u*j + v) + u*m**2*k**2)

u1, t1, u2, t2, v1, v2, i1, i2 = variables(
    "u1 t1 u2 t2 v1 v2 i1 i2")
D = u1*t2 - u2*t1
mP = m**2*(t2*i1 - t1*i2) - t2*v1 + t1*v2
mQ = m**2*(-u2*i1 + u1*i2) + u2*v1 - u1*v2
identity("Inverse row 1 before setting determinant D=m",
         u1*mP + t1*mQ, D*(m**2*i1-v1))
identity("Inverse row 2 before setting determinant D=m",
         u2*mP + t2*mQ, D*(m**2*i2-v2))
identity("Image matrix determinant", (m*t2)*(m*u1)-(-m*t1)*(-m*u2),
         m**2*D)

J, q0, r, s, c0 = variables("J q0 r s c0")
identity("Lifted product congruence", (J+m*r)*(q0+m*s),
         J*q0+m*(q0*r+J*s)+m**2*r*s)
identity("Explicit image-lattice determinant", m*m**2 - 0*(m*c0), m**3)

a, b, X, s, h, delta, y = variables("a b X s h delta y")
R = a*X**2 - s*X + b*N
identity("Strict exclusion completed square", 4*a*R,
         (2*a*X-s)**2-(s**2-4*a*b*N))
identity("Midpoint gap polynomial", N*X**2-(2*N*h+delta)*X+h**2*N,
         N*(X-h)**2-delta*X)
identity("Tangent comparison with denominators cleared",
         X*(N*X+h**2*y-2*N*h), N*(X-h)**2+h**2*(X*y-N))

family_N = h*(2*h-1)-1
family_k = 2*h-1
identity("Obstruction composite factorization", family_N, (h-1)*(2*h+1))
identity("Obstruction surplus one", h*family_k-family_N, 1)
identity("Obstruction delta=h", family_N*h+h**2*family_k-2*family_N*h, h)
identity("Obstruction interval inside factor range",
         family_N-(h+1)**2, h**2-3*h-2)
identity("Obstruction lower-neighbor positivity",
         family_N-h*(h-1), h**2-1)
identity("Obstruction upper-neighbor positivity",
         family_N-h*(h+1), h**2-2*h-1)
d, z = variables("d z")
surplus, = variables("surplus")
identity("Sharp unsuccessful-query delta>=h decomposition",
         N*d**2+h**2*surplus-h*(h+d),
         (N-h**2)*d**2+h**2*(surplus-1)+h*d*(h*d-1))
identity("Discrete tangent separation on right",
         (h+1)*d**2-(h+d), (d-1)*((h+1)*d+h))
# Nonnegative-coefficient certificates for h=6+z, z>=0.
identity("Interval positivity for h>=6",
         (6+z)**2-3*(6+z)-2, z**2+9*z+16)
identity("Upper-neighbor positivity for h>=6",
         (6+z)**2-2*(6+z)-1, z**2+10*z+23)
identity("Lower-neighbor positivity for h>=6",
         (6+z)**2-1, z**2+12*z+35)

# Reachable initial-query family; still symbolic, with no parameter run.
initial_N = h*(4*h-3)-1
identity("Initial-query family composite factorization", initial_N, (h-1)*(4*h+1))
identity("Initial-query family isqrt lower bracket", initial_N-(2*h-1)**2, h-2)
identity("Initial-query family isqrt upper bracket", (2*h)**2-initial_N, 3*h+1)
identity("Initial-query family discrete separation", initial_N-h*(h+1),
         3*h**2-4*h-1)
identity("Initial-query family separation positivity for h>=6",
         3*(6+z)**2-4*(6+z)-1, 3*z**2+32*z+83)


def fixed_lattice_case(name, n, mod, residue, basis, vs, factor_pair):
    (u1, t1), (u2, t2) = basis
    v1, v2 = vs
    p, q = factor_pair
    assert gcd(n, mod) == gcd(residue, mod) == 1
    assert u1*t2-u2*t1 == mod
    for u, t, v in [(u1, t1, v1), (u2, t2, v2)]:
        assert (u*residue**2-n*t) % mod == 0
        assert (u*residue**2+v*residue+n*t) % (mod**2) == 0
        assert (v+2*u*residue) % mod == 0
    assert p*q == n and (p-residue) % mod == 0
    assert (u1*p+v1+t1*q) % (mod**2) == 0
    assert (u2*p+v2+t2*q) % (mod**2) == 0
    i1 = (u1*p+v1+t1*q) // (mod**2)
    i2 = (u2*p+v2+t2*q) // (mod**2)
    assert (t2*v1-t1*v2) % mod == 0
    assert (u2*v1-u1*v2) % mod == 0
    recovered = (
        mod*(t2*i1-t1*i2)-(t2*v1-t1*v2)//mod,
        mod*(-u2*i1+u1*i2)+(u2*v1-u1*v2)//mod,
    )
    assert recovered == factor_pair
    return {"name": name, "N": n, "m": mod, "j": residue,
            "basis": basis, "v": vs, "factor_pair": factor_pair,
            "indices": [i1, i2], "recovered": recovered,
            "image_determinant": mod**3}


fixed_examples = [
    fixed_lattice_case("m=1 with signed unimodular basis and arbitrary v",
                       65, 1, 0, ((-1, 2), (-1, 1)), (-7, 3), (5, 13)),
    fixed_lattice_case("negative unit representative, shifted v, signed factors",
                       77, 5, -2, ((1, 2), (0, 5)), (-21, 55), (-7, -11)),
]

# Single preselected exact illustration; s is proved symbolically above/in
# the report, not obtained by running an optimizer or enumerating divisors.
n, h, k = 65, 6, 11
a, b, support = n, h*h, 786
disc = support*support - 4*a*b*n
root_cap = isqrt(disc-1)
lo = -(-(support-root_cap)//(2*a))
hi = (support+root_cap)//(2*a)
values = {str(x): a*x*x-support*x+b*n for x in [5, 6, 7]}
assert values == {"5": 35, "6": -36, "7": 23}
assert [lo, hi] == [6, 6]
assert gcd(h, n) == gcd(k, n) == 1
assert h*k == n+1 and n % 3 == 2 and (h-1)*(2*h+1) == n
assert isqrt(disc)**2 != disc

here = Path(__file__).resolve()
prefix = here.with_name("W012-quotient-support-review")
frozen_proposal = Path(str(prefix)+"-input-research--hypotheses--W012.md")
proposal_hash = sha256(frozen_proposal.read_bytes()).hexdigest()
assert proposal_hash == "730b559341a8d4abb41b5fe5b3e1deab2ab47d4b72af3188f4f13d173249faac"
output = {
    "status": "PASS",
    "scope": "Fixed universal polynomial identities and three fixed arithmetic illustrations; no numerical candidate run or sweep.",
    "certificate_sha256": sha256(here.read_bytes()).hexdigest(),
    "frozen_proposal_sha256": proposal_hash,
    "polynomial_identity_count": len(checks),
    "polynomial_identities": checks,
    "fixed_lattice_examples": fixed_examples,
    "fixed_obstruction_illustration": {
        "N": n, "h": h, "optimizer_proved_in_report": [h, k],
        "s": support, "D": disc, "strict_integer_exclusion": [lo, hi],
        "R_values": values, "boundary_integer_candidates": [],
    },
    "limitations": "Not a Lean proof, optimizer implementation, query-count theorem or performance evidence.",
}
Path(str(prefix)+"-certificate-output.json").write_text(json.dumps(output, indent=2)+"\n")
print(json.dumps({"status": "PASS", "polynomial_identities": len(checks),
                  "fixed_lattice_examples": 2, "fixed_obstruction_illustrations": 1}))
