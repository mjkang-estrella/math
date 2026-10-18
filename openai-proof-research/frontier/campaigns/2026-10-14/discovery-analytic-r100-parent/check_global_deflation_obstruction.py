"""Exact Q(lambda), lambda^2=49/50 diagnostic. This is a route obstruction only."""
from fractions import Fraction as F
import json


class Q:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, other):
        other = q(other)
        return Q(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, other):
        return self + -q(other)

    def __mul__(self, other):
        other = q(other)
        return Q(self.a * other.a + F(49, 50) * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __eq__(self, other):
        other = q(other)
        return (self.a, self.b) == (other.a, other.b)

    def pair(self):
        return [str(self.a), str(self.b)]


def q(x):
    return x if isinstance(x, Q) else Q(x)


def mm(a, b):
    return [[sum((q(a[i][l]) * b[l][j] for l in range(len(b))), Q())
             for j in range(len(b[0]))] for i in range(len(a))]


def sub(a, b):
    return [[q(x) - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def gram(slices):
    n = len(slices[0])
    out = [[Q() for _ in range(n)] for _ in range(n)]
    for s in slices:
        sq = mm(s, s)
        out = [[x + y for x, y in zip(ar, br)] for ar, br in zip(out, sq)]
    return out


def norm2(a):
    return sum((q(x) * x for row in a for x in row), Q())


def comm_error(slices):
    return sum((norm2(sub(mm(x, y), mm(y, x)))
                for i, x in enumerate(slices) for y in slices[i + 1:]), Q())


def beta2(slices):
    n = len(slices[0])
    return norm2(sub(gram(slices), [[int(i == j) for j in range(n)] for i in range(n)]))


t, a, lam = F(1, 10), F(7, 10), Q(0, 1)
T = [[[lam, 0, 0], [0, t, 0], [0, 0, t]],
     [[0, t, 0], [t, a, 0], [0, 0, -a]],
     [[0, 0, t], [0, 0, -a], [t, -a, 0]]]
S = [[[a, 0], [0, -a]], [[0, -a], [-a, 0]]]
assert gram(T) == [[Q(int(i == j)) for j in range(3)] for i in range(3)]
db = beta2(T) - beta2(S)
dc = comm_error(T) - comm_error(S)
assert db == Q(-F(1, 1250))
assert dc == Q(F(3, 5000), -F(1, 125))
assert db + 2 * dc == Q(F(1, 2500), -F(2, 125))
assert F(49, 50) > F(58, 100)
assert F(49, 50) > F(3, 40) ** 2  # lambda > 3/40 makes dc negative.
print(json.dumps({
    'status': 'EXACT_ROUTE_OBSTRUCTION_ONLY',
    'scalar_field': 'Q(lambda), lambda>0, lambda^2=49/50; pairs are a+b*lambda',
    'tensor_polynomial': 'lambda*x^3+3t*x*(y^2+z^2)+a*(y^3-3*y*z^2)',
    't': str(t), 'a': str(a), 'B_T': 'I3 exactly',
    'C_T': comm_error(T).pair(), 'C_S': comm_error(S).pair(),
    'beta2_T': beta2(T).pair(), 'beta2_S': beta2(S).pair(),
    'differences_T_minus_S': {'beta2': db.pair(), 'C': dc.pair(),
                            'beta2_plus_2C': (db + 2 * dc).pair()},
    'global_maximum_proof': [
        'For x<0 reflect x: lambda*x^3+3t*x*r^2 increases, harmonic term unchanged.',
        'For x>=0 and r=sqrt(1-x^2), y^3-3yz^2<=r^3.',
        '3t*x+a*r<=sqrt(9t^2+a^2)=sqrt(58)/10<lambda.',
        'T<=lambda*x^3+lambda*(1-x^2)<=lambda; equality at e_x.'
    ],
    'consequence': 'Deflation at a true global maximizer increases BOTH beta2 and C. Any positive-weight linear potential beta2+w*C increases. Every coordinatewise nondecreasing potential weakly increases; a constant potential need not strictly increase.',
    'limits': 'Not a counterexample to the full rounding target. Total C is about1.9, outside the small-total regime. No acceptance or count change.'
}, indent=2))
